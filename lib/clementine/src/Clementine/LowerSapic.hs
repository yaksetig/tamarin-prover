-- |
-- Module      : Clementine.LowerSapic
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- == Real lowering: Clementine AST -> Theory.OpenTheory -> rendered .spthy
--
-- This module is the "real" lowering pass. Unlike 'Clementine.Lower'
-- (which produces a self-describing 'CompiledTheory' summary used by
-- the v0.0 default build), this module produces a fully-fledged
-- 'Theory.OpenTheory' value and renders it through the existing
-- @prettyOpenTheory@ pretty-printer.
--
-- The lowering is built incrementally — see the @Status@ note below.
-- Right now we produce a /walking skeleton/: an 'OpenTheory' that
-- contains one lemma per @verify@ query (each one trivially @True@)
-- and no process. This is enough to:
--
--   1. Prove that the whole pipeline (parse → lower → translate →
--      pretty-print → 'String' → @tamarin-prover --prove@) works
--      end-to-end without falling over.
--   2. Produce a real @.spthy@ file on disk for inspection.
--   3. Verify that 'Sapic.translate' accepts our output cleanly.
--
-- Subsequent commits will replace the trivial lemmas with the real
-- §2.3 templates, and add a 'Theory.Sapic.PlainProcess' built from
-- the principal/step structure of the input. Each of those changes
-- is local to this file.
--
-- == Build status
--
-- This module is gated by the @with-sapic@ cabal flag. After the
-- toolchain unblock, that flag works on modern GHCs (verified on
-- GHC 9.14 with the workspace 'cabal.project' at the repo root).
module Clementine.LowerSapic
  ( lowerProtocolSapic
  , lowerProtocolSapicText
  , LowerError(..)
  ) where

-- We need 'Control.Category.(.)' (lens composition) instead of the
-- Prelude's function composition operator. fclabels lenses are
-- categories.
import           Prelude               hiding (id, (.))
import           Control.Category      (id, (.))

import           Control.Monad         (foldM)
import           Control.Monad.Catch   (MonadThrow, MonadCatch)
import qualified Data.Map.Strict       as M
import           Data.Maybe            (mapMaybe)
import qualified Data.Set              as Set
import qualified Data.Text             as T

-- tamarin-prover-utils
import           Extension.Data.Label  (get, set)

-- tamarin-prover-term
--
-- Note: 'fAppNoEq', 'fAppPair', 'fAppExp' all live in 'Term.Term'
-- which is an @other-modules@ of @tamarin-prover-term@. We reach
-- them via 'Term.LTerm' → 'Term.VTerm' → 'Term.Term' (the latter
-- is re-exported through @module Term.Term@ in @VTerm.hs@ and
-- @LTerm.hs@).
import           Term.LTerm            ( LVar(..), LSort(..)
                                       , pubTerm
                                       , fAppNoEq, fAppPair, fAppExp )
import           Term.VTerm            (varTerm)
import           Term.Builtin.Signature
                                       ( aencSym, signSym, hashSym
                                       , verifySym, pkSym, sencSym )
import           Term.Maude.Signature  ( MaudeSig
                                       , dhMaudeSig, asymEncMaudeSig
                                       , symEncMaudeSig
                                       , signatureMaudeSig
                                       , hashMaudeSig )

-- tamarin-prover-theory
import           Theory.Model.Fact     (protoFact, Multiplicity(..))

-- tamarin-prover-theory
import qualified Theory                as Th
import           Theory                ( OpenTheory, defaultOpenTheory
                                       , prettyOpenTranslatedTheory
                                       , removeTranslationItems
                                       , thyName
                                       , thySignature
                                       , sigpMaudeSig )
import           Theory.Text.Parser    (parseLemmaWithMacros)

import           Clementine.Sources    (makeAutoSourcesLemma)
import           Theory.Sapic          ( PlainProcess
                                       , Process(..)
                                       , SapicAction(..)
                                       , ProcessCombinator(..)
                                       , SapicLVar(..)
                                       , SapicNTerm
                                       , SapicNFact
                                       )
import           Text.PrettyPrint.Class (Doc, render)

-- tamarin-prover-sapic
import qualified Sapic

import           Clementine.AST

--------------------------------------------------------------------------------
-- Errors specific to the Sapic lowering
--------------------------------------------------------------------------------

-- | Errors that can arise during the Sapic lowering. These map onto
-- the @E0500-E0599@ band in 'Clementine.Errors'.
data LowerError
  = LowerEmptyProtocol
  | LowerSapicTranslationFailed !String
  deriving (Show)

--------------------------------------------------------------------------------
-- Top-level entry points
--------------------------------------------------------------------------------

-- | Lower a Clementine 'Protocol' to a fully-translated 'OpenTheory'.
-- Runs in @MonadThrow + MonadCatch@ because 'Sapic.translate' uses
-- exception machinery internally.
lowerProtocolSapic
  :: (MonadThrow m, MonadCatch m)
  => Protocol
  -> m OpenTheory
lowerProtocolSapic p = do
  -- Start from an empty theory, set its name to the Clementine
  -- protocol name, then mappend in the Maude signatures for every
  -- builtin the source mentions. This is what enables `^`, `aenc`,
  -- `sign`, `verify`, `pk`, `h`, `senc`, etc. in the rule body
  -- terms.
  let th0  = set thyName (T.unpack (protoName p))
           $ installBuiltins (protoBuiltins p)
           $ defaultOpenTheory False
      proc = lowerProtocolToProcess p
      th1  = Th.addProcess proc th0

  -- Verify-block lemmas, in declaration order.
  th2 <- foldM addLemmaOrFail th1
                   (concatMap (lowerQuery th1 p) (protoVerify p))

  -- Sources lemma (design step §5). 'makeAutoSourcesLemma' returns
  -- 'Nothing' when no open chains are detected, in which case the
  -- theory is unchanged.
  th3 <- case makeAutoSourcesLemma p of
           Nothing  -> pure th2
           Just src -> case parseLemmaWithMacros th2 src of
             Left e  -> error
                          ("Clementine.LowerSapic: internal: \
                           \auto_sources lemma failed to parse: "
                           ++ show e)
             Right l -> addLemmaOrFail th2 l

  Sapic.translate th3

-- | Mappend the Maude signatures for each Clementine builtin into
-- the theory's signature lens, replicating what the @builtins:@
-- declaration in a hand-written .spthy does. This is what makes
-- @^@, @aenc@, @sign@, @verify@, @pk@, @h@, @senc@ available as
-- function symbols in subsequent terms.
installBuiltins :: [Builtin] -> OpenTheory -> OpenTheory
installBuiltins bs th =
  let -- fclabels lens composition: set (sigpMaudeSig . thySignature)
      -- accesses the MaudeSig nested inside the SignaturePure inside
      -- the Theory. This is the same pattern as in
      -- Theory.Text.Parser.hs:251.
      lens       = sigpMaudeSig . thySignature
      currentSig = get lens th
      newSig     = foldr mappend currentSig (map builtinMaudeSig bs)
  in  set lens newSig th

builtinMaudeSig :: Builtin -> MaudeSig
builtinMaudeSig b = case b of
  BIDH      -> dhMaudeSig
  BISigning -> signatureMaudeSig
  BIHashing -> hashMaudeSig
  BISymEnc  -> symEncMaudeSig
  BIAsymEnc -> asymEncMaudeSig

-- | Convenience: lower, run Sapic translation, drop the source
-- 'Theory.Sapic.PlainProcess' (so the resulting spthy contains the
-- translated MSR rules but NOT the original process declaration —
-- otherwise tamarin-prover would try to compile the process a
-- second time and complain about duplicate rules), then pretty
-- print and post-process for compatibility with older tamarin-prover
-- binaries.
lowerProtocolSapicText
  :: (MonadThrow m, MonadCatch m)
  => Protocol
  -> m String
lowerProtocolSapicText p = do
  th <- lowerProtocolSapic p
  let translated = removeTranslationItems th
      raw        = render (prettyOpenTranslatedTheory translated :: Doc)
  pure (compatibilityCleanup raw)

-- | Strip rule annotations that the workspace pretty-printer
-- (Tamarin 1.13.0) emits but that older Tamarin binaries (e.g. the
-- 1.10.0 from Homebrew) reject. The annotations are purely cosmetic
-- (color, role, process structure debug info) — removing them does
-- not change proof semantics.
--
-- Specifically, we replace
--
-- @
--   rule (modulo E) Foo[color=#ffffff, process="...", issapicrule,
--                       role='Process']:
-- @
--
-- with
--
-- @
--   rule (modulo E) Foo:
-- @
--
-- The bracket content can span multiple lines, so we cannot use a
-- simple per-line @sed@. The state machine below tracks whether we
-- are currently inside a rule-header bracket and elides everything
-- between an opening @[@ and a closing @]:@ that follows a @rule@
-- keyword.
compatibilityCleanup :: String -> String
compatibilityCleanup = unlines . go . lines
  where
    go :: [String] -> [String]
    go []       = []
    go (l:rest) =
      case findRuleBracketStart l of
        Nothing -> l : go rest
        Just preAndOpen
          -- Single-line case: closing `]:` is on the same line.
          | hasClose l ->
              let cleaned = preAndOpen ++ ":"
              in cleaned : go rest
          -- Multi-line case: consume continuation lines until we hit `]:`.
          | otherwise ->
              let (_skipped, after) = break hasClose rest
                  cleaned           = preAndOpen ++ ":"
              in case after of
                   []      -> cleaned : go rest    -- malformed; bail safely
                   (_:tl)  -> cleaned : go tl

    -- A rule bracket starts at a line that contains "rule " followed
    -- by an identifier and an immediate '['. We return the prefix
    -- "  rule (modulo E) Foo" (without the trailing '[') if so.
    findRuleBracketStart :: String -> Maybe String
    findRuleBracketStart line
      | not ("rule" `isInfixOf'` line) = Nothing
      | otherwise = case break (== '[') line of
          (pre, '[':_) | "rule" `isInfixOf'` pre -> Just pre
          _                                      -> Nothing

    hasClose :: String -> Bool
    hasClose l = "]:" `isInfixOf'` l

    -- Local isInfixOf for [Char] to avoid pulling in Data.List qualified.
    isInfixOf' :: String -> String -> Bool
    isInfixOf' needle haystack
      | length needle > length haystack = False
      | take (length needle) haystack == needle = True
      | otherwise = case haystack of
          []     -> False
          (_:xs) -> isInfixOf' needle xs

--------------------------------------------------------------------------------
-- Process construction
--
-- Each Clementine 'Principal' becomes one Sapic process under top-
-- level replication: `! new ~ltk1; new ~ltk2; ... ; 0`. The principals
-- are then composed in parallel.
--
-- This is the next-smallest step up from "no process at all": it
-- exercises 'Sapic.translate's heavy code path (so we know the
-- machinery is wired up) without needing to encode the full step
-- semantics yet. Subsequent commits add step bodies to the tail of
-- each principal's process.
--------------------------------------------------------------------------------

lowerProtocolToProcess :: Protocol -> PlainProcess
lowerProtocolToProcess = lowerProtocolToProcess'

lowerProtocolToProcess' :: Protocol -> PlainProcess
lowerProtocolToProcess' p =
    -- Generate every long-term key at the PROTOCOL level (above
    -- the per-principal replication) so that all principals share
    -- the same fresh names. This is what makes peer public-key
    -- references unify across sides:
    --
    --     A's `aenc(_, pkR)` ≡ `aenc(_, pk(~skR))`
    --     R's `adec(_, ~skR)` ≡ unifies with the same `~skR`
    --
    -- The earlier per-principal layout broke this because each
    -- principal generated its own ~skR independently.
    foldr withFreshLtk
      (parallelOf
        [ lowerPrincipal principalNames placements pkMap (protoSteps p) prin
        | prin <- protoPrincipals p
        ])
      allLongTermKeys
  where
    principalNames    = map prinName (protoPrincipals p)
    placements        = computeAgreementPlacements p
    allLongTermKeys   = nubText
                          [ n
                          | prin <- protoPrincipals p
                          , KGenerates n _ <- prinKnows prin
                          ]
    pkMap             = computePubKeyMap (protoPrincipals p)

    withFreshLtk n acc =
      ProcessAction (New (mkSapicVar n)) mempty acc

    parallelOf :: [PlainProcess] -> PlainProcess
    parallelOf []  = ProcessNull mempty
    parallelOf [x] = x
    parallelOf xs  =
      let (l, r) = splitAt (length xs `div` 2) xs
      in  ProcessComb Parallel mempty (parallelOf l) (parallelOf r)

    nubText :: [T.Text] -> [T.Text]
    nubText = go Set.empty
      where
        go _    []     = []
        go seen (x:xs)
          | x `Set.member` seen = go seen xs
          | otherwise           = x : go (Set.insert x seen) xs

-- | Walk every principal block and collect the global public-key
-- map. For each declaration of the form
--
-- @
--   knows public pkR = PK(skR)
-- @
--
-- record the binding @pkR -> skR@. Subsequent references to @pkR@
-- from /any/ principal will resolve to @pk(~skR)@ instead of an
-- opaque public constant.
--
-- The same key may be declared in multiple principals (e.g. both
-- @principal A@ and @principal B@ might say @pkA = PK(skA)@); we
-- collapse duplicates by keeping the first occurrence.
computePubKeyMap :: [Principal] -> M.Map T.Text T.Text
computePubKeyMap = M.fromListWith (\_ x -> x) . concatMap forPrincipal
  where
    forPrincipal pr =
      [ (pubName, skName)
      | KKnowsPublic pubName (Just (EApp OpPK [EVar skName _] _)) _
          <- prinKnows pr
      ]

-- | Compute, for every verify-block agreement query, where the
-- corresponding 'Running'/'Commit' events should be emitted in the
-- lowered process.
--
-- Placement rule (Clementine design step 3 §3.2):
--
--   * 'Commit' on the initiator @i@'s side at the LATEST step in
--     which all of the agreed terms are in @i@'s scope. Since
--     state-fact carrying is monotonic, this is always @i@'s last
--     step (after the latest binding step among the agreed terms).
--
--   * 'Running' on the responder @r@'s side at the EARLIEST step
--     in which all of the agreed terms are in @r@'s scope. This
--     is the maximum binding-step of the agreed terms on @r@'s
--     side.
--
-- The result is a map from (principal name, step label) to the
-- list of events that should be appended to that step's process.
computeAgreementPlacements
  :: Protocol -> M.Map (T.Text, T.Text) [AgreementEvent]
computeAgreementPlacements p =
  M.fromListWith (++) (concatMap forQuery (protoVerify p))
  where
    -- Per-principal binding-step maps, computed once.
    bindingSteps :: M.Map T.Text (M.Map T.Text Int)
    bindingSteps = M.fromList
      [ (prinName pr, computeBindingSteps pr (protoSteps p))
      | pr <- protoPrincipals p
      ]

    forQuery :: Query -> [((T.Text, T.Text), [AgreementEvent])]
    forQuery q = case q of
      QInjAgreement     i r ts _ -> placeAgreement i r ts
      QNonInjAgreement  i r ts _ -> placeAgreement i r ts
      -- Aliveness's lemma template references @Commit(a, b, <'I',
      -- 'R', t>)@ but doesn't constrain @t@ — it just needs SOME
      -- Commit to fire its hypothesis. So we don't emit a separate
      -- placeholder Commit for QAuthentication; instead it
      -- piggybacks on whichever inj_agree / agreement event already
      -- exists with the same role pair. If neither query exists
      -- the aliveness lemma is vacuously true (no Commit anywhere)
      -- and Tamarin verifies it in zero steps.
      QAuthentication   _ _ _    -> []
      _                          -> []

    placeAgreement
      :: T.Text -> T.Text -> [TermRef]
      -> [((T.Text, T.Text), [AgreementEvent])]
    placeAgreement i r ts =
      let iBindings = M.findWithDefault M.empty i bindingSteps
          rBindings = M.findWithDefault M.empty r bindingSteps
          tNames    = map trVar ts

          -- The maximum binding-step index of the agreed terms on
          -- a given side. Terms that aren't bound on this side
          -- fall back to index @0@ (the start of the protocol);
          -- when the lemma references a term that exists only on
          -- the other side (e.g. ISO-DH's @kA@ which is bound on
          -- A's side as @kA@ but on B's side as @kB@), the event
          -- still gets placed and the agreement falls back to
          -- aliveness-style matching.
          maxBinding :: M.Map T.Text Int -> Int
          maxBinding bnds = case tNames of
            [] -> 0
            _  -> maximum [M.findWithDefault 0 t bnds | t <- tNames]

          iIdx = maxBinding iBindings
          rIdx = maxBinding rBindings

          -- Step in protoSteps where principal `n` participates,
          -- whose index is at least `idx`. We take the LAST such
          -- step for the committer (latest in scope) and the
          -- FIRST such step for the running party (earliest).
          stepAt n idx pickFn =
            case filter (\(_, s) -> involves n s)
                        (zip [0 :: Int ..] (protoSteps p)) of
              [] -> Nothing
              xs ->
                case filter (\(j, _) -> j >= idx) xs of
                  [] -> case xs of
                    [] -> Nothing
                    _  -> Just (snd (pickFn xs))   -- fallback
                  ys -> Just (snd (pickFn ys))

          mCommit  = stepAt i iIdx last
          mRunning = stepAt r rIdx head
      in  catMaybesPair
            [ fmap (\s -> ((i, stepLabel s), [AgreeCommit  i r ts])) mCommit
            , fmap (\s -> ((r, stepLabel s), [AgreeRunning i r ts])) mRunning
            ]

    catMaybesPair :: [Maybe a] -> [a]
    catMaybesPair = mapMaybe id

-- | Per-principal binding-step map: for every variable that
-- becomes in scope on this principal's side, the index (in
-- 'protoSteps' order) of the step that first binds it.
--
-- Initial scope (the principal's own block, including
-- @generates@ and @knows@) is recorded with index @-1@, so it
-- always satisfies any @>= 0@ check downstream.
computeBindingSteps :: Principal -> [Step] -> M.Map T.Text Int
computeBindingSteps pr allSteps =
    foldl' addStepBindings initial
      (zip [0 ..] (filter (involves (prinName pr)) allSteps))
  where
    -- Initial scope from the principal block.
    initial :: M.Map T.Text Int
    initial = M.fromList
      [ (n, -1)
      | k <- prinKnows pr
      , n <- case k of
          KGenerates    n' _   -> [n']
          KKnowsPublic  n' _ _ -> [n']
          KKnowsPrivate n' _   -> [n']
      ]

    addStepBindings :: M.Map T.Text Int -> (Int, Step) -> M.Map T.Text Int
    addStepBindings m (idx, s) =
      let role = roleOf (prinName pr) s
          newVars = case role of
            RSender     -> Set.toList (foldMap senderBindings (stepBody s))
            RLocalActor -> Set.toList (foldMap senderBindings (stepBody s))
            RReceiver   -> Set.toList (foldMap receiverBindings (stepBody s))
      in  foldr (\v -> M.insertWith (\_ old -> old) v idx) m newVars

    senderBindings :: StepStmt -> Set.Set T.Text
    senderBindings stmt = case stmt of
      SNew n _              -> Set.singleton n
      SLet n _ _            -> Set.singleton n
      _                     -> Set.empty

    -- The receiver only binds the variables that appear in the
    -- SSend's expression (it doesn't run the new/let/require).
    receiverBindings :: StepStmt -> Set.Set T.Text
    receiverBindings (SSend e _) = collectVarsExpr e
    receiverBindings _           = Set.empty

    roleOf :: T.Text -> Step -> StepRole
    roleOf n s
      | stepFrom s == n = case stepKind s of
          StepLocal       -> RLocalActor
          StepNetwork _ _ -> RSender
      | otherwise = case stepKind s of
          StepNetwork tgt _ | tgt == n -> RReceiver
          _                            -> RLocalActor   -- defensive

-- | Whether a principal participates in a step (sender, receiver,
-- or local actor).
involves :: T.Text -> Step -> Bool
involves n s = stepFrom s == n || case stepKind s of
  StepNetwork tgt _ -> tgt == n
  _                 -> False

-- (foldl' is already in Prelude in GHC 9.14; no local definition needed.)

-- | Lower one principal: emit per-session @KeyGen@ events for the
-- long-term keys (which are 'new'-bound at the protocol level
-- above this 'Rep'), then the step sequence, all wrapped in
-- replication and an NDC reveal branch.
--
-- The long-term key freshes are NOT generated here; they live at
-- the protocol level so all principals share the same names.
lowerPrincipal
  :: [T.Text]
  -> M.Map (T.Text, T.Text) [AgreementEvent]
  -> M.Map T.Text T.Text
  -> [Step]
  -> Principal
  -> PlainProcess
lowerPrincipal principalNames placements pkMap allSteps pr =
    ProcessAction Rep mempty
      $ keyGenEvents
      $ ProcessComb NDC mempty
          (stepSequence bindingMap ctx0
                         (relevantSteps (prinName pr) allSteps)
                         (ProcessNull mempty))           -- left: protocol
          (revealBranch (prinName pr) (map mkSapicVar genKeys))  -- right: reveal
  where
    genKeys    = [n | KGenerates n _ <- prinKnows pr]
    bindingMap = computeBindingSteps pr allSteps

    -- For each long-term key generated by this principal, emit a
    -- `KeyGen($P, ~k)` event so aliveness lemmas can witness it.
    keyGenEvents k =
      foldr
        (\n acc ->
            ProcessAction
              (Event (keyGenFact (prinName pr) n))
              mempty
              acc)
        k
        genKeys

    ctx0 = LowerCtx
      { lcReceived         = Set.empty
      , lcPrincipalNames   = Set.fromList principalNames
      , lcPublicParams     = Set.fromList
          [n | KKnowsPublic n _ _ <- prinKnows pr]
      , lcCurrentPrincipal = prinName pr
      , lcAgreementMap     = placements
      , lcPubKeyMap        = pkMap
      }

-- | @KeyGen(<principal>, <ltk>)@ event fact.
keyGenFact :: T.Text -> T.Text -> SapicNFact SapicLVar
keyGenFact prin ltk =
  protoFact Linear "KeyGen"
    [ pubTerm (T.unpack prin)
    , varTerm (mkSapicVar ltk)
    ]

-- | The reveal branch of a principal's NDC. Emits a 'Reveal'
-- event tagged with the principal's name, then sends every
-- long-term key on the public channel.
revealBranch :: T.Text -> [SapicLVar] -> PlainProcess
revealBranch prin ltks =
    ProcessAction (Event (revealFact prin)) mempty
      (foldr outLtk (ProcessNull mempty) ltks)
  where
    outLtk v acc =
      ProcessAction (ChOut Nothing (varTerm v)) mempty acc

-- | @Reveal(<principal>)@ event fact. Lemma templates from
-- design step 2 §2.3.1 / §2.3.2 quantify over this for the
-- compromise-excuse clause.
revealFact :: T.Text -> SapicNFact SapicLVar
revealFact prin = protoFact Linear "Reveal" [pubTerm (T.unpack prin)]

-- | Per-principal walking context. Carries:
--
--   * @lcReceived@   — variable names that this principal has
--                      received from a peer in an earlier step.
--                      Subsequent references to these names use the
--                      @pat_@-prefixed Sapic variable instead of the
--                      sender's local name (since on this
--                      principal's side, the wire-bound variable is
--                      'patFoo' and not 'foo').
--   * @lcPrincipalNames@ — the set of principal identifiers in the
--                      protocol. Identifiers that match a principal
--                      lower to public constants ('A', 'B', ...)
--                      instead of fresh variables.
--   * @lcPublicParams@ — the set of @knows public@ identifiers in
--                      this principal's block (e.g. peer keys
--                      @pkA@, @pkB@). They lower to public constants
--                      so the rules don't reference them as unbound
--                      fresh variables.
data LowerCtx = LowerCtx
  { lcReceived       :: !(Set.Set T.Text)
  , lcPrincipalNames :: !(Set.Set T.Text)
  , lcPublicParams   :: !(Set.Set T.Text)
  , -- | Which principal we are currently lowering. Used to look
    -- up Running/Commit event placements in 'lcAgreementMap'.
    lcCurrentPrincipal :: !T.Text
  , -- | Per-(principal, step label) list of agreement events
    -- ('Running'/'Commit') to inject into that step's process
    -- continuation. Computed once per protocol from the verify
    -- block, then consulted during step lowering.
    lcAgreementMap :: !(M.Map (T.Text, T.Text) [AgreementEvent])
  , -- | Global public-key map: maps a @knows public@ identifier to
    -- the underlying long-term key name (when the user wrote
    -- @knows public pkR = PK(skR)@). Subsequent references to the
    -- public key resolve to @pk(~skR)@ instead of an opaque
    -- public constant, so encryption to a peer's public key
    -- actually unifies with the peer's @adec(_, ~skR)@ equation.
    --
    -- Populated at protocol level from /every/ principal block
    -- that declares such an equation, then shared across all
    -- principals' lowering contexts.
    lcPubKeyMap :: !(M.Map T.Text T.Text)
  }

-- | A Running or Commit event placed by 'computeAgreementPlacements'
-- on a particular (principal, step) pair.
--
-- Each constructor carries the lemma's role names @(i, r)@ and
-- the list of agreed terms from the @verify@ block. The agreed
-- terms become a payload tuple inside the action fact, so the
-- lemma template's @\<\'I\', \'R\', t\>@ pattern unifies with the
-- specific terms each session agreed on (rather than a constant
-- placeholder, which would make different sessions
-- indistinguishable and break injectivity).
--
--   * 'AgreeCommit' is emitted by @i@ at @i@'s latest step in
--     which all the agreed terms are in scope.
--   * 'AgreeRunning' is emitted by @r@ at @r@'s earliest step in
--     which all the agreed terms are in scope.
data AgreementEvent
  = AgreeRunning !T.Text !T.Text ![TermRef]  -- ^ (i, r, terms) — emitted by r
  | AgreeCommit  !T.Text !T.Text ![TermRef]  -- ^ (i, r, terms) — emitted by i
  deriving (Show, Eq)

-- | The role this principal plays in a given step.
data StepRole = RSender | RReceiver | RLocalActor

-- | Steps that this principal participates in, in declaration order,
-- tagged with the role the principal plays and the step's index in
-- 'protoSteps' (so the binding-map lookups stay aligned).
relevantSteps :: T.Text -> [Step] -> [(Step, StepRole, Int)]
relevantSteps p = mapMaybe pick . zip [0 ..]
  where
    pick (i, s)
      | stepFrom s == p = case stepKind s of
          StepLocal       -> Just (s, RLocalActor, i)
          StepNetwork _ _ -> Just (s, RSender, i)
      | otherwise = case stepKind s of
          StepNetwork tgt _ | tgt == p -> Just (s, RReceiver, i)
          _                            -> Nothing

stepSequence
  :: M.Map T.Text Int
  -> LowerCtx
  -> [(Step, StepRole, Int)]
  -> PlainProcess
  -> PlainProcess
stepSequence _        _   []             k = k
stepSequence bindings ctx ((s,r,idx):rest) k =
  -- After a receive, /new/ variables in the sent expression
  -- become "received" on this principal's side. A variable is
  -- new only if the principal didn't already bind it locally
  -- in a STRICTLY EARLIER step — otherwise the receive just
  -- confirms the value the principal already has, and references
  -- should keep resolving to the local fresh (not get
  -- pat-prefixed).
  let ctx' = case r of
        RReceiver ->
          let allMentioned = collectVarsBody (stepBody s)
              alreadyLocal = Set.fromList
                [ v | v <- Set.toList allMentioned
                    , Just bIdx <- [M.lookup v bindings]
                    , bIdx < idx
                ]
              newlyReceived = allMentioned `Set.difference` alreadyLocal
          in  ctx { lcReceived = lcReceived ctx <> newlyReceived }
        _ -> ctx
  in  lowerStep ctx s r (stepSequence bindings ctx' rest k)

-- | Lower one step from one principal's perspective.
--
--   * Sender: run every statement in the step body in declaration
--     order. The 'SSend' becomes an 'out(c, e)' action.
--   * Receiver: run /only/ a single 'in(c, e)' action for the
--     'SSend' statement in the body. The other statements are
--     sender-side computation (fresh nonces, let-bindings,
--     requires, claims) and do not happen on the receiver. This is
--     the standard message-passing semantics from design step 2.
--   * Local actor: same as sender but no 'out'.
--
-- After all of the above, any 'AgreementEvent's that the
-- placement map prescribes for this (principal, step) pair are
-- appended as Sapic 'Event' actions. Tamarin lemma templates from
-- §2.3 quantify over the resulting 'Running'/'Commit' action facts.
lowerStep :: LowerCtx -> Step -> StepRole -> PlainProcess -> PlainProcess
lowerStep ctx s role k =
    let kWithAgreements = appendAgreementEvents ctx (stepLabel s) k
    in case role of
         RSender     -> foldSenderStmts (stepBody s) kWithAgreements
         RLocalActor -> foldSenderStmts (stepBody s) kWithAgreements
         RReceiver   -> emitReceive (stepBody s) kWithAgreements
  where
    foldSenderStmts []     kont = kont
    foldSenderStmts (x:xs) kont = lowerStmt ctx role x (foldSenderStmts xs kont)

    -- The receiver only consumes the wire message. We find the
    -- (single) 'SSend' in the body and emit a 'ChIn' for it. If
    -- there is no SSend (a `local` step accidentally tagged as
    -- network) we emit nothing.
    emitReceive body kont = case [e | SSend e _ <- body] of
      []      -> kont
      (e : _) ->
        ProcessAction
          (ChIn Nothing (lowerExprPat ctx e) Set.empty)
          mempty
          kont

-- | Append the agreement events for the current (principal, step)
-- pair to the continuation, in the order they appear in the
-- placement map. Each event becomes a Sapic 'Event' action whose
-- payload tuple includes the agreed terms lowered against the
-- /current principal's/ scope (so receiver-side @ni@ resolves to
-- @~patNi@ on the receiver's side and to @~ni@ on the originator's
-- side, and Tamarin's matcher can unify them via the wire-tracking
-- chain).
appendAgreementEvents
  :: LowerCtx -> T.Text -> PlainProcess -> PlainProcess
appendAgreementEvents ctx label k =
  let key    = (lcCurrentPrincipal ctx, label)
      events = M.findWithDefault [] key (lcAgreementMap ctx)
  in  foldr wrap k events
  where
    -- Commit(a, b, <I, R, t>) on the committer's side: a=I, b=R.
    wrap (AgreeCommit i r ts) acc =
      ProcessAction (Event (agreementFact ctx "Commit" i r i r ts)) mempty acc
    -- Running(b, a, <I, R, t>) on the running party's side: b=R, a=I.
    wrap (AgreeRunning i r ts) acc =
      ProcessAction (Event (agreementFact ctx "Running" r i i r ts)) mempty acc

-- | Build a Running/Commit action fact whose third argument is a
-- 3-tuple @\<\'I\', \'R\', \<agreed_terms\>\>@. The lemma template's
-- @\<\'I\', \'R\', t\>@ pattern unifies with the agreed-terms
-- tuple via the universally-quantified @t@.
--
-- The agreed terms are lowered through 'lowerExpr' against the
-- current principal's context, so each side emits the same value
-- under different local names (the names unify via Tamarin's
-- backward-chaining wire tracking).
agreementFact
  :: LowerCtx
  -> String -> T.Text -> T.Text -> T.Text -> T.Text -> [TermRef]
  -> SapicNFact SapicLVar
agreementFact ctx tag arg1 arg2 i r ts =
  protoFact Linear tag
    [ pubTerm (T.unpack arg1)
    , pubTerm (T.unpack arg2)
    , fAppPair
        ( pubTerm (T.unpack i)
        , fAppPair
            ( pubTerm (T.unpack r)
            , agreedTermsTuple ts
            )
        )
    ]
  where
    -- Right-fold the agreed terms into a tuple. With zero terms
    -- (e.g. for `authentication(I, R)` which has no payload), we
    -- emit a stable placeholder constant so the lemma still has
    -- something to unify against.
    agreedTermsTuple :: [TermRef] -> SapicNTerm SapicLVar
    agreedTermsTuple []     = pubTerm "noAgreed"
    agreedTermsTuple [tr]   = lowerTermRef tr
    agreedTermsTuple (x:xs) = fAppPair (lowerTermRef x, agreedTermsTuple xs)

    lowerTermRef :: TermRef -> SapicNTerm SapicLVar
    lowerTermRef tr =
      -- The TermRef's variable name is looked up via the same
      -- resolveVar that handles step-body variable resolution, so
      -- it picks up the principal's local fresh names, received
      -- pat-vars, and pkMap entries automatically.
      resolveVar ctx (trVar tr)

-- | Collect the variable names that a /receiver/ binds when it
-- consumes the wire message of a step. Only the @SSend@'s
-- expression matters: the @new@/@let@/@require@/@claim@
-- statements are sender-side computation and do not introduce any
-- bindings on the receiver.
collectVarsBody :: [StepStmt] -> Set.Set T.Text
collectVarsBody = foldMap go
  where
    go (SSend e _) = collectVarsExpr e
    go _           = Set.empty

collectVarsExpr :: Expr -> Set.Set T.Text
collectVarsExpr e = case e of
  EVar n _       -> Set.singleton n
  EConst _ _     -> Set.empty
  ETup xs _      -> foldMap collectVarsExpr xs
  EApp _ xs _    -> foldMap collectVarsExpr xs
  EExp a b _     -> collectVarsExpr a <> collectVarsExpr b

-- | Lower a single statement of a step body.
--
-- v0.2 coverage: 'SNew', 'SLet', 'SSend', 'SClaim', and 'SRequire'
-- (the latter is now a real CondEq guard, gated on the equality
-- verify(...) = true). Variable references inside the body
-- correctly distinguish between locally-fresh names, peer-received
-- names, and principal identifiers via the 'LowerCtx'.
lowerStmt :: LowerCtx -> StepRole -> StepStmt -> PlainProcess -> PlainProcess
lowerStmt ctx role stmt k = case stmt of

  SNew n _ ->
    ProcessAction (New (mkSapicVar n)) mempty k

  SLet n e _ ->
    ProcessComb
      (Let { letLeft  = varTerm (mkSapicVar n)
           , letRight = lowerExpr ctx e
           , letMatch = Set.empty
           })
      mempty
      k                              -- "then" branch: n is in scope
      (ProcessNull mempty)           -- "else" branch: degenerate

  SRequire e _ ->
    -- Continue iff `e` evaluates to `true`. For the canonical
    -- `require VERIFY(pk, body, sig)` form this becomes a CondEq
    -- against the constant 'true', which Tamarin's equational
    -- theory rewrites by the `verify(sign(...)) = true` rule when
    -- the signature is honestly produced.
    ProcessComb
      (CondEq (lowerExpr ctx e) sapicTrue)
      mempty
      k
      (ProcessNull mempty)

  SSend e _ -> case role of
    RSender   -> ProcessAction (ChOut Nothing (lowerExpr ctx e))               mempty k
    -- Receiver side: prefix every variable name with `pat_` so that
    -- Sapic.applyM does not flag the receive as capturing a
    -- let-bound name from a parallel branch (see
    -- 'Theory.Sapic.Process.CapturedEx' for the diagnostic). Per
    -- Sapic's own error-message recommendation, the workaround is
    -- exactly this rename.
    RReceiver -> ProcessAction (ChIn Nothing (lowerExprPat ctx e) Set.empty)   mempty k
    RLocalActor -> k                  -- local steps don't `send`; ignore

  SClaim (ClaimSecret n) _ ->
    ProcessAction (Event (secretFact ctx n)) mempty k

-- | The constant @true@ that Tamarin's equational theory uses on
-- the right-hand side of @verify(sign(_,_), _, pk(_)) = true@.
sapicTrue :: SapicNTerm SapicLVar
sapicTrue = pubTerm "true"

-- | Build a @Secret(<n>)@ event fact. Tamarin lemma templates from
-- design step 2 §2.3.1 quantify over this fact name.
secretFact :: LowerCtx -> T.Text -> SapicNFact SapicLVar
secretFact ctx n =
  protoFact Linear "Secret" [resolveVar ctx n]

-- | Resolve a Clementine identifier to a Sapic term according to
-- the lowering context.
--
-- Resolution order (first match wins):
--
--   1. Principal name → public constant (e.g. @\'A\'@, @\'B\'@).
--   2. Public-key with a known underlying secret → @pk(~secret)@.
--      This is the case for @knows public pkR = PK(skR)@: the
--      reference to @pkR@ from any principal (including ones that
--      do NOT have @skR@ in their own block) lowers to
--      @pk(~skR)@, which is the SAME term that @principal R@ uses
--      after registering @~skR@ at the protocol level. This is
--      what enables @adec@ on the receiver side to unify with
--      @aenc@ on the sender side.
--   3. Public param with no equation → opaque public constant.
--   4. Received (peer-bound) variable → @pat@-prefixed Sapic var.
--   5. Otherwise → fresh-sorted Sapic variable.
resolveVar :: LowerCtx -> T.Text -> SapicNTerm SapicLVar
resolveVar ctx n
  | n `Set.member` lcPrincipalNames ctx     = pubTerm (T.unpack n)
  | Just sk <- M.lookup n (lcPubKeyMap ctx) = fAppNoEq pkSym
                                                [varTerm (mkSapicVar sk)]
  | n `Set.member` lcPublicParams   ctx     = pubTerm (T.unpack n)
  | n `Set.member` lcReceived ctx           = varTerm (mkPatVar n)
  | otherwise                               = varTerm (mkSapicVar n)
  where
    mkPatVar nm = SapicLVar (LVar ("pat" ++ capitalize (T.unpack nm)) LSortFresh 0) Nothing
    capitalize ""     = ""
    capitalize (c:cs) = toUpper c : cs

    toUpper c
      | c >= 'a' && c <= 'z' = toEnum (fromEnum c - 32)
      | otherwise            = c

-- | Build a fresh-sorted Sapic variable from a Clementine identifier.
mkSapicVar :: T.Text -> SapicLVar
mkSapicVar name =
  SapicLVar (LVar (T.unpack name) LSortFresh 0) Nothing

--------------------------------------------------------------------------------
-- AST Expr -> Sapic term
--
-- v0.2 coverage (this commit):
--   * EVar    -> varTerm of a fresh-sorted Sapic variable
--   * EConst  -> pubTerm of the literal name
--   * ETup    -> right-folded pair: <a, b, c> = pair(a, pair(b, c))
--   * EApp    -> real function-symbol applications, dispatched on
--                the PrimOp tag (AENC -> aencSym, SIGN -> signSym,
--                VERIFY -> verifySym, PK -> pkSym, H -> hashSym,
--                ENC -> sencSym, ...)
--   * EExp    -> diffie-hellman expSym
--
-- The PrimOps that are not yet wired (DEC/ADEC/MAC/AEAD) still
-- collapse to opaque variables; they are unused in the iso_dh and
-- nsl fixtures.
--------------------------------------------------------------------------------

lowerExpr :: LowerCtx -> Expr -> SapicNTerm SapicLVar
lowerExpr ctx e = case e of
  EVar n _       -> resolveVar ctx n
  EConst c _     -> pubTerm (T.unpack c)
  ETup [] _      -> pubTerm "unit"      -- defensive; parser rejects
  ETup [x] _     -> lowerExpr ctx x
  ETup xs _      -> foldr1Pair (map (lowerExpr ctx) xs)
  EApp op args _ -> lowerPrimApp op (map (lowerExpr ctx) args)
  -- Special case: a literal DH share `'<base>'^<exp>` whose
  -- exponent was received from a peer collapses to a single
  -- canonical Sapic variable. The full term `(g^x)^y` parses
  -- left-associatively, so the inner `g^x` matches this rule and
  -- the outer fAppExp picks up the local `y`.
  EExp (EConst b _) (EVar n _) _
    | n `Set.member` lcReceived ctx ->
        varTerm (mkDHPatVar b n)
  EExp b x _     -> fAppExp (lowerExpr ctx b, lowerExpr ctx x)
  where
    foldr1Pair :: [SapicNTerm SapicLVar] -> SapicNTerm SapicLVar
    foldr1Pair []     = pubTerm "unit"
    foldr1Pair [t]    = t
    foldr1Pair (t:ts) = fAppPair (t, foldr1Pair ts)

-- | Map a Clementine 'PrimOp' to its corresponding Tamarin function
-- symbol. Operators that we have not yet wired (DEC, ADEC, MAC) fall
-- through to an opaque variable so the rule still type-checks; they
-- are unused in the v0.2 fixture set.
lowerPrimApp :: PrimOp -> [SapicNTerm SapicLVar] -> SapicNTerm SapicLVar
lowerPrimApp op args = case op of
  OpAEnc   -> fAppNoEq aencSym   args
  OpEnc    -> fAppNoEq sencSym   args
  OpSign   -> fAppNoEq signSym   args
  OpVerify -> fAppNoEq verifySym args
  OpPK     -> fAppNoEq pkSym     args
  OpH      -> fAppNoEq hashSym   args
  -- Not yet wired:
  OpDec    -> opaque "opaqueDec"
  OpADec   -> opaque "opaqueAdec"
  OpMAC    -> opaque "opaqueMac"
  where
    opaque n = varTerm (mkSapicVar (T.pack n))

-- | Pattern-side variant of 'lowerExpr', for receive sites.
--
-- Same as 'lowerExpr' except every Clementine identifier becomes
-- a Sapic variable named @pat_<n>@. Sapic's bindings analysis uses
-- the @pat_@ prefix as the convention for "this is a pattern
-- introduced by an input, not a capture from outer scope". Without
-- this rename, parallel principals that happen to use the same
-- variable name (e.g. both A's @sigA@ binding and B's @sigA@
-- receive of the same wire bytes) cause Sapic to throw
-- 'Theory.Sapic.Process.CapturedEx CapturedIn'.
-- | Receive-side variant: every plain identifier becomes a Sapic
-- pattern variable with the @pat@ prefix. Principal names and
-- public params still lower to public constants. DH shares
-- @'<base>'^<var>@ collapse to a single canonical pat-variable so
-- they appear as a single term on the wire (avoiding the
-- multiplication-restriction warning that comes from trying to
-- pattern-match on @'g'^~patX@, since DH is not a destructor in
-- Tamarin's equational theory).
lowerExprPat :: LowerCtx -> Expr -> SapicNTerm SapicLVar
lowerExprPat ctx e = case e of
  EVar n _
    | n `Set.member` lcPrincipalNames ctx     -> pubTerm (T.unpack n)
    | Just sk <- M.lookup n (lcPubKeyMap ctx) -> fAppNoEq pkSym
                                                  [varTerm (mkSapicVar sk)]
    | n `Set.member` lcPublicParams   ctx     -> pubTerm (T.unpack n)
    | otherwise                               -> varTerm (mkPatVar n)
  EConst c _     -> pubTerm (T.unpack c)
  ETup [] _      -> pubTerm "unit"
  ETup [x] _     -> lowerExprPat ctx x
  ETup xs _      -> foldr1Pair (map (lowerExprPat ctx) xs)
  EApp op args _ -> lowerPrimApp op (map (lowerExprPat ctx) args)
  -- DH-share special case: `'g'^x` becomes a single pat variable.
  EExp (EConst b _) (EVar n _) _ -> varTerm (mkDHPatVar b n)
  EExp b x _     -> fAppExp (lowerExprPat ctx b, lowerExprPat ctx x)
  where
    foldr1Pair []     = pubTerm "unit"
    foldr1Pair [t]    = t
    foldr1Pair (t:ts) = fAppPair (t, foldr1Pair ts)

    mkPatVar n = SapicLVar (LVar ("pat" ++ capitalize (T.unpack n)) LSortFresh 0) Nothing
    capitalize ""      = ""
    capitalize (c:cs)  = toUpper c : cs

    toUpper c
      | c >= 'a' && c <= 'z' = toEnum (fromEnum c - 32)
      | otherwise            = c

-- | Canonical Sapic variable for a received DH share @'<base>'^<exp>@.
-- The same function is used at the wire receive site and at any
-- subsequent body reference, so the two stay in sync without an
-- explicit map.
mkDHPatVar :: T.Text -> T.Text -> SapicLVar
mkDHPatVar base expvar =
  SapicLVar
    (LVar ("patDh" ++ capitalize (T.unpack base) ++ capitalize (T.unpack expvar))
          LSortFresh 0)
    Nothing
  where
    capitalize ""     = ""
    capitalize (c:cs) = toUpper c : cs
    toUpper c
      | c >= 'a' && c <= 'z' = toEnum (fromEnum c - 32)
      | otherwise            = c

--------------------------------------------------------------------------------
-- Lemma generation
--------------------------------------------------------------------------------

-- | Lower one verify query to one or more lemmas.
--
-- All queries now instantiate real §2.3 templates by parsing
-- hand-built lemma source through 'parseLemmaWithMacros'. This is
-- the same trick we use for 'executable' (§2.3.7) — it sidesteps
-- the awkwardness of constructing 'ProtoFormula' values directly.
--
-- The lemma /bodies/ refer to the canonical action facts from
-- design step 3 §3.1: @Secret(_)@, @Running(_,_,_)@,
-- @Commit(_,_,_)@, @Reveal(_)@, @Honest(_)@. Whether the rules
-- generated by 'lowerProtocolToProcess' actually emit these facts
-- is a separate concern — for v0.2 only @Secret@ is reliably
-- emitted (by 'SClaim'), so the secrecy lemmas are the only
-- non-vacuous ones in practice. The other templates are still
-- correct and will become useful as soon as the §2.1/§2.2 rule
-- generation emits Running/Commit/Reveal.
lowerQuery :: OpenTheory -> Protocol -> Query -> [Th.Lemma Th.ProofSkeleton]
lowerQuery th _ q = case q of
  QExecutable _              -> [executable     th]
  QSecrecy t _               -> [secrecyLemma   th (trVar t)]
  QForwardSecrecy t _        -> [fsLemma        th (trVar t)]
  QInjAgreement i r ts _     -> [injAgreeLemma  th i r ts]
  QNonInjAgreement i r ts _  -> [agreeLemma     th i r ts]
  QAuthentication i r _      -> [aliveLemma     th i r]

-- | Common helper: parse a lemma source string through the
-- in-tree formula parser, panic with a clear message if our
-- hard-coded string is malformed.
buildLemma :: OpenTheory -> String -> String -> Th.Lemma Th.ProofSkeleton
buildLemma th label src =
  case parseLemmaWithMacros th src of
    Left e  -> error ("Clementine.LowerSapic." <> label
                       <> ": internal: failed to parse hard-coded \
                          \lemma. This is a bug in Clementine, not \
                          \in your .clem file. parseLemmaWithMacros \
                          \said: " <> show e)
    Right l -> l

-- | The executable lemma — §2.3.7. Asserts that at least one
-- honest run reaches Sapic's @Init@ action fact (which fires at
-- the head of every translated process). Uses an exists-trace
-- quantifier so the lemma is satisfied by a single witness.
executable :: OpenTheory -> Th.Lemma Th.ProofSkeleton
executable th = buildLemma th "executable" $
  "lemma executable:\n\
  \  exists-trace\n\
  \  \"Ex #i. Init() @ #i\""

-- | Secrecy lemma — §2.3.1.
--
-- Standard form: a Secret claim implies the adversary cannot
-- learn the secret unless an LtK was revealed. The current rule
-- generator does not yet emit a @Reveal@ rule, so the
-- compromise-excuse clause is unsatisfiable in practice — which
-- means we are proving plain secrecy, no compromise. That is the
-- right form for v0.2; once Reveal_LTK rules land we can
-- distinguish weak secrecy from forward secrecy.
secrecyLemma :: OpenTheory -> T.Text -> Th.Lemma Th.ProofSkeleton
secrecyLemma th term = buildLemma th ("secrecy_" <> T.unpack term) $
  "lemma secrecy_" <> T.unpack term <> ":\n\
  \  all-traces\n\
  \  \"All x #i. Secret(x) @ i ==>\n\
  \    not (Ex #j. K(x) @ j)\n\
  \    | (Ex A #r. Reveal(A) @ r)\"\n"

-- | Forward secrecy — §2.3.2. Same as secrecy but the reveal
-- exception clause is restricted to reveals that happened BEFORE
-- the secret was claimed. Stronger than plain secrecy: it says
-- the secret stays safe even if compromise happens later.
fsLemma :: OpenTheory -> T.Text -> Th.Lemma Th.ProofSkeleton
fsLemma th term = buildLemma th ("fs_" <> T.unpack term) $
  "lemma fs_" <> T.unpack term <> ":\n\
  \  all-traces\n\
  \  \"All x #i. Secret(x) @ i ==>\n\
  \    not (Ex #j. K(x) @ j)\n\
  \    | (Ex A #r. Reveal(A) @ r & #r < #i)\"\n"

-- | Injective agreement — §2.3.3 (Lowe's hierarchy).
--
-- The standard form: when @actor@ commits to running with @peer@
-- on parameters @ts@, some matching @peer@-session was running
-- with @actor@ on @ts@, no two commits share the same running,
-- modulo honest-LtK reveal.
--
-- Until the rule generator emits Running/Commit action facts the
-- antecedent is unsatisfiable and the lemma holds vacuously, but
-- the formula is the right one and will start exercising the
-- prover as soon as those facts are emitted.
injAgreeLemma :: OpenTheory -> T.Text -> T.Text -> [TermRef] -> Th.Lemma Th.ProofSkeleton
injAgreeLemma th i r _ts = buildLemma th nm $
  "lemma " <> nm <> ":\n\
  \  all-traces\n\
  \  \"All a b t #i.\n\
  \     Commit(a, b, <" <> roleI <> ", " <> roleR <> ", t>) @ i\n\
  \     ==> ( Ex #j. Running(b, a, <" <> roleI <> ", " <> roleR <> ", t>) @ j\n\
  \                & j < i\n\
  \                & not (Ex a2 b2 #i2.\n\
  \                          Commit(a2, b2, <" <> roleI <> ", " <> roleR <> ", t>) @ i2\n\
  \                          & not (#i2 = #i)) )\n\
  \         | (Ex X #r. Reveal(X) @ r)\"\n"
  where
    nm    = "inj_agree_" <> T.unpack i <> "_to_" <> T.unpack r
    roleI = "'" <> T.unpack i <> "'"
    roleR = "'" <> T.unpack r <> "'"

-- | Non-injective agreement — §2.3.4. Same as 'injAgreeLemma'
-- minus the injectivity clause.
agreeLemma :: OpenTheory -> T.Text -> T.Text -> [TermRef] -> Th.Lemma Th.ProofSkeleton
agreeLemma th i r _ts = buildLemma th nm $
  "lemma " <> nm <> ":\n\
  \  all-traces\n\
  \  \"All a b t #i.\n\
  \     Commit(a, b, <" <> roleI <> ", " <> roleR <> ", t>) @ i\n\
  \     ==> (Ex #j. Running(b, a, <" <> roleI <> ", " <> roleR <> ", t>) @ j & j < i)\n\
  \         | (Ex X #r. Reveal(X) @ r)\"\n"
  where
    nm    = "agree_" <> T.unpack i <> "_to_" <> T.unpack r
    roleI = "'" <> T.unpack i <> "'"
    roleR = "'" <> T.unpack r <> "'"

-- | Aliveness — Lowe's weakest authentication form, §2.3.5.
--
-- "If @a@ commits to running with @b@, then @b@ has at least
-- generated a long-term key (i.e., @b@ exists in the trace at
-- all)." Useful as a sanity check; @inj_agree@ is the form users
-- typically want.
aliveLemma :: OpenTheory -> T.Text -> T.Text -> Th.Lemma Th.ProofSkeleton
aliveLemma th i r = buildLemma th nm $
  "lemma " <> nm <> ":\n\
  \  all-traces\n\
  \  \"All a b t #i.\n\
  \     Commit(a, b, <" <> roleI <> ", " <> roleR <> ", t>) @ i\n\
  \     ==> (Ex lk #j. KeyGen(b, lk) @ j)\n\
  \         | (Ex X #r. Reveal(X) @ r)\"\n"
  where
    nm    = "aliveness_" <> T.unpack i <> "_to_" <> T.unpack r
    roleI = "'" <> T.unpack i <> "'"
    roleR = "'" <> T.unpack r <> "'"

addLemmaOrFail
  :: MonadThrow m => OpenTheory -> Th.Lemma Th.ProofSkeleton -> m OpenTheory
addLemmaOrFail th l = case Th.addLemma l th of
  Just th' -> pure th'
  -- This only fires on duplicate lemma names. The walking skeleton
  -- can hit it if a verify block has e.g. two `secrecy(k)` queries;
  -- once the lemma generator deduplicates by name we will never see
  -- this in practice.
  Nothing  -> error "Clementine.LowerSapic.addLemmaOrFail: \
                    \duplicate lemma name (TODO: dedupe in lowerQuery)"

--------------------------------------------------------------------------------
-- TODO[next]: real lowering
--
-- The following pieces are intentionally absent from this walking
-- skeleton. Each one is a self-contained next step that can be
-- landed independently:
--
-- 1. lowerProtocolToProcess :: Protocol -> PlainProcess
--    Build one Sapic process per principal, composed in parallel
--    under top-level replication. Each principal's process is
--    `! new ~ltk1; ...; new ~ltkN; <step body>`. Use ProcessAction
--    for individual actions and ProcessComb for combinators.
--
-- 2. lowerStep / lowerStmt
--    Map each Clementine StepStmt to a Sapic action:
--      SNew     -> ProcessAction (New v) ann k
--      SLet     -> ProcessComb (Let lhs rhs Set.empty) ann k null
--      SSend    -> ProcessAction (ChOut Nothing t) ann k
--      SRequire -> ProcessComb (CondEq t sapicTrue) ann k null
--      SClaim   -> ProcessAction (Event secretFact) ann k
--    On the receiver side a `send` becomes a ChIn — that decision
--    is driven by the per-step "is this principal the sender?"
--    flag computed in lowerProtocolToProcess.
--
-- 3. lowerExpr :: Expr -> SapicNTerm SapicLVar
--    Recursive walk over the AST, mapping primitive operators to
--    function symbols from Term.Builtin.Signature.
--
-- 4. Real lemma templates from §2.3 — replace the `trivial` helper
--    above with formula builders that quantify over the canonical
--    action facts (Secret, Running, Commit, Reveal, Honest, K).
--
-- 5. Sources lemma inference (§5) - call after Sapic.translate over
--    the resulting MSR rules, emit a single [sources] lemma.
--
-- All five are tracked in the project task list.
--------------------------------------------------------------------------------
