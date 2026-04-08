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
import           Control.Category      ((.))

import           Control.Monad         (foldM)
import           Control.Monad.Catch   (MonadThrow, MonadCatch)
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
  th2 <- foldM addLemmaOrFail th1
                   (concatMap (lowerQuery th1 p) (protoVerify p))
  Sapic.translate th2

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
lowerProtocolToProcess' p = parallelOf
  [ lowerPrincipal principalNames (protoSteps p) prin
  | prin <- protoPrincipals p
  ]
  where
    principalNames = map prinName (protoPrincipals p)

    parallelOf :: [PlainProcess] -> PlainProcess
    parallelOf []  = ProcessNull mempty
    parallelOf [x] = x
    parallelOf xs  =
      let (l, r) = splitAt (length xs `div` 2) xs
      in  ProcessComb Parallel mempty (parallelOf l) (parallelOf r)

-- | Lower one principal: long-term key freshes, then the sequence
-- of step actions belonging to this principal (as sender, receiver,
-- or local actor), all wrapped in top-level replication.
lowerPrincipal :: [T.Text] -> [Step] -> Principal -> PlainProcess
lowerPrincipal principalNames allSteps pr =
    ProcessAction Rep mempty
      $ withFreshKeys [n | KGenerates n _ <- prinKnows pr]
      $ stepSequence ctx0 (relevantSteps (prinName pr) allSteps)
      $ ProcessNull mempty
  where
    withFreshKeys []     k = k
    withFreshKeys (n:ns) k =
      ProcessAction (New (mkSapicVar n)) mempty (withFreshKeys ns k)

    ctx0 = LowerCtx
      { lcReceived       = Set.empty
      , lcPrincipalNames = Set.fromList principalNames
      , lcPublicParams   = Set.fromList
          [n | KKnowsPublic n _ _ <- prinKnows pr]
      }

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
  }

-- | The role this principal plays in a given step.
data StepRole = RSender | RReceiver | RLocalActor

-- | Steps that this principal participates in, in declaration order,
-- tagged with the role the principal plays.
relevantSteps :: T.Text -> [Step] -> [(Step, StepRole)]
relevantSteps p = mapMaybe pick
  where
    pick s
      | stepFrom s == p = case stepKind s of
          StepLocal       -> Just (s, RLocalActor)
          StepNetwork _ _ -> Just (s, RSender)
      | otherwise = case stepKind s of
          StepNetwork tgt _ | tgt == p -> Just (s, RReceiver)
          _                            -> Nothing

stepSequence :: LowerCtx -> [(Step, StepRole)] -> PlainProcess -> PlainProcess
stepSequence _   []           k = k
stepSequence ctx ((s,r):rest) k =
  -- After a receive, the variables in the sent expression become
  -- "received" on this principal's side and any subsequent
  -- reference to them must use the pat_-prefixed name. Sender and
  -- local steps do not change the context.
  let ctx' = case r of
        RReceiver -> ctx { lcReceived = lcReceived ctx
                                       <> collectVarsBody (stepBody s) }
        _         -> ctx
  in  lowerStep ctx s r (stepSequence ctx' rest k)

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
lowerStep :: LowerCtx -> Step -> StepRole -> PlainProcess -> PlainProcess
lowerStep ctx s role = case role of
  RSender     -> foldSenderStmts (stepBody s)
  RLocalActor -> foldSenderStmts (stepBody s)
  RReceiver   -> emitReceive (stepBody s)
  where
    foldSenderStmts []     k = k
    foldSenderStmts (x:xs) k = lowerStmt ctx role x (foldSenderStmts xs k)

    -- The receiver only consumes the wire message. We find the
    -- (single) 'SSend' in the body and emit a 'ChIn' for it. If
    -- there is no SSend (a `local` step accidentally tagged as
    -- network) we emit nothing.
    emitReceive body k = case [e | SSend e _ <- body] of
      []      -> k
      (e : _) ->
        ProcessAction
          (ChIn Nothing (lowerExprPat ctx e) Set.empty)
          mempty
          k

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
resolveVar :: LowerCtx -> T.Text -> SapicNTerm SapicLVar
resolveVar ctx n
  | n `Set.member` lcPrincipalNames ctx = pubTerm (T.unpack n)
  | n `Set.member` lcPublicParams   ctx = pubTerm (T.unpack n)
  | n `Set.member` lcReceived ctx       = varTerm (mkPatVar n)
  | otherwise                           = varTerm (mkSapicVar n)
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
-- pattern variable with the @pat@ prefix. Principal names still
-- lower to public constants. The @ctx@ argument is unused for the
-- variable handling itself but kept symmetric so call sites stay
-- uniform.
lowerExprPat :: LowerCtx -> Expr -> SapicNTerm SapicLVar
lowerExprPat ctx e = case e of
  EVar n _
    | n `Set.member` lcPrincipalNames ctx -> pubTerm (T.unpack n)
    | n `Set.member` lcPublicParams   ctx -> pubTerm (T.unpack n)
    | otherwise                           -> varTerm (mkPatVar n)
  EConst c _     -> pubTerm (T.unpack c)
  ETup [] _      -> pubTerm "unit"
  ETup [x] _     -> lowerExprPat ctx x
  ETup xs _      -> foldr1Pair (map (lowerExprPat ctx) xs)
  EApp op args _ -> lowerPrimApp op (map (lowerExprPat ctx) args)
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
