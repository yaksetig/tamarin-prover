-- |
-- Module      : Clementine.LowerSapic
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- == Real lowering: Clementine AST -> Theory.OpenTheory via Sapic
--
-- This module replaces the v0.0 'Clementine.Lower.CompiledTheory'
-- summary with a real 'Theory.OpenTheory' value, by:
--
--   1. Constructing one 'Theory.Sapic.PlainProcess' per principal,
--      composed in parallel under top-level replication.
--   2. Generating 'Theory.Lemma' values from the @verify@ block using
--      the templates from Clementine design step 2 §2.3 with the
--      action-fact contract from design step 3 §3.1.
--   3. Adding both to a 'Theory.OpenTheory' built from
--      'Theory.defaultOpenTheory'.
--   4. Calling 'Sapic.translate' to perform pattern destructuring
--      ('Sapic.LetDestructors'), channel encoding, and MSR
--      generation.
--
-- == Build status
--
-- This module is gated by the @with-sapic@ cabal flag, which is OFF
-- by default. The flag is OFF because the wider tamarin-prover
-- workspace currently has dependency drift on @fclabels < 2@ and
-- @template-haskell < 2.9@ that prevents @tamarin-prover-utils@ from
-- building against modern GHCs (verified with GHC 9.14). Once the
-- workspace is restored to a buildable state — likely via a stack
-- LTS bump or fclabels modernisation in 'tamarin-prover-utils' — the
-- @with-sapic@ flag can be turned on by default and this module
-- becomes the production lowering path.
--
-- The code below is written against the API surface I have read out
-- of @lib/sapic/src/Sapic.hs@ and @lib/theory/src/Theory/Sapic@ in
-- the same revision as the rest of this scaffold. It has NOT been
-- compiled. Sections that depend on details I could not statically
-- verify (the precise spelling of 'SapicNTerm' constructors,
-- 'ProcessParsedAnnotation' field defaults, the 'addLemma' Either
-- shape) are flagged with @TODO[verify]@ comments and concentrated
-- in the helper functions at the bottom of this module so they can
-- be filled in once the workspace builds.
module Clementine.LowerSapic
  ( lowerProtocolSapic
  , LowerError(..)
  ) where

import           Control.Monad         (foldM)
import           Control.Monad.Catch   (MonadThrow, MonadCatch)
import qualified Data.Set              as Set
import           Data.Text             (Text)
import qualified Data.Text             as T

-- tamarin-prover-theory
import qualified Theory                as Th
import           Theory                (OpenTheory, defaultOpenTheory)
import           Theory.Sapic
                   ( PlainProcess
                   , Process(..)
                   , SapicAction(..)
                   , ProcessCombinator(..)
                   )
-- tamarin-prover-sapic
import qualified Sapic

import           Clementine.AST

--------------------------------------------------------------------------------
-- Errors specific to the Sapic lowering
--------------------------------------------------------------------------------

-- | Errors that can arise during the Sapic lowering. These wrap into
-- 'Clementine.Errors.ClementineError' at the top of the driver, with
-- the appropriate @E0500-E0599@ code.
data LowerError
  = LowerUndefinedPrincipal Text
  | LowerEmptyVerifyBlock
  | LowerSapicTranslationFailed String
  deriving (Show)

--------------------------------------------------------------------------------
-- Top-level entry point
--------------------------------------------------------------------------------

-- | Lower a Clementine 'Protocol' to a fully translated
-- 'Theory.OpenTheory'. Pure up to the 'Sapic.translate' call, which
-- runs in 'MonadThrow' / 'MonadCatch' to propagate Sapic exceptions
-- from its many internal phases.
lowerProtocolSapic
  :: (MonadThrow m, MonadCatch m)
  => Protocol
  -> m OpenTheory
lowerProtocolSapic p = do
  -- 1. Empty starting theory.
  let th0 = defaultOpenTheory False

  -- 2. Build the Sapic process and add it.
  let proc = lowerProtocolToProcess p
  let th1  = Th.addProcess proc th0

  -- 3. Generate lemmas from the verify block. We use 'addLemma' which
  --    returns 'Maybe OpenTheory' (Nothing on duplicate lemma name).
  th2 <- foldM addLemmaOrFail th1 (concatMap (lowerQuery p) (protoVerify p))

  -- 4. Run Sapic's MSR generation pipeline.
  Sapic.translate th2

addLemmaOrFail
  :: MonadThrow m => OpenTheory -> Th.Lemma Th.ProofSkeleton -> m OpenTheory
addLemmaOrFail th l = case Th.addLemma l th of
  Just th' -> pure th'
  -- TODO[verify]: wrap as ClementineError once routed through
  -- Clementine.hs; for now we fail loudly so the bug is obvious.
  -- The lemma name is an fclabels lens not a plain accessor, so
  -- printing it requires `get lName l`; deferred until we wire the
  -- Extension.Data.Label import.
  Nothing  -> error "Clementine.LowerSapic.addLemmaOrFail: \
                    \duplicate lemma name (TODO[verify]: format with \
                    \Extension.Data.Label.get and Th.lName)"

--------------------------------------------------------------------------------
-- AST -> Sapic.PlainProcess
--------------------------------------------------------------------------------

-- | Compose every principal's process in parallel under top-level
-- replication. Each principal becomes:
--
-- @
--     ! ( new ~ltk1 ;
--         ...
--         new ~ltkN ;
--         step1 ; step2 ; ... ; 0 )
-- @
--
-- The Sapic 'Parallel' combinator binds left-associatively for our
-- purposes, but we balance the tree to keep proof sizes manageable.
lowerProtocolToProcess :: Protocol -> PlainProcess
lowerProtocolToProcess p =
    parallelOf (map (lowerPrincipal (protoSteps p)) (protoPrincipals p))
  where
    parallelOf :: [PlainProcess] -> PlainProcess
    parallelOf []     = ProcessNull defaultAnn
    parallelOf [x]    = x
    parallelOf xs     =
      let (l, r) = splitAt (length xs `div` 2) xs
      in  ProcessComb Parallel defaultAnn (parallelOf l) (parallelOf r)

-- | Lower a single principal: long-term key freshes wrapped around
-- the role's step sequence under replication.
lowerPrincipal :: [Step] -> Principal -> PlainProcess
lowerPrincipal allSteps prin =
    bangReplicate
      $ withFreshKeys (longTermKeys prin)
      $ stepSequence (stepsOf (prinName prin) allSteps)
      $ ProcessNull defaultAnn
  where
    bangReplicate body = ProcessAction Rep defaultAnn body

    withFreshKeys [] body = body
    withFreshKeys (k:ks) body =
      ProcessAction (New (sapicVar k)) defaultAnn (withFreshKeys ks body)

    longTermKeys p = [n | KGenerates n _ <- prinKnows p]

-- | The steps belonging to a given principal — those whose 'stepFrom'
-- matches, plus those whose 'stepKind' is a network step targeting
-- this principal as receiver.
stepsOf :: Text -> [Step] -> [(Step, Bool)]
stepsOf name = concatMap categorize
  where
    -- Bool flag is True if this principal is the SENDER, False if
    -- this principal is the RECEIVER for the step.
    categorize s
      | stepFrom s == name = [(s, True)]
      | otherwise = case stepKind s of
          StepNetwork target _ | target == name -> [(s, False)]
          _ -> []

-- | Sequence a list of (step, isSender) into a Sapic process.
stepSequence :: [(Step, Bool)] -> PlainProcess -> PlainProcess
stepSequence []           k = k
stepSequence ((s,sn):rest) k = lowerStep s sn (stepSequence rest k)

-- | Lower one step into a chain of Sapic actions terminated by the
-- continuation @k@.
lowerStep :: Step -> Bool -> PlainProcess -> PlainProcess
lowerStep step isSender k =
    foldStmts (stepBody step) k
  where
    foldStmts []     cont = cont
    foldStmts (x:xs) cont = lowerStmt x isSender (foldStmts xs cont)

lowerStmt :: StepStmt -> Bool -> PlainProcess -> PlainProcess
lowerStmt stmt isSender k = case stmt of

  SNew n _ ->
    ProcessAction (New (sapicVar n)) defaultAnn k

  SLet n e _ ->
    ProcessComb
      (Let { letLeft  = sapicVarTerm n
           , letRight = lowerExpr e
           , letMatch = Set.empty
           })
      defaultAnn
      k
      (ProcessNull defaultAnn)

  SRequire e _ ->
    -- A `require` becomes a CondEq guard: continue iff the expression
    -- evaluates to a tautology. For a verify(...) call this matches
    -- the standard `Eq(verify(...), true)` idiom from design step 2.
    ProcessComb
      (CondEq (lowerExpr e) sapicTrue)
      defaultAnn
      k
      (ProcessNull defaultAnn)

  SSend e _
    | isSender ->
        ProcessAction (ChOut Nothing (lowerExpr e)) defaultAnn k
    | otherwise ->
        -- The receiver "consumes" the same expression via In; the
        -- inference algorithm from design step 2 §2.2.2 handles
        -- pattern destructuring downstream via Sapic.LetDestructors.
        ProcessAction
          (ChIn { inChan = Nothing
                , inMsg  = lowerExpr e
                , inMatch = Set.empty })
          defaultAnn
          k

  SClaim (ClaimSecret n) _ ->
    -- Emit Secret(<role>, <'tag', term>) as an Event action so the
    -- secrecy lemma template (§2.3.1) has a fact to quantify over.
    ProcessAction
      (Event (secretEventFact n))
      defaultAnn
      k

--------------------------------------------------------------------------------
-- AST.Expr -> Sapic term
--
-- The Sapic term type is 'SapicNTerm SapicLVar'. We translate
-- structurally; primitive operators map to function applications
-- using the standard Tamarin signatures imported by the matching
-- builtin (asymmetric_encryption, signing, etc.).
--
-- TODO[verify]: All of these helpers want concrete API calls into
-- 'Theory.Sapic.Term' / 'Term.LTerm' which I have not statically
-- verified against the source. The /shapes/ are right; the precise
-- function names may need touching up. They are concentrated here so
-- the rest of the file stays correct.
--------------------------------------------------------------------------------

-- TODO[verify]: replace placeholder with the real LNTerm constructors
-- once the workspace builds. The pattern is:
--   sapicVar n     ~~  freshVar (T.unpack n)
--   sapicVarTerm n ~~  varTerm  (sapicVar n)
--   sapicTrue      ~~  fAppNoEq trueSym []
--   secretEventFact n ~~ Fact "Secret" Linear [varTerm currentRole, ...]
sapicVar :: Text -> a
sapicVar = error "Clementine.LowerSapic.sapicVar: TODO[verify] — \
                 \construct SapicLVar from Text"

sapicVarTerm :: Text -> a
sapicVarTerm = error "Clementine.LowerSapic.sapicVarTerm: TODO[verify] — \
                     \construct SapicNTerm from Text"

sapicTrue :: a
sapicTrue = error "Clementine.LowerSapic.sapicTrue: TODO[verify] — \
                  \the 'true' constant in the active equational theory"

secretEventFact :: Text -> a
secretEventFact = error "Clementine.LowerSapic.secretEventFact: TODO[verify] — \
                        \construct a Secret(<role>, <'<n>', <var n>>) fact"

-- TODO[verify]: lower an Expr to a SapicNTerm. Recurses on the
-- structure with the obvious mapping for tuples / primitives / DH.
lowerExpr :: Expr -> a
lowerExpr e = case e of
  EVar  n _      -> sapicVarTerm n
  EConst c _     -> error ("EConst " ++ T.unpack c ++ " — TODO[verify]")
  ETup  _ _      -> error "ETup — TODO[verify] (use pair/triple constructor)"
  EApp  _op _ _  -> error "EApp — TODO[verify] (look up Tamarin function symbol)"
  EExp  _ _ _    -> error "EExp — TODO[verify] (DH ^ from diffie-hellman builtin)"

-- | A default 'ProcessParsedAnnotation' for synthesized Sapic nodes.
-- The parser annotation is empty since we generate processes without
-- a parsed source position; the SOURCE comments come from
-- 'Clementine.Lower.Origin' and 'Clementine.SourceMap' instead.
defaultAnn :: a
defaultAnn = error "Clementine.LowerSapic.defaultAnn: TODO[verify] — \
                   \empty ProcessParsedAnnotation value"

--------------------------------------------------------------------------------
-- AST.Query -> Theory.Lemma
--
-- One conjunctive Lemma per Query, generated from the §2.3 templates.
-- The Lemma's formula is built using Theory.Model.Formula constructors.
--------------------------------------------------------------------------------

-- TODO[verify]: instantiate the §2.3 lemma templates as
-- Theory.Lemma values. The exact constructors live in
-- @Theory.Model.Formula@ and @Theory@ (re-exported). For each query
-- we build a 'ProtoFormula' and wrap it in 'Lemma' with the right
-- 'TraceQuantifier' (AllTraces vs ExistsTrace).
lowerQuery :: Protocol -> Query -> [Th.Lemma Th.ProofSkeleton]
lowerQuery _ q = case q of
  QExecutable _              -> error "lowerQuery executable — TODO[verify]"
  QSecrecy _ _               -> error "lowerQuery secrecy — TODO[verify]"
  QForwardSecrecy _ _        -> error "lowerQuery forward_secrecy — TODO[verify]"
  QInjAgreement _ _ _ _      -> error "lowerQuery injective_agreement — TODO[verify]"
  QNonInjAgreement _ _ _ _   -> error "lowerQuery non_injective_agreement — TODO[verify]"
  QAuthentication _ _ _      -> error "lowerQuery authentication — TODO[verify]"

--------------------------------------------------------------------------------
-- Notes for the next iteration
--
-- 1. The pattern destructuring algorithm from design step 2 §2.2.2
--    is NOT in this module. We rely on Sapic.LetDestructors to do it
--    automatically once 'Sapic.translate' runs over our process. The
--    only thing we have to get right is feeding it 'Let' combinators
--    whose left-hand side is a destructor application.
--
-- 2. The action-fact contract from design step 3 §3.1 maps onto Sapic
--    Event actions. The lemma templates from §2.3 reference these by
--    name; as long as our Event constructors emit facts with the
--    canonical names ('Secret', 'Running', 'Commit', 'Honest',
--    'Reveal', 'KeyGen', 'Step_<role>_<lbl>'), the lemmas will
--    quantify over them correctly.
--
-- 3. Sources lemma inference (design step 5) runs AFTER
--    'Sapic.translate' on the resulting MSR rules, not on the Sapic
--    process. It walks 'Theory.theoryRules' and emits a single
--    auto-sources Lemma annotated with [sources]. This lives in
--    'Clementine.Sources' (also gated on the with-sapic flag), not
--    in this module.
--------------------------------------------------------------------------------
