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

import           Control.Monad         (foldM)
import           Control.Monad.Catch   (MonadThrow, MonadCatch)
import qualified Data.Text             as T

-- tamarin-prover-term
import           Term.LTerm            (LVar(..), LSort(..))

-- tamarin-prover-theory
import qualified Theory                as Th
import           Theory                ( OpenTheory, defaultOpenTheory
                                       , prettyOpenTranslatedTheory
                                       , removeTranslationItems
                                       , TraceQuantifier(..) )
import           Theory.ProofSkeleton  (unprovenLemma)
import           Theory.Model.Formula  (ltrue, LNFormula)
import           Theory.Text.Parser    (parseLemmaWithMacros)
import           Theory.Sapic          ( PlainProcess
                                       , Process(..)
                                       , SapicAction(..)
                                       , ProcessCombinator(..)
                                       , SapicLVar(..)
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
  let th0 = defaultOpenTheory False
      -- One Sapic process for the whole protocol; principals are
      -- composed in parallel under top-level replication.
      proc = lowerProtocolToProcess p
      th1  = Th.addProcess proc th0
  th2 <- foldM addLemmaOrFail th1
                   (concatMap (lowerQuery th1 p) (protoVerify p))
  Sapic.translate th2

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
lowerProtocolToProcess p = parallelOf (map lowerPrincipal (protoPrincipals p))
  where
    -- Balance the parallel tree to avoid quadratic proof shape on
    -- protocols with many principals.
    parallelOf :: [PlainProcess] -> PlainProcess
    parallelOf []  = ProcessNull mempty
    parallelOf [x] = x
    parallelOf xs  =
      let (l, r) = splitAt (length xs `div` 2) xs
      in  ProcessComb Parallel mempty (parallelOf l) (parallelOf r)

-- | Lower one principal to `! new ~ltk1; new ~ltk2; ...; 0`.
lowerPrincipal :: Principal -> PlainProcess
lowerPrincipal pr =
    ProcessAction Rep mempty
      $ withFreshKeys
          [n | KGenerates n _ <- prinKnows pr]
          (ProcessNull mempty)
  where
    withFreshKeys []     k = k
    withFreshKeys (n:ns) k =
      ProcessAction (New (mkSapicVar n)) mempty (withFreshKeys ns k)

-- | Build a fresh-sorted Sapic variable from a Clementine identifier.
-- We pick LSortFresh because every Clementine `generates` corresponds
-- to a Tamarin Fr() premise.
mkSapicVar :: T.Text -> SapicLVar
mkSapicVar name =
  SapicLVar (LVar (T.unpack name) LSortFresh 0) Nothing

--------------------------------------------------------------------------------
-- Lemma generation
--------------------------------------------------------------------------------

-- | Lower one verify query to one or more lemmas.
--
-- Status: most queries still produce trivial @True@ lemmas (the
-- walking skeleton). The exception is 'QExecutable', which is the
-- first query to use a real formula — it asserts that the protocol
-- starts at all by quantifying over the @Init@ action fact that
-- Sapic emits at the head of every translated process.
--
-- The next iteration replaces the trivial cases with the §2.3
-- templates (Secret/Running/Commit/etc.). Each upgrade is strict:
-- the pipeline stays valid, and any lemma not yet ported still
-- emits a runnable (if uninteresting) skeleton.
lowerQuery :: OpenTheory -> Protocol -> Query -> [Th.Lemma Th.ProofSkeleton]
lowerQuery th _ q = case q of
  QExecutable _              -> [executable th]
  QSecrecy t _               -> [trivial ("secrecy_"   <> name t) AllTraces]
  QForwardSecrecy t _        -> [trivial ("fs_"        <> name t) AllTraces]
  QInjAgreement i r _ _      -> [trivial ("inj_agree_" <> sId i r) AllTraces]
  QNonInjAgreement i r _ _   -> [trivial ("agree_"     <> sId i r) AllTraces]
  QAuthentication i r _      -> [trivial ("aliveness_" <> sId i r) AllTraces]
  where
    name t        = T.unpack (trVar t)
    sId i r       = T.unpack i <> "_to_" <> T.unpack r

    -- Build a Lemma whose body is just `True`. The proof skeleton is
    -- left unproven; tamarin-prover will discharge it trivially.
    trivial :: String -> TraceQuantifier -> Th.Lemma Th.ProofSkeleton
    trivial nm qua = unprovenLemma nm [] qua (ltrue :: LNFormula)

-- | The executable lemma: assert that some honest run actually
-- starts. We quantify over the @Init@ action fact that
-- 'Sapic.Basetranslation' emits at the head of every translated
-- process — so as soon as we have a non-empty process, this lemma
-- is provable by witnessing the trace that fires the @Init@ rule.
--
-- Built by parsing the lemma source through the existing
-- 'parseLemmaWithMacros' instead of constructing a 'ProtoFormula'
-- AST by hand. The risk of the parser ever rejecting our hard-coded
-- string is low — if it does, the @error@ surfaces immediately at
-- compile-time of the first @clemc@ run rather than silently
-- producing wrong proofs.
executable :: OpenTheory -> Th.Lemma Th.ProofSkeleton
executable th =
  case parseLemmaWithMacros th lemmaSrc of
    Left e  -> error ("Clementine.LowerSapic.executable: internal: \
                      \failed to parse hard-coded executable lemma: "
                      ++ show e)
    Right l -> l
  where
    lemmaSrc =
      "lemma executable:\n\
      \  exists-trace\n\
      \  \"Ex #i. Init() @ #i\""

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
