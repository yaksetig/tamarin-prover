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

-- tamarin-prover-theory
import qualified Theory                as Th
import           Theory                ( OpenTheory, defaultOpenTheory
                                       , prettyOpenTheory
                                       , TraceQuantifier(..) )
import           Theory.ProofSkeleton  (unprovenLemma)
import           Theory.Model.Formula  (ltrue, LNFormula)
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
  -- Add lemmas first; the walking skeleton has no process to add.
  th1 <- foldM addLemmaOrFail th0 (concatMap (lowerQuery p) (protoVerify p))
  -- Sapic.translate is a no-op when there is no process attached
  -- (verified by reading lib/sapic/src/Sapic.hs:48-52). We still
  -- call it so the pipeline shape matches the eventual non-trivial
  -- case where we DO add a process.
  Sapic.translate th1

-- | Convenience: lower and pretty-print to a String containing the
-- generated .spthy text. This is what the @clemc@ driver writes to
-- disk when built with @--flag with-sapic@.
lowerProtocolSapicText
  :: (MonadThrow m, MonadCatch m)
  => Protocol
  -> m String
lowerProtocolSapicText p = do
  th <- lowerProtocolSapic p
  pure (render (prettyOpenTheory th :: Doc))

--------------------------------------------------------------------------------
-- Lemma generation
--------------------------------------------------------------------------------

-- | Lower one verify query to one or more lemmas.
--
-- Walking-skeleton implementation: every query becomes a trivial
-- @True@ lemma named after the query. The lemma name is taken from
-- the same scheme as 'Clementine.Lower.summarizeQuery' so the
-- generated theory and the source-map sidecar agree.
--
-- The next iteration of this function will instantiate the §2.3
-- templates (Secret/Running/Commit/etc.) instead of @ltrue@. Doing
-- it that way means each upgrade is a strict improvement: the
-- pipeline stays valid, and any lemma that we have not yet ported
-- still emits a runnable (if uninteresting) skeleton.
lowerQuery :: Protocol -> Query -> [Th.Lemma Th.ProofSkeleton]
lowerQuery _ q = case q of
  QExecutable _              -> [trivial "executable"        ExistsTrace]
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
