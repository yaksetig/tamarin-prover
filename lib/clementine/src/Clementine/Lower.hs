-- |
-- Module      : Clementine.Lower
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- Lowering pass: 'Clementine.AST.Protocol' to a (placeholder) compiled
-- form.
--
-- == v0.0 status
--
-- This is a /stub/. The intended target is 'Theory.OpenTheory', built
-- by lowering the Clementine AST to a 'Theory.Sapic.LProcess' and then
-- handing off to 'Sapic.translate' (which already implements the heavy
-- lifting: pattern destructuring, channel encodings, MSR generation).
--
-- For v0.0 we only build a 'CompiledTheory' summary value so that the
-- pipeline can be exercised end-to-end (parse → summarize → print)
-- without committing to a Theory-API integration we have not yet
-- validated against the compiler. The next milestone replaces
-- 'CompiledTheory' with 'OpenTheory' and wires in Sapic; everything
-- upstream of this module stays unchanged.
--
-- The order of the planned implementation, for the next iteration:
--
-- 1. Map each 'Principal' to a Sapic top-level process under
--    replication ('!new ~ltk; …').
-- 2. Map each 'Step' to a sequence of Sapic process actions
--    ('new', 'let', 'event', 'in', 'out').
-- 3. Use 'Sapic.LetDestructors.translateLetDestr' for receiver-side
--    pattern matching (the binding inference algorithm from design
--    step 2 §2.2.2).
-- 4. Generate canonical 'Theory.Lemma' values from 'protoVerify' using
--    the templates from design step 2 §2.3.
-- 5. Hand the resulting 'OpenTheory' to 'Sapic.translate'.
module Clementine.Lower
  ( CompiledTheory(..)
  , RoleSummary(..)
  , StepSummary(..)
  , LemmaSummary(..)
  , Origin(..)
  , originStep
  , originPrincipal
  , originQuery
  , originSynth
  , lowerProtocol
  ) where

import           Data.Text (Text)
import qualified Data.Text as T

import           Clementine.AST

-- | A human-readable summary of what 'lowerProtocol' /would/ produce
-- once the Sapic integration is wired up. Used by the v0.0 'clemc'
-- driver to give visible output for the round-trip test corpus.
data CompiledTheory = CompiledTheory
  { ctName     :: !Text
  , ctBuiltins :: ![Text]
  , ctRoles    :: ![RoleSummary]
  , ctSteps    :: ![StepSummary]
  , ctLemmas   :: ![LemmaSummary]
  } deriving (Show)

data RoleSummary = RoleSummary
  { rsName     :: !Text
  , rsLongTerm :: ![Text]   -- generated long-term keys
  , rsPublic   :: ![Text]   -- public parameters this role consumes
  , rsPrivate  :: ![Text]   -- private parameters this role consumes
  , rsOrigin   :: !Origin
  } deriving (Show)

data StepSummary = StepSummary
  { ssLabel     :: !Text
  , ssFrom      :: !Text
  , ssDirection :: !Text   -- "-> P" or "local"
  , ssOps       :: ![Text]  -- one entry per step body statement, prettied
  , ssOrigin    :: !Origin
  } deriving (Show)

data LemmaSummary = LemmaSummary
  { lsName     :: !Text
  , lsTemplate :: !Text     -- e.g. "secrecy", "fs", "inj_agree"
  , lsArgs     :: ![Text]
  , lsOrigin   :: !Origin
  } deriving (Show)

-- | Where a generated artifact came from. Used by 'Clementine.SourceMap'
-- to emit the JSON sidecar that maps generated rules and lemmas back
-- to their .clem source location.
--
-- We carry the source position together with a structured kind
-- (\"step m2 in principal B\", \"verify query #3\") so consumers don't
-- need to re-parse the .clem file to render meaningful labels.
data Origin = Origin
  { origPos  :: !SrcPos
  , origKind :: !Text
  } deriving (Show)

-- | Constructors that match the design of the JSON @origin.kind@ tag.
originStep :: Text -> Text -> SrcPos -> Origin
originStep prin lbl pos = Origin pos ("step " <> lbl <> " in principal " <> prin)

originPrincipal :: Text -> SrcPos -> Origin
originPrincipal n pos = Origin pos ("principal " <> n)

originQuery :: Text -> SrcPos -> Origin
originQuery kind pos = Origin pos ("verify query: " <> kind)

originSynth :: Text -> SrcPos -> Origin
originSynth label pos = Origin pos ("synthesized: " <> label)

-- | The lowering entry point. Pure and total: every well-formed AST
-- produces a 'CompiledTheory'. (Once we move to 'OpenTheory' this will
-- become 'Either LowerError OpenTheory' so the soundness invariants
-- from design step 3 §3.4 can refuse to emit ill-formed theories.)
lowerProtocol :: Protocol -> CompiledTheory
lowerProtocol p = CompiledTheory
  { ctName     = protoName p
  , ctBuiltins = map builtinName (protoBuiltins p)
  , ctRoles    = map summarizeRole (protoPrincipals p)
  , ctSteps    = map summarizeStep (protoSteps p)
  , ctLemmas   = concatMap (summarizeQuery (protoPrincipals p)) (protoVerify p)
  }

builtinName :: Builtin -> Text
builtinName = \case
  BIDH      -> "diffie-hellman"
  BISigning -> "signing"
  BIHashing -> "hashing"
  BISymEnc  -> "symmetric-encryption"
  BIAsymEnc -> "asymmetric-encryption"

summarizeRole :: Principal -> RoleSummary
summarizeRole pr = RoleSummary
  { rsName     = prinName pr
  , rsLongTerm = [n | KGenerates    n _   <- prinKnows pr]
  , rsPublic   = [n | KKnowsPublic  n _ _ <- prinKnows pr]
  , rsPrivate  = [n | KKnowsPrivate n _   <- prinKnows pr]
  , rsOrigin   = originPrincipal (prinName pr) (prinPos pr)
  }

summarizeStep :: Step -> StepSummary
summarizeStep s = StepSummary
  { ssLabel     = stepLabel s
  , ssFrom      = stepFrom s
  , ssDirection = case stepKind s of
      StepLocal             -> "local"
      StepNetwork to ch     -> arrow ch <> " " <> to
  , ssOps       = map describeStmt (stepBody s)
  , ssOrigin    = originStep (stepFrom s) (stepLabel s) (stepPos s)
  }
  where
    arrow ChNet    = "->"
    arrow ChAuth   = "~>"
    arrow ChConf   = "=>"
    arrow ChSecure = ":>"

describeStmt :: StepStmt -> Text
describeStmt = \case
  SNew n _              -> "new " <> n
  SLet n e _            -> "let " <> n <> " = " <> renderExpr e
  SRequire e _          -> "require " <> renderExpr e
  SSend e _             -> "send " <> renderExpr e
  SClaim (ClaimSecret n) _ -> "claim secret(" <> n <> ")"

renderExpr :: Expr -> Text
renderExpr = \case
  EVar n _      -> n
  EConst c _    -> "'" <> c <> "'"
  ETup es _     -> "<" <> T.intercalate ", " (map renderExpr es) <> ">"
  EApp op args _ -> primText op <> "(" <> T.intercalate ", " (map renderExpr args) <> ")"
  EExp e1 e2 _  -> renderExpr e1 <> "^" <> renderExpr e2
  where
    primText OpEnc    = "ENC"
    primText OpDec    = "DEC"
    primText OpAEnc   = "AENC"
    primText OpADec   = "ADEC"
    primText OpPK     = "PK"
    primText OpSign   = "SIGN"
    primText OpVerify = "VERIFY"
    primText OpH      = "H"
    primText OpMAC    = "MAC"

summarizeQuery :: [Principal] -> Query -> [LemmaSummary]
summarizeQuery _ q = case q of
  QExecutable pos              ->
    [LemmaSummary "executable" "exists-trace" [] (originQuery "executable" pos)]
  QSecrecy t pos               ->
    [LemmaSummary ("secrecy_" <> trVar t) "secrecy" [trVar t] (originQuery "secrecy" pos)]
  QForwardSecrecy t pos        ->
    [LemmaSummary ("fs_" <> trVar t) "fs" [trVar t] (originQuery "forward_secrecy" pos)]
  QInjAgreement a b ts pos     ->
    [LemmaSummary ("inj_agree_" <> a <> "_" <> b) "inj_agree"
                  (a : b : map trVar ts) (originQuery "injective_agreement" pos)]
  QNonInjAgreement a b ts pos  ->
    [LemmaSummary ("agree_" <> a <> "_" <> b) "agree"
                  (a : b : map trVar ts) (originQuery "non_injective_agreement" pos)]
  QAuthentication a b pos      ->
    [LemmaSummary ("aliveness_" <> a <> "_to_" <> b) "aliveness"
                  [a, b] (originQuery "authentication" pos)]
