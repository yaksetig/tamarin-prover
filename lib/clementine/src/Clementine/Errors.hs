{-# LANGUAGE TemplateHaskell #-}
-- |
-- Module      : Clementine.Errors
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- Error code taxonomy for the Clementine compiler.
--
-- Each error has a stable identifier (e.g. @E0001@). Codes are
-- /never/ renumbered. The Rust convention applies: once a code is in
-- the wild, even if the underlying check is removed, the code stays
-- reserved and the explanation file is kept.
--
-- Each code has a long-form markdown explanation under
-- @lib/clementine/explain/E####.md@, embedded into the binary at
-- compile time via 'file-embed'. The 'explain' function returns the
-- explanation for a given code, used by @clemc --explain E0023@.
module Clementine.Errors
  ( -- * Error type
    ClementineError(..)
  , ErrorCode(..)
  , ErrorSeverity(..)
    -- * Code metadata
  , errorCodeText
  , errorCodeSeverity
  , errorCodeShortDesc
  , allErrorCodes
    -- * Pretty printing
  , renderError
    -- * --explain flag
  , explain
  , explainAll
  ) where

import           Data.FileEmbed     (embedDir)
import           Data.Map.Strict    (Map)
import qualified Data.Map.Strict    as Map
import           Data.Maybe         (fromMaybe)
import           Data.Text          (Text)
import qualified Data.Text          as T
import qualified Data.Text.Encoding as T
import qualified Data.ByteString    as BS

import           Clementine.AST     (SrcPos(..))

--------------------------------------------------------------------------------
-- Error codes
--------------------------------------------------------------------------------

-- | Stable error identifier.
--
-- Naming convention: @E####@ for errors that prevent compilation,
-- @W####@ for warnings that allow compilation but flag a soundness
-- concern. Numbers are assigned in groups:
--
-- * @E0001-E0099@ — parser / surface syntax
-- * @E0100-E0199@ — name resolution and term references
-- * @E0200-E0299@ — soundness invariants from design step 3 §3.4
-- * @E0300-E0399@ — verify-block lemma generation
-- * @E0400-E0499@ — sources lemma inference
-- * @E0500-E0599@ — Sapic lowering / channel encoding
-- * @W1000+@      — warnings
data ErrorCode
  -- Parser
  = E0001  -- ^ generic parser failure
  | E0002  -- ^ unexpected end of input
  | E0003  -- ^ reserved word used as identifier

  -- Name resolution / term references
  | E0100  -- ^ undefined identifier
  | E0101  -- ^ ambiguous term reference in verify block
  | E0102  -- ^ undefined term reference in verify block
  | E0103  -- ^ duplicate principal name
  | E0104  -- ^ duplicate step label
  | E0105  -- ^ free variable in step body has no source
  | E0106  -- ^ shadowing within a step body

  -- Soundness invariants (design step 3 §3.4, the nine compiler invariants)
  | E0201  -- ^ §3.4 inv 1: action fact arity drift
  | E0202  -- ^ §3.4 inv 2: Reveal references unhonest agent
  | E0203  -- ^ §3.4 inv 3: Reveal rule has no !Ltk premise
  | E0204  -- ^ §3.4 inv 4: Commit unreachable from any Running
  | E0205  -- ^ §3.4 inv 5: Secret references undefined term
  | E0206  -- ^ §3.4 inv 6: no executable lemma in verify block
  | E0207  -- ^ §3.4 inv 7: reserved-name shadow
  | E0208  -- ^ §3.4 inv 8: phase coherence (FS without phase or temporal anchor)
  | E0209  -- ^ §3.4 inv 9: honest peer not reachable for agreement lemma

  -- Verify-block lemma placement (design step 2 §2.3, step 3 §3.2)
  | E0301  -- ^ injective_agreement: no joint scope for terms on initiator
  | E0302  -- ^ injective_agreement: no joint scope for terms on responder
  | E0303  -- ^ Commit/Running cannot be ordered (responder runs after initiator commits)
  | E0304  -- ^ secrecy(t): t never appears in any rule's scope
  | E0305  -- ^ unlinkability requested but heuristic predicts non-termination

  -- Sources lemma inference (design step 5)
  | E0401  -- ^ open chain detected but no honest origin found
  | E0402  -- ^ cleartext + wrapped envelopes for same fresh; sources lemma is wrong

  -- Sapic lowering / channels
  | E0501  -- ^ channel arrow refers to undeclared :> channel
  | E0502  -- ^ feature not yet implemented in v0.0 Lower stub

  -- Warnings
  | W1001  -- ^ authentication() is aliveness only
  | W1002  -- ^ unlinkability proof may not terminate
  | W1003  -- ^ Secret claim auto-placed; add explicit claim secret
  | W1004  -- ^ auto-sources lemma over-generated
  | W1005  -- ^ auto-tagging fired on a step that already had explicit tags
  | W1006  -- ^ peer reachable only via registered (honest) form; UKS attacks not modelled
  deriving (Eq, Ord, Show, Read, Bounded, Enum)

-- | Severity controls how the driver reports the diagnostic and
-- whether compilation continues.
data ErrorSeverity = SevError | SevWarning
  deriving (Eq, Ord, Show)

-- | A diagnostic, with optional source location and a free-form
-- detail message that the renderer prints under the headline.
data ClementineError = ClementineError
  { errCode    :: !ErrorCode
  , errPos     :: !(Maybe SrcPos)
  , errMsg     :: !Text
  , errDetails :: ![Text]   -- ^ extra context lines, printed indented
  } deriving (Show)

-- | List of every error code, in declaration order. Used by 'explainAll'.
allErrorCodes :: [ErrorCode]
allErrorCodes = [minBound..maxBound]

-- | Render the code as @E0001@/@W1001@.
errorCodeText :: ErrorCode -> Text
errorCodeText = T.pack . show

-- | Severity for a given code.
errorCodeSeverity :: ErrorCode -> ErrorSeverity
errorCodeSeverity c
  | T.head (errorCodeText c) == 'W' = SevWarning
  | otherwise                       = SevError

-- | The single-line summary that appears in the diagnostic header.
errorCodeShortDesc :: ErrorCode -> Text
errorCodeShortDesc = \case
  E0001 -> "parser failure"
  E0002 -> "unexpected end of input"
  E0003 -> "reserved word used as identifier"
  E0100 -> "undefined identifier"
  E0101 -> "ambiguous term reference"
  E0102 -> "undefined term reference"
  E0103 -> "duplicate principal name"
  E0104 -> "duplicate step label"
  E0105 -> "free variable has no source"
  E0106 -> "shadowing within a step"
  E0201 -> "action fact arity drift"
  E0202 -> "reveal references unhonest agent"
  E0203 -> "reveal rule has no !Ltk premise"
  E0204 -> "commit unreachable from any running"
  E0205 -> "secret claim references undefined term"
  E0206 -> "no executable lemma in verify block"
  E0207 -> "reserved name shadowed"
  E0208 -> "forward_secrecy without phase model or temporal anchor"
  E0209 -> "honest peer unreachable for agreement lemma"
  E0301 -> "injective_agreement: no joint initiator scope"
  E0302 -> "injective_agreement: no joint responder scope"
  E0303 -> "commit cannot be ordered after running"
  E0304 -> "secrecy: term never in any rule's scope"
  E0305 -> "unlinkability heuristic predicts non-termination"
  E0401 -> "open chain has no honest origin"
  E0402 -> "fresh value has both cleartext and wrapped envelopes"
  E0501 -> "channel arrow refers to undeclared :> channel"
  E0502 -> "feature not implemented in this Lower"
  W1001 -> "authentication() is aliveness only"
  W1002 -> "unlinkability proof may not terminate"
  W1003 -> "secret claim auto-placed"
  W1004 -> "auto-sources lemma over-generated"
  W1005 -> "auto-tagging fired on already-tagged step"
  W1006 -> "peer reachable only via honest registration"

--------------------------------------------------------------------------------
-- Pretty printing
--------------------------------------------------------------------------------

-- | Render a diagnostic in a rustc-style multi-line format.
renderError :: ClementineError -> Text
renderError e = T.unlines $
  [ header ] ++ posLine ++ details ++
  [ "  = help: run `clemc --explain " <> errorCodeText (errCode e) <> "` for the long form" ]
  where
    sev = case errorCodeSeverity (errCode e) of
            SevError   -> "error"
            SevWarning -> "warning"
    header =
      sev <> "[" <> errorCodeText (errCode e) <> "]: " <> errMsg e
    posLine = case errPos e of
      Nothing -> []
      Just sp ->
        [ "  --> " <> T.pack (spFile sp)
                   <> ":" <> T.pack (show (spLine sp))
                   <> ":" <> T.pack (show (spCol sp))
        ]
    details = map ("  | " <>) (errDetails e)

--------------------------------------------------------------------------------
-- --explain flag
--------------------------------------------------------------------------------

-- | The full markdown explanation for a code, or a stub message if
-- the explanation file has not been written yet. Used by
-- @clemc --explain E0023@.
explain :: ErrorCode -> Text
explain code = fromMaybe (stubExplanation code) (Map.lookup code explanations)

-- | Map from error code to embedded markdown body. Built once at
-- module load time from the files under @lib\/clementine\/explain\/@.
explanations :: Map ErrorCode Text
explanations = Map.fromList
  [ (code, body)
  | (path, bytes) <- explainFiles
  , let name = takeWhile (/= '.') path
  , Just code <- [parseCode name]
  , let body  = T.decodeUtf8 bytes
  ]

-- | All embedded explanation files. The 'embedDir' Template Haskell
-- splice walks @explain\/@ at compile time and produces a
-- @[(FilePath, ByteString)]@.
explainFiles :: [(FilePath, BS.ByteString)]
explainFiles = $(embedDir "explain")

-- | Convert @"E0023"@ to 'E0023'. We rely on derived 'Read'/'Show'
-- instances on 'ErrorCode' (the enum constructors are spelled exactly
-- the same as the file names).
parseCode :: String -> Maybe ErrorCode
parseCode s
  | s `elem` map show allErrorCodes = Just (read s)
  | otherwise                       = Nothing

-- | Default explanation body when an explanation file is missing.
stubExplanation :: ErrorCode -> Text
stubExplanation code = T.unlines
  [ "# " <> errorCodeText code <> ": " <> errorCodeShortDesc code
  , ""
  , "This error code is reserved but its long-form explanation has"
  , "not been written yet. Filing an issue with the .clem source that"
  , "triggered it would be appreciated."
  ]

-- | Render the explanations for every code in a single document.
-- Useful for generating reference docs.
explainAll :: Text
explainAll = T.intercalate "\n\n---\n\n" (map explain allErrorCodes)
