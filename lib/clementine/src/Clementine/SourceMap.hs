-- |
-- Module      : Clementine.SourceMap
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- Source map sidecar emitter.
--
-- When @clemc@ writes @out.spthy@, it also writes
-- @out.spthy.sourcemap.json@ — a structured map from generated rule
-- and lemma names back to the @.clem@ source location they came from.
--
-- Consumers (an IDE plugin, the Tamarin web UI, or a CI tool that
-- annotates failed proofs) can read this without having to re-parse
-- the @.clem@ file.
--
-- The format is intentionally minimal and hand-rolled (no aeson
-- dependency) so the v0.0 scaffold has zero non-portable deps. The
-- shape matches the design from item 4 of the design conversation.
module Clementine.SourceMap
  ( SourceMap(..)
  , buildSourceMap
  , renderSourceMap
  , writeSourceMap
  ) where

import           Data.Text          (Text)
import qualified Data.Text          as T
import qualified Data.Text.IO       as T

import           Clementine.AST     (SrcPos(..))
import           Clementine.Lower

-- | A source map for one compiled .clem file.
data SourceMap = SourceMap
  { smSourceFile :: !FilePath
  , smRules      :: ![SourceMapEntry]
  , smLemmas     :: ![SourceMapEntry]
  } deriving (Show)

-- | One entry in the source map: a generated artifact name plus its
-- origin information.
data SourceMapEntry = SourceMapEntry
  { smeName   :: !Text
  , smeOrigin :: !Origin
  } deriving (Show)

-- | Build a source map from a compiled theory. Currently we expose
-- one entry per role and one per lemma; once 'Clementine.Lower'
-- generates real Sapic processes, we will also expose entries for
-- generated MSR rules.
buildSourceMap :: FilePath -> CompiledTheory -> SourceMap
buildSourceMap srcFile ct = SourceMap
  { smSourceFile = srcFile
  , smRules      = [ SourceMapEntry (rsName r) (rsOrigin r) | r <- ctRoles ct ]
                ++ [ SourceMapEntry (ssLabel s) (ssOrigin s) | s <- ctSteps ct ]
  , smLemmas     = [ SourceMapEntry (lsName l) (lsOrigin l) | l <- ctLemmas ct ]
  }

--------------------------------------------------------------------------------
-- JSON rendering (hand-rolled; no aeson dependency)
--------------------------------------------------------------------------------

-- | Render a source map as JSON. Stable, deterministic ordering.
renderSourceMap :: SourceMap -> Text
renderSourceMap sm = T.unlines $
  [ "{"
  , "  \"version\": 1,"
  , "  \"source\": " <> jstr (T.pack (smSourceFile sm)) <> ","
  , "  \"rules\": ["
  ] ++
  commaList (map renderEntry (smRules sm)) ++
  [ "  ],"
  , "  \"lemmas\": ["
  ] ++
  commaList (map renderEntry (smLemmas sm)) ++
  [ "  ]"
  , "}"
  ]
  where
    renderEntry e = T.concat
      [ "    { \"name\": "  , jstr (smeName e)
      , ", \"kind\": "       , jstr (origKind (smeOrigin e))
      , ", \"file\": "       , jstr (T.pack (spFile (origPos (smeOrigin e))))
      , ", \"line\": "       , T.pack (show (spLine (origPos (smeOrigin e))))
      , ", \"col\": "        , T.pack (show (spCol  (origPos (smeOrigin e))))
      , " }"
      ]

-- | Append commas to all but the last element of a JSON array body.
commaList :: [Text] -> [Text]
commaList []     = []
commaList [x]    = [x]
commaList (x:xs) = (x <> ",") : commaList xs

-- | Render a JSON string literal. We escape only what is strictly
-- necessary for the values we emit (file paths, identifier strings,
-- short kind labels). No control characters expected.
jstr :: Text -> Text
jstr t = "\"" <> T.concatMap escape t <> "\""
  where
    escape '"'  = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\r' = "\\r"
    escape '\t' = "\\t"
    escape c    = T.singleton c

-- | Convenience: write a source map to disk at @basePath ++ \".sourcemap.json\"@.
writeSourceMap :: FilePath -> SourceMap -> IO ()
writeSourceMap basePath sm =
  T.writeFile (basePath <> ".sourcemap.json") (renderSourceMap sm)
