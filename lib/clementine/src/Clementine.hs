-- |
-- Module      : Clementine
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- Top-level entry point for the Clementine high-level frontend.
--
-- == Pipeline (v0.0)
--
-- @
-- .clem file
--    │
--    │ Clementine.Parser.parseProtocolFile
--    ▼
-- Clementine.AST.Protocol
--    │
--    │ Clementine.Lower.lowerProtocol  -- stub: produces a CompiledTheory summary
--    ▼
-- Clementine.Lower.CompiledTheory
-- @
--
-- The next milestone replaces 'CompiledTheory' with 'Theory.OpenTheory'
-- and routes through 'Sapic.translate'. Everything in this module's
-- public surface is shaped to make that swap a one-line change.
module Clementine
  ( -- * High-level driver
    compileFile
  , compileText
  , CompileResult
    -- * Re-exports
  , module Clementine.AST
  , module Clementine.Lower
  , module Clementine.Errors
  ) where

import           Data.Text (Text)
import qualified Data.Text as T

import           Clementine.AST
import           Clementine.Errors
import           Clementine.Lower
import qualified Clementine.Parser as Parser

-- | The result of compiling a .clem source. The Lower stub never
-- emits errors of its own in v0.0; everything that fails fails at
-- parse time.
type CompileResult = Either ClementineError CompiledTheory

-- | Parse and lower a .clem file from disk.
compileFile :: FilePath -> IO CompileResult
compileFile fp = do
  parsed <- Parser.parseProtocolFile fp
  pure $ case parsed of
    Left pe   -> Left (parseErrorToClementine pe)
    Right ast -> Right (lowerProtocol ast)

-- | Parse and lower a .clem source given as 'Text'.
compileText :: FilePath -> Text -> CompileResult
compileText fp src = case Parser.parseProtocol fp src of
  Left pe   -> Left (parseErrorToClementine pe)
  Right ast -> Right (lowerProtocol ast)

-- | Convert a parser error into the Clementine error type. We do not
-- yet extract the source position from parsec; that is queued for the
-- next iteration alongside the source-map work.
parseErrorToClementine :: Parser.ParseError -> ClementineError
parseErrorToClementine pe = ClementineError
  { errCode    = E0001
  , errPos     = Nothing
  , errMsg     = "parse error"
  , errDetails = T.lines (T.pack (show pe))
  }
