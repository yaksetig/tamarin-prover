{-# LANGUAGE CPP #-}
-- |
-- Module      : Clementine
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- Top-level entry point for the Clementine high-level frontend.
--
-- == Pipeline
--
-- @
-- .clem file
--    │
--    │ Clementine.Parser.parseProtocolFile
--    ▼
-- Clementine.AST.Protocol
--    │
--    ├── Clementine.Lower.lowerProtocol     ──► CompiledTheory  (default build)
--    │                                          (always available; used by the
--    │                                           source map and the test harness)
--    │
--    └── Clementine.LowerSapic.lowerProtocolSapicText
--                                            ──► .spthy text   (--flag with-sapic)
--                                                (only when the with-sapic cabal
--                                                 flag is on, then the clemc
--                                                 binary writes the .spthy file
--                                                 alongside the source map)
-- @
--
-- The two paths run independently. Adding the Sapic wiring did not
-- change the @CompiledTheory@ path, so the v0.0 default build keeps
-- working unchanged.
module Clementine
  ( -- * High-level driver
    compileFile
  , compileText
  , CompileResult
    -- * Sapic-backed compilation (gated on --flag with-sapic)
  , compileFileToSpthy
  , withSapic
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

#ifdef WITH_SAPIC
import           Control.Exception     (SomeException, try)
import qualified Clementine.LowerSapic as LowerSapic
#endif

-- | The result of compiling a .clem source. The default 'Lower' pass
-- never emits errors of its own; everything that fails fails at
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

-- | Whether this build of Clementine has the Sapic-backed lowering
-- compiled in. The @clemc@ driver uses this to decide whether to
-- emit a @.spthy@ file alongside the source map.
withSapic :: Bool
#ifdef WITH_SAPIC
withSapic = True
#else
withSapic = False
#endif

-- | Parse a .clem file and produce the rendered @.spthy@ text via
-- 'Clementine.LowerSapic'. Returns 'Left' wrapping any parse error
-- or any exception thrown by the Sapic translation pipeline.
--
-- When this build does NOT have the @with-sapic@ flag, this function
-- returns 'Left' with code 'E0502' ("feature not implemented in this
-- Lower"). That keeps the type signature stable across both build
-- configurations so the @clemc@ driver can call it unconditionally.
compileFileToSpthy :: FilePath -> IO (Either ClementineError String)
#ifdef WITH_SAPIC
compileFileToSpthy fp = do
  parsed <- Parser.parseProtocolFile fp
  case parsed of
    Left pe   -> pure (Left (parseErrorToClementine pe))
    Right ast -> do
      result <- try (LowerSapic.lowerProtocolSapicText ast)
                  :: IO (Either SomeException String)
      pure $ case result of
        Right spthy -> Right spthy
        Left  exc   -> Left ClementineError
          { errCode    = E0502
          , errPos     = Just (protoPos ast)
          , errMsg     = "Sapic lowering failed"
          , errDetails = T.lines (T.pack (show exc))
          }
#else
compileFileToSpthy _ = pure $ Left ClementineError
  { errCode    = E0502
  , errPos     = Nothing
  , errMsg     = "this clemc was built without --flag with-sapic"
  , errDetails =
      [ "rebuild with `cabal build clemc --flag with-sapic` to enable .spthy output"
      ]
  }
#endif

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
