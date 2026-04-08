-- |
-- The @clemc@ command-line driver for the Clementine high-level
-- frontend.
--
-- == Usage
--
-- @
-- clemc <file.clem>           parse and lower the given file
-- clemc --explain <CODE>      print the long-form explanation for a code
-- clemc --explain-all         print every error code's explanation
-- clemc --list-codes          print every error code with its short
--                             description (one per line)
-- clemc --help                this message
-- @
--
-- The @clemc <file.clem>@ form additionally writes a JSON source map
-- sidecar at @<file.clem>.sourcemap.json@ next to the input.
module Main (main) where

import           Control.Monad      (forM_)
import qualified Data.Text          as T
import qualified Data.Text.IO       as T
import           System.Environment (getArgs)
import           System.Exit        (exitFailure, exitSuccess, exitWith,
                                     ExitCode(..))
import           System.IO          (hPutStrLn, stderr)

import           Clementine
import           Clementine.SourceMap

main :: IO ()
main = do
  args <- getArgs
  case args of
    []                      -> usage >> exitWith (ExitFailure 2)
    ["--help"]              -> usage >> exitSuccess
    ["-h"]                  -> usage >> exitSuccess
    ["--list-codes"]        -> listCodes
    ["--explain-all"]       -> T.putStr explainAll >> exitSuccess
    ["--explain", codeStr]  -> runExplain codeStr
    ["--explain"]           -> usage >> exitWith (ExitFailure 2)
    [path]                  -> runCompile path
    (path : _ : _)          -> hPutStrLn stderr "clemc: extra arguments ignored"
                            >> runCompile path

usage :: IO ()
usage = mapM_ (hPutStrLn stderr)
  [ "clemc — Clementine high-level frontend for Tamarin"
  , ""
  , "Usage:"
  , "  clemc <file.clem>          parse and lower the given file"
  , "  clemc --explain <CODE>     print the long-form explanation"
  , "  clemc --explain-all        print every code's explanation"
  , "  clemc --list-codes         list error/warning codes"
  , "  clemc --help               this message"
  ]

-- | @clemc <path>@: parse, lower, write the source map.
runCompile :: FilePath -> IO ()
runCompile path = do
  result <- compileFile path
  case result of
    Left err -> do
      T.hPutStr stderr (renderError err)
      exitFailure
    Right ct -> do
      let nRoles  = length (ctRoles  ct)
          nSteps  = length (ctSteps  ct)
          nLemmas = length (ctLemmas ct)
      putStrLn $ "compiled " ++ path
      putStrLn $ "  " ++ show nRoles  ++ " role(s)"
      putStrLn $ "  " ++ show nSteps  ++ " step(s)"
      putStrLn $ "  " ++ show nLemmas ++ " lemma(s)"
      let sm = buildSourceMap path ct
      writeSourceMap path sm
      putStrLn $ "  source map: " ++ path ++ ".sourcemap.json"
      exitSuccess

-- | @clemc --explain CODE@: look up the long-form explanation.
runExplain :: String -> IO ()
runExplain codeStr =
  case lookupCode codeStr of
    Nothing -> do
      hPutStrLn stderr $ "clemc: unknown error code " ++ show codeStr
      hPutStrLn stderr   "       run `clemc --list-codes` to see all of them"
      exitWith (ExitFailure 2)
    Just c  -> do
      T.putStr (explain c)
      exitSuccess

-- | @clemc --list-codes@: print every code, one per line.
listCodes :: IO ()
listCodes = do
  forM_ allErrorCodes $ \c ->
    T.putStrLn $ errorCodeText c <> "  " <> errorCodeShortDesc c
  exitSuccess

-- | Look up an error code by its textual form (e.g. @"E0101"@).
lookupCode :: String -> Maybe ErrorCode
lookupCode s =
  case filter (\c -> T.unpack (errorCodeText c) == s) allErrorCodes of
    (c : _) -> Just c
    []      -> Nothing
