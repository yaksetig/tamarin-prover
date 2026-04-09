-- |
-- Test harness for Clementine.
--
-- Two corpora:
--
--   * 'positiveFixtures' — well-formed @.clem@ files that should
--     parse, pass wellformedness, and lower to a non-empty summary.
--
--   * 'negativeFixtures' — malformed @.clem@ files paired with the
--     specific error code they should trigger. Failure mode: the
--     compile succeeds when it should fail, OR the compile fails
--     with a different error code than expected.
--
-- Run from the package root:
--
--     cabal test
--
module Main (main) where

import           Control.Monad (forM_, unless)
import           System.Exit   (exitFailure, exitSuccess)
import           System.IO     (hPutStrLn, stderr)

import           Clementine

--------------------------------------------------------------------------------
-- Positive fixtures: should parse + lower cleanly
--------------------------------------------------------------------------------

positiveFixtures :: [FilePath]
positiveFixtures =
  [ "test/Fixtures/hello.clem"
  , "test/Fixtures/iso_dh.clem"
  , "test/Fixtures/nsl.clem"
  ]

--------------------------------------------------------------------------------
-- Negative fixtures: each one should fail compilation with a
-- specific error code from Clementine.Errors.
--------------------------------------------------------------------------------

negativeFixtures :: [(FilePath, ErrorCode)]
negativeFixtures =
  [ ("test/Fixtures/errors/missing_executable.clem",  E0206)
  , ("test/Fixtures/errors/duplicate_principal.clem", E0103)
  , ("test/Fixtures/errors/duplicate_step.clem",      E0104)
  , ("test/Fixtures/errors/undefined_term_ref.clem",  E0102)
  , ("test/Fixtures/errors/undeclared_role.clem",     E0209)
  , ("test/Fixtures/errors/secret_undefined.clem",    E0205)
  ]

--------------------------------------------------------------------------------

main :: IO ()
main = do
  positiveResults <- mapM runPositive positiveFixtures
  negativeResults <- mapM runNegative negativeFixtures

  let posFails = [f | (f, False) <- zip positiveFixtures positiveResults]
      negFails = [f | ((f, _), False) <- zip negativeFixtures negativeResults]
      allFails = posFails ++ negFails

  if null allFails
    then do
      putStrLn $ "ok: " ++ show (length positiveFixtures)
                         ++ " positive + "
                         ++ show (length negativeFixtures)
                         ++ " negative fixture(s) passed"
      exitSuccess
    else do
      hPutStrLn stderr $ "failures: " ++ show allFails
      exitFailure

--------------------------------------------------------------------------------

runPositive :: FilePath -> IO Bool
runPositive fp = do
  putStrLn $ "==> " ++ fp
  result <- compileFile fp
  case result of
    Left err -> do
      hPutStrLn stderr "  expected success but compilation failed:"
      mapM_ (hPutStrLn stderr . ("    " ++)) (lines (show err))
      pure False
    Right ct -> do
      let nRoles  = length (ctRoles  ct)
          nSteps  = length (ctSteps  ct)
          nLemmas = length (ctLemmas ct)
      putStrLn $ "  ok: " ++ show nRoles  ++ " role(s), "
                          ++ show nSteps  ++ " step(s), "
                          ++ show nLemmas ++ " lemma(s)"
      let nonEmpty = nRoles > 0 && nSteps > 0 && nLemmas > 0
      unless nonEmpty $ hPutStrLn stderr "  warning: empty summary"
      pure nonEmpty

runNegative :: (FilePath, ErrorCode) -> IO Bool
runNegative (fp, expected) = do
  putStrLn $ "==> " ++ fp ++ "  (expecting " ++ show expected ++ ")"
  result <- compileFile fp
  case result of
    Right _ -> do
      hPutStrLn stderr $
        "  expected failure with " ++ show expected
        ++ " but compilation SUCCEEDED"
      pure False
    Left err
      | errCode err == expected -> do
          putStrLn $ "  ok: failed with " ++ show expected
          pure True
      | otherwise -> do
          hPutStrLn stderr $
            "  expected " ++ show expected
            ++ " but got " ++ show (errCode err)
          pure False
