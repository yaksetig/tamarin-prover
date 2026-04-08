-- |
-- v0.0 test harness for Clementine.
--
-- This is the smallest possible smoke test: it parses every .clem file
-- under test/Fixtures/ and asserts that lowering produces a non-empty
-- summary. It does NOT yet run tamarin-prover on the result — that
-- arrives in the next iteration alongside the Sapic-process lowering.
--
-- Run from the package root:
--
-- > cabal test
--
-- or via stack:
--
-- > stack test tamarin-prover-clementine
module Main (main) where

import           Control.Monad (forM_, unless)
import           System.Exit   (exitFailure, exitSuccess)
import           System.IO     (hPutStrLn, stderr)

import           Clementine

-- The fixture corpus. Add new entries here as features land.
fixtures :: [FilePath]
fixtures =
  [ "test/Fixtures/iso_dh.clem"
  , "test/Fixtures/nsl.clem"
  ]

main :: IO ()
main = do
  results <- mapM runFixture fixtures
  let failures = [f | (f, False) <- zip fixtures results]
  if null failures
    then do
      putStrLn $ "ok: parsed and lowered " ++ show (length fixtures) ++ " fixture(s)"
      exitSuccess
    else do
      hPutStrLn stderr $ "failures: " ++ show failures
      exitFailure

runFixture :: FilePath -> IO Bool
runFixture fp = do
  putStrLn $ "==> " ++ fp
  result <- compileFile fp
  case result of
    Left err -> do
      hPutStrLn stderr $ "  parse/lower failed:"
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
