module WLP (
  verifyStmt,
  verifyProg,
  module Stmt,
  pprint
  ) where

--
import Text.PrettyPrint.ANSI.Leijen hiding (int, bool)
import System.IO (stdout)

import Stmt

-- | Main entry point of wlp-engine.
--   If any of the proof obligations generated in a while loop
--   invariant fails then verify fails.
verifyStmt :: Stmt -> IO ()
verifyStmt stmt = do
  putStrLn "Verifying the following program: \n"
  displayIO stdout (renderPretty 0.1 80 (pretty stmt))
  putStrLn ""
  let w = wlp stmt (lb True)
  case w of
    Left err   -> do
      putStrLn "Error:"
      pprint err
    Right expr -> do
      pprint expr
      putStrLn ""
      pprint $ prove expr
      putStrLn ""

verifyProg :: [Prog] -> Prog -> IO ()
verifyProg env prog' = do
  putStrLn "Verifying the following program: \n"
  displayIO stdout (renderPretty 0.1 80 (pretty prog'))
  putStrLn ""
  let w = wlpProg env prog' (lb True)
  case w of
    Left err   -> do
      putStrLn "Error:"
      pprint err
    Right expr -> do
      pprint expr
      putStrLn ""
      pprint $ prove expr
      putStrLn ""


pprint :: Pretty a => a -> IO ()
pprint p = do
  displayIO stdout (renderPretty 0.1 80 (pretty p))
  putStrLn ""
