module Main where

--
import Text.PrettyPrint.ANSI.Leijen hiding (int, bool)
import System.IO (stdout)
import Control.Monad (unless, forM_,)
import Data.SBV (prove)

import Stmt
import Expr
import Example

-- | Main entry point of wlp-engine.
--   If any of the proof obligations generated in a while loop
--   invariant fails then verify fails.
verify :: Stmt -> IO ()
verify stmt = do
  putStrLn "Verifying the following program: \n"
  displayIO stdout (renderPretty 0.1 80 (pretty stmt))
  let w = wlp stmt (l True)
  case w of
    Left err   ->
      displayIO stdout (renderPretty 0.1 80 (pretty err))
    Right expr -> do
      putStrLn ""
      prove (interpret' expr ) >>= print

main :: IO ()
main = mapM_ verify
  [ swap1
  , swap2
  , d1
  , d2 ]

pprint :: Pretty a => a -> IO ()
pprint p =
  displayIO stdout (renderPretty 0.1 80 (pretty p))
