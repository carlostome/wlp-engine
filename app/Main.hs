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
  let (p,po) = wlp stmt (l True)
  unless (null $ po) (putStrLn "\n\nProof obligations of while loops:")
  forM_ po $ \obl -> do
    result <- prove (interpret' obl)
    displayIO stdout (renderPretty 0.1 80 (pretty obl))
    putStrLn "\n"
    print result
  prove (interpret' p ) >>= print

main :: IO ()
main = mapM_ verify
  [ swap1
  , swap2
  , d1
  , d2 ]
