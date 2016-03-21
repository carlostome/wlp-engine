module Stmt where

import           Control.Monad.Writer         hiding ((<>))
import           Data.Map                     (Map)
import qualified Data.Map                     as M
import           Data.SBV                     (isTheorem)
import           Data.Stream                  (Stream)
import qualified Data.Stream                  as S
import Data.Maybe
import           System.IO.Unsafe
import           Text.PrettyPrint.ANSI.Leijen hiding (bool, int)

import           Expr
import           Var

-- | Statement type
data Stmt
  = Skip
  | Assert (Expr Bool)
  | Assume (Expr Bool)
  | AsgI  [Name] [Expr Integer]
  | AsgAI [(Name,Expr Integer)] [Expr Integer]
  | AsgPC [Expr Integer] Name [Expr Integer]
  | Seq Stmt Stmt
  | Choice Stmt Stmt
  | While (Expr Bool) (Expr Bool) Stmt
  | WhileKO Int (Expr Bool) Stmt
  | WhileKC Int (Expr Bool) Stmt
  | WhileF  (Expr Bool) Stmt
  | WhileFX Int (Expr Bool) Stmt
  | Scope [Var] Stmt


-- Smart constructors
skip   = Skip
assert = Assert
assume = Assume
asgi  = AsgI
asgai = AsgAI
while = While
whileKO = WhileKO
whileKC = WhileKC
whileF  = WhileF
whileFX = WhileFX
stmts :: [Stmt] -> Stmt
stmts  = foldr Seq Skip
vars vs = Scope vs . foldr Seq Skip
choice :: [Stmt] -> Stmt
choice = foldr1 Choice

-- | Weakest liberal precondition: wlp S q
--   Writer monad keeps track of p.o. for while loops.
wlp :: Stmt
     -> Expr Bool
     -> Either Doc (Expr Bool)
wlp stmt q =
  case stmt of
    Skip     -> return q
    Assert p -> return (p /\  q)
    Assume p -> return (p ==> q)
    AsgI vars exprs    -> return (subst2 (M.fromList $ zip vars exprs) q)
    AsgAI [(n,ix)] [expr] -> return (cond1 (splice (n,ix) expr q))
    Seq s1 s2       -> wlp s2 q >>= wlp s1
    Choice s1 s2    -> do
      w1 <- wlp s1 q
      w2 <- wlp s2 q
      return (w1 /\ w2)
    While inv cond s ->
      do wloop <- wlp s inv
         let i1 =  inv /\ neg cond  ==> q
             i2 =  inv /\ cond      ==> wloop
         if isTrue i1 && isTrue i2
          then return inv
          else Left (text "")
    Scope vs s ->
      do w <- wlp s q
         return (foralls vs w)

    -- Loop unrolling
    WhileKO 0 cond s -> return (neg cond ==> q)
    WhileKO n cond s -> do
      wk <- wlp (WhileKO (n-1) cond s) q >>= wlp s
      return $ (cond /\ wk) \/ (neg cond /\ q)

    WhileKC 0 cond s -> return (neg cond /\ q)
    WhileKC n cond s -> do
      wk <- wlp (WhileKC (n-1) cond s) q >>= wlp s
      return $ (cond /\ wk) \/ (neg cond /\ q)

    -- Fixpoint invariant
    WhileF cond s    -> calculateFix Nothing cond s q

    WhileFX n cond s -> calculateFix (Just n) cond s q

calculateFix :: Maybe Int -> Expr Bool -> Stmt -> Expr Bool -> Either Doc (Expr Bool)
calculateFix stop cond s q =
  go stop (pair $ S.iterate (\w0 -> let Right w1 = wlp s w0 in  (cond /\ w1) \/ (neg cond /\ q))(l True))
  where
     go :: Maybe Int -> Stream (Expr Bool,Expr Bool) -> Either Doc (Expr Bool)
     go (Just 0) _ = Left . text $ ("Exhausted " ++ (show $ fromJust stop) ++ " iterations looking for an invariant.")
     go n stream   =
          let (w0,w1)  = S.head stream
          in if isTrue ((w0 ==> w1) /\ (w1 ==> w0))
                then return w0
                else go (fmap (\x -> x-1) n) (S.tail stream)

pair :: Stream a -> Stream (a,a)
pair (S.Cons a (S.Cons b s)) = (a,b) S.<:> pair (S.Cons b s)

isTrue :: Expr Bool -> Bool
isTrue = fromMaybe False . unsafePerformIO . isTheorem Nothing . interpret' . boundVars

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance Pretty Stmt where
  pretty stmt =
    case stmt of
      Skip     -> text "skip"
      Assert e -> hsep [green $ text "assert", pretty e]
      Assume e -> hsep [magenta $ text "assume", pretty e]
      AsgI n e -> hsep [ hcat $ punctuate (comma <> space) (map text n)
                       , text ":="
                       , hcat $ punctuate (comma <> space) (map pretty e)]
      AsgAI ni e -> hsep [ hcat $ punctuate (comma <> space) (map (\(n,ix) -> text n <> brackets (pretty ix)) ni)
                        , text ":="
                        , hcat $ punctuate (comma <> space) (map pretty e)]
      Seq  s1 s2   -> vcat $ punctuate (semi <> space) [pretty s1, pretty s2]
      Choice s1 s2 -> hcat [pretty s1, text "[]", pretty s2]
      While  i c s -> vcat [ hsep [yellow $ text "inv", pretty i, yellow $ text "while", pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      WhileKO i c s -> vcat [ hsep [(yellow $ text "while") <> angles (red $ pretty i) , pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      WhileKC i c s -> vcat [ hsep [(yellow $ text "while") <> brackets (red $ pretty i) , pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      WhileF c s   -> vcat [ hsep [(yellow $ text "while") , pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      WhileFX _ c s   -> vcat [ hsep [(yellow $ text "while") , pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      Scope vs s   -> vcat [hsep [text "vars", hsep $ punctuate comma (map pretty vs), text "in"]
                           , indent 2 (pretty s)
                           ,text "end"]
