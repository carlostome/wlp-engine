{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Stmt (
  -- * Stmt
  Stmt,
  -- ** Smart constructors
  skip, assert, assume, asg,
  while, whileKO, whileKC, whileF, whileFX,
  stmts, choice, ifS, var,
  pcall,

  -- * Program definition
  Prog,
  -- ** Smart constructors
  spec, prog,

  -- * WLP
  wlp, wlpProg,

  module Expr
  ) where

import           Control.Monad                (liftM2)
import           Data.Map                     (Map)
import qualified Data.Map                     as M
import           Data.Maybe                   (catMaybes, fromJust)
import           Data.Stream                  (Stream)
import qualified Data.Stream                  as S
import           Text.PrettyPrint.ANSI.Leijen hiding (bool, int)

import           Expr

-- | Statement type
data Stmt
  = Skip
  | Assert (Expr BOOL)
  | Assume (Expr BOOL)
  | Asg [Asg]
  | PCall [UTarget] Name [UExpr] 
  | Seq Stmt Stmt
  | Choice Stmt Stmt
  | While (Expr BOOL) (Expr BOOL) Stmt
  | WhileKO Int (Expr BOOL) Stmt
  | WhileKC Int (Expr BOOL) Stmt
  | WhileF  (Expr BOOL) Stmt
  | WhileFX Int (Expr BOOL) Stmt
  | Scope UVar Stmt

-- Smart constructors
skip   = Skip
assert = Assert
assume = Assume
asg    = Asg
while = While
whileKO = WhileKO
whileKC = WhileKC
whileF  = WhileF
whileFX = WhileFX
stmts :: [Stmt] -> Stmt
stmts  = foldr Seq Skip
choice :: [Stmt] -> Stmt
choice = foldr1 Choice
var v' = Scope (u v')
pcall = PCall
ifS c s1 s2 = Choice (Seq (Assume c) s1) (Seq (Assume (neg c)) s2)


-- | Weakest liberal precondition: wlp S q
wlp :: Stmt
    -> Expr BOOL
    -> Either Doc (Expr BOOL)
wlp stmt q =
  case stmt of
    Skip     -> return q
    Assert p -> return (p /\  q)
    Assume p -> return (p ==> q)
    Asg asglist -> return (subst asglist q)
    Seq s1 s2   -> wlp  s2 q >>= wlp s1
    Choice s1 s2 -> do
      w1 <- wlp s1 q
      w2 <- wlp s2 q
      return (w1 /\ w2)
    w@(While inv cond s) ->
      do wloop <- wlp s inv
         let i1 =  (inv /\ neg cond)  ==> q
             i2 =  (inv /\ cond)      ==> wloop
         case prove i1 of
           NotValid err -> Left (vsep [ text "While checking that (I /\\ ~C ==> Q) in the loop:"
                                      , hang 2 (pretty w)
                                      , hsep [text "Cannot prove:", pretty i1], hang 2 err])
           Valid        ->
            case prove i2 of
              NotValid err -> Left (vsep [ text "While checking that (inv /\\ cond ==> wlp s inv) in the loop:"
                                         , hang 2 (pretty w)
                                         , hsep [text "Cannot prove:", pretty i2], hang 2 err])
              Valid -> return inv

    Scope (UV _ v') s ->
      do w' <- wlp s q
         return (forall v' w')

    -- Loop unrolling
    WhileKO 0 cond _ -> return (neg cond ==> q)
    WhileKO n cond s -> do
      wk <- wlp (WhileKO (n-1) cond s) q >>= wlp s
      return $ (cond /\ wk) \/ (neg cond /\ q)

    WhileKC 0 cond _ -> return (neg cond /\ q)
    WhileKC n cond s -> do
      wk <- wlp (WhileKC (n-1) cond s) q >>= wlp s
      return $ (cond /\ wk) \/ (neg cond /\ q)

    -- Fixpoint invariant
    WhileF cond s    -> calculateFix Nothing cond s q

    WhileFX n cond s -> calculateFix (Just n) cond s q

    -- Program Call
    PCall _ _ _ -> Left . text $ "Program calls should be transformed before wlp"


--------------------------------------------------------------------------------
-- Fix point iteration
--------------------------------------------------------------------------------

-- | Calculate the fix point for the loop given
--  its condition and the body.
calculateFix :: Maybe Int                -- ^ Maximun number of iterations
             -> Expr BOOL                -- ^ Condition
             -> Stmt                     -- ^ Stmt
             -> Expr BOOL                -- ^ Postcondition
             -> Either Doc (Expr BOOL)
calculateFix stop cond s q =
  go stop (pair $ S.iterate (\w0 -> let Right w1 = wlp s w0 in  (cond /\ w1) \/ (neg cond /\ q))(lb True))
  where
     go :: Maybe Int -> Stream (Expr BOOL,Expr BOOL) -> Either Doc (Expr BOOL)
     go (Just 0) _ = Left . text $ ("Exhausted " ++ (show $ fromJust stop)
                                    ++ " iterations looking for an invariant.")
     go n stream   =
          let (w0,w1)  = S.head stream
          in if proveBool (w0 <==> w1)
                then return w0
                else go (fmap (\x -> x-1) n) (S.tail stream)

pair :: Stream a -> Stream (a,a)
pair (S.Cons a (S.Cons b' s)) = (a,b') S.<:> pair (S.Cons b' s)

--------------------------------------------------------------------------------
-- Program Call transformation
--------------------------------------------------------------------------------

-- | Type of programs
data Prog = Prog Name [UVar] [UVar] Stmt

-- | Construct a program given its specification
-- in terms of pre and post conditions.
spec :: Name -> [UVar] -> [UVar] -> Expr BOOL -> Expr BOOL -> Prog
spec name inpvars outvars pre post = Prog name inpvars outvars (stmts [assert pre, assume post])

-- | Construct a program given its body.
prog :: Name -> [UVar] -> [UVar] -> Stmt -> Prog
prog = Prog

-- | WLP of a program given an environment and a postcondition.
wlpProg env p q = simplProg env p >>= flip wlp q

simplProg :: [Prog] -> Prog -> Either Doc Stmt
simplProg env (Prog _ inp out s) = do
  ts <- inline (mkEnv env) s
  return (foldr Scope ts (inp ++ out))

-- | Transform a stmt with program calls inlining
-- the other program calls.
inline :: Map Name Prog -> Stmt -> Either Doc Stmt
inline m (PCall tgts name args) =
  case M.lookup name m of
    Nothing -> Left $ hsep [text "Program", text name, text "not defined in environment."]
    (Just (Prog _ inpvars retvars sm)) ->
      let inputs  = catMaybes $ zipWith mixexp inpvars args
          returns = catMaybes $ zipWith mixtarg tgts retvars
      in return (foldr Scope (stmts [asg inputs, sm, asg returns]) (inpvars ++ retvars))
inline _ Skip = return Skip
inline _ s@(Assert _) = return s
inline _ s@(Assume _) = return s
inline _ s@(Asg _) = return s
inline m (Seq s1 s2)    = liftM2 Seq (inline m s1) (inline m s2)
inline m (Choice s1 s2) = liftM2 Choice (inline m s1) (inline m s2)
inline m (While i' c s) = fmap (While i' c) (inline m s)
inline m (WhileKO n c s) = fmap (WhileKO n c) (inline m s)
inline m (WhileKC n c s) = fmap (WhileKC n c) (inline m s)
inline m (WhileF c s)    = fmap (WhileF c) (inline m s)
inline m (WhileFX i' c s) = fmap (WhileFX i' c) (inline m s)
inline m (Scope v' s)     = fmap (Scope v') (inline m s)

mkEnv :: [Prog] -> Map Name Prog
mkEnv = M.fromList . map (\p@(Prog n _ _ _) -> (n, p))

--------------------------------------------------------------------------------
-- Pretty printing and Show instances
--------------------------------------------------------------------------------

instance Pretty Stmt where
  pretty stmt =
    case stmt of
      Skip     -> text "skip"
      Assert e -> hsep [green $ text "assert", text $ show e]
      Assume e -> hsep [magenta $ text "assume", text $ show e]
      Asg n    -> hcat $ punctuate (comma <> space) (map pretty n)
      Seq  s1 s2   -> vcat $ punctuate (semi <> space) [pretty s1, pretty s2]
      Choice s1 s2 -> hsep [braces $ pretty s1, text "[]", braces $ pretty s2]
      While  n c s ->
        vcat [ hsep [yellow $ text "inv", pretty n, yellow $ text "while"
                    , pretty c, yellow $ text "do"]
             , indent 2 (braces $ pretty s)]
      WhileKO n c s ->
        vcat [ hsep [(yellow $ text "while") <> angles (red $ pretty n)
                    , pretty c, yellow $ text "do"]
             , indent 2 (braces $ pretty s)]
      WhileKC n c s ->
        vcat [ hsep [(yellow $ text "while") <> brackets (red $ pretty n)
                    , pretty c, yellow $ text "do"]
             , indent 2 (braces $ pretty s)]
      WhileF c s   -> vcat [ hsep [(yellow $ text "while") , pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      WhileFX _ c s   -> vcat [ hsep [(yellow $ text "while") , pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      Scope (UV _ v') s  -> vcat [hsep [text "var", pretty v', text "in"]
                                       , indent 2 (pretty s)
                                       ,text "end"]
      PCall tgts name expr ->
        hsep [hsep (punctuate comma (map pretty tgts))
             , text ":=", pretty name
             , parens (hsep $ punctuate comma (map pretty expr))]

instance Pretty Prog where
  pretty (Prog n inp out s) =
    vcat [pretty n <> parens (hsep (punctuate comma (map pretty inp))
                           <> char '|' <>
                           hsep (punctuate comma (map pretty out))) <+> char '='
         , indent 2 (pretty s)]

