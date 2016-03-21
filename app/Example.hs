module Example where

import Stmt
import Var
import Expr

{-- | Swap two variables using tmp
var x:int, y:int, a:int, b:int in
  assume (x = a /\ y = b);
  var tmp:int in
    tmp := x;
    x := y;
    y := tmp:
  end;
  assert (x = b /\ y = a);
end
-}
swap1 :: Stmt
swap1 = vars ["x" ::: int, "y" ::: int, "b" ::: int,  "a" ::: int]
          [assume ((vi "x" ==. vi "a") /\ (vi "y" ==. vi "b"))
          ,vars ["tmp" ::: int]
            [ asgi ["tmp"] [vi "x"]
            , asgi ["x"]   [vi "y"]
            , asgi ["y"]   [vi "tmp"]]
          ,assert ((vi "x" ==. vi "b") /\ (vi "y" ==. vi "a"))]

{-- | Swap two variables (no aux var)
var x:int, y:int, a:int, b:int in
  assume (x = a /\ y = b);
  x := x + y;
  y := x - y;
  x := x - y:
  end;
  assert (x = b /\ y = a);
end
-}
swap2 :: Stmt
swap2 = vars ["x" ::: int, "y" ::: int, "b" ::: int,  "a" ::: int]
          [ assume ((vi "x" ==. vi "a") /\ (vi "y" ==. vi "b"))
          , asgi ["x"]   [vi "x" +. vi "y"]
          , asgi ["y"]   [vi "x" -. vi "y"]
          , asgi ["x"]   [vi "x" -. vi "y"]
          , assert ((vi "x" ==. vi "b") /\ (vi "y" ==. vi "a"))]

{-- | Swap two array elements
var a:[int], j:int, i:int, x:int, y:int in
  assume (a[i] = x /\ a[j] = y) ;
  var tmp in
    tmp  := a[i];
    a[i] := a[j];
    a[j] := tmp:
  end
  assert (a[i] = y /\ a[j] = x);
end
-}
swaparr :: Stmt
swaparr = vars ["a" ::: intarr, "i" ::: int, "j" ::: int, "x" ::: int, "y" ::: int]
      [ assume ((("a" `ati` vi "i") ==. vi "x") /\ (("a" `ati` vi "j") ==. vi "y"))
      , vars ["tmp" ::: int]
          [ asgi  ["tmp"] ["a" `ati` vi "i"]
          , asgai [("a", vi "i")] ["a" `ati` vi "j"]
          , asgai [("a", vi "j")] [vi "tmp"]]
      , assert ((("a" `ati` vi "i") ==. vi "y") /\ (("a" `ati` vi "j") ==. vi "x"))]

{-- | Example D1
var x:int, y:iny in
  assume 0<x ;
  inv 0<=x while 0<x { x := x-1 } ;
  y := x ;
  assert y=0;
end
-}
d1 :: Stmt
d1 = vars ["x" ::: int, "y" ::: int]
      [ assume (l 0 <. vi "x")
      , while  (l 0 <=. vi "x")
               (l 0 <. vi"x")
               (asgi ["x"] [vi "x" -. l 1])
      , asgi ["y"] [vi "x"]
      , assert (vi "y" ==. l 0)]

{-- | Example D2
var x:int, y:iny in
  assume 2<=x ;
  inv 0<=x while 0<x { x := x-2 } ;
  y := x ;
  assert y=0 ;
end
-}
d2 :: Stmt
d2 = vars ["x" ::: int, "y" ::: int]
      [ assume (l 2 <=. vi "x")
      , while  (l 0 <=. vi "x")
               (l 0 <. vi"x")
               (asgi ["x"] [vi "x" -. l 2])
      , asgi ["y"] [vi "x"]
      , assert (vi "y" ==. l 0)]

{-- | minind
var a:[int], i:int, N:int, i0:int in
  assume (i < N, i = i0)
  var min in
    r := a[i];
    min := i;
    inv (i <= N /\ forall j : i0 <= j < i : a[r] <= a[j]) while i<N do
      {assume (a[i] < min); min := a[i]; r := i;} [] {assume (not (a[i] < min));skip };
      i := i + 1;
      }
  end
  assert (forall j : i0 <= j < i: a[r] <= a[j])
end
-}
minind :: Stmt
minind = vars ["a" ::: intarr, "i" ::: int, "N" ::: int, "i0" ::: int, "r" ::: int]
          [ assume (vi "i" <. vi "N" /\ l 0 <=. vi "i")
          , vars ["min" ::: int]
              [ asgi ["r", "min"] [vi "i", "a" `ati` vi "i"]
              , while  (vi "i" <=. vi "N")
                       -- (forall ("j" ::: int) (vi "i0" <=: vi "j" /\: vi "j" <: vi "i" ==>:
                       --                       ("a" `ati` vi "r" <=: "a" `ati` vi "j" ))))
                       (vi "i" <. vi "N")
                       (stmts [choice [stmts [assume (("a" `ati` vi "i") <. vi "min")
                                             ,asgi ["r", "min"] [vi "i", "a" `ati` vi "i"]]
                                      ,stmts [assume (neg (("a" `ati` vi ".") <. vi "min"))
                                             ,skip]]
                              ,asgi ["i"] [vi "i" +. l 1]])]
          , assert (forall ("k" ::: int) (vi "i" <=. vi "k" /\ vi "k" <. vi "N" ==>
                                         (("a" `ati` vi "r") <=. ("a" `ati` vi "k") )))]

{-- | Loop1
var a:[int], i:int, s:int, N:int in
  assume 0=i /\ s=0 /\ 0<=N ;
  while i<N {
    assert 0<=i /\ i<N ;
    s := s + a[i] ;
    i := i+1
  }
  assert true
end
-}
loop1 :: (Expr Bool -> Stmt -> Stmt) -> Integer -> Stmt
loop1 while n = vars ["a" ::: intarr, "i" ::: int, "s" ::: int, "N" ::: int]
          [ assume (vi "i" ==. l 0 /\ vi "s" ==. l 0 /\ l 0 <=. vi "N" /\ vi "N" ==. l n)
          , while  (vi "i" <. vi "N")
                      (stmts [ assert (vi "i" >=. l 0 /\ vi "i" <. vi "N")
                             , asgi ["s"] [vi "s" +. "a" `ati` vi "i"]
                             , asgi ["i"] [vi "i" +. l 1]])
          , assert (l True)]

{-- | Loop2
var a:[int], i:int, N:int, k:int in
  assume 0=i /\ 0<=N /\ 0<=k /\ k<N ;
  while i<N { i := i+1 }
  assert 0<=k /\ k<N ;
  s = a[k]
  assert true
--}
loop2 :: (Expr Bool -> Stmt -> Stmt) -> Integer -> Stmt
loop2 while n = vars ["a" ::: intarr, "i" ::: int, "s" ::: int, "N" ::: int, "k"::: int]
          [ assume (vi "i" ==. l 0 /\ l 0 <=. vi "N" /\ l 0 <=. vi "k" /\ vi "k" <. vi "N" /\ vi "N" ==. l n)
          , while (vi "i" <. vi "N") (asgi ["i"] [vi "i" +. l 1])
          , assert (l 0 <=. vi "k" /\ vi "k" <. vi "N")
          , asgi ["s"] ["a" `ati` vi "k"]
          , assert (l True)]
