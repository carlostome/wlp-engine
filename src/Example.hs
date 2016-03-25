module Example where

import           Stmt

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
swap1 =
  var (i "x") $ var (i "y") $ var ("b" ::: int) $ var ("a" ::: int) $ stmts
    [assume ((vi "x" ==. vi "a") /\ (vi "y" ==. vi "b"))
    ,var ("tmp" ::: int) $ stmts
       [ asg [i "tmp" .:= vi "x"]
       , asg [i "x"   .:= vi "x"]
       , asg [i "x"   .:= vi "y"]
       , asg [i "y"   .:= vi "tmp"]]
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
swap2 =
  var (i "x") $ var (i "y") $ var ("b" ::: int) $ var ("a" ::: int) $ stmts
    [ assume ((vi "x" ==. vi "a") /\ (vi "y" ==. vi "b"))
    , asg [i "x" .:= vi "x" +. vi "y"]
    , asg [i "y" .:= vi "x" -. vi "y"]
    , asg [i "x" .:= vi "x" -. vi "y"]
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
swaparr =
  var (ai "a") $ var (i "i") $ var ("j" ::: int) $ var ("x" ::: int) $ var ("y" ::: int) $ stmts
      [ assume ((("a" `ixi` vi "i") ==. vi "x") /\ (("a" `ixi` vi "j") ==. vi "y"))
      , var ("tmp" ::: int) $ stmts
          [ asg  [i "tmp" .:= "a" `ixi` vi "i"]
          , asg  [ati "a" (vi "i") ("a" `ixi` vi "j")]
          , asg  [ati "a" (vi "j") (vi "tmp")]]
      , assert ((("a" `ixi` vi "i") ==. vi "y") /\ (("a" `ixi` vi "j") ==. vi "x"))]

{-- | Array 1
var a:[int], j:int, i:int, in
  assume (a[i] = a[j] /\ ~(j = i)) ;
    a[i] := a[i] + 1;
    a[j] := a[j] + 1;
  end
  assert (a[i] = a[j]);
end
-}

arr1 :: Stmt
arr1 =
  var (ai "a") $ var (i "i") $ var ("j" ::: int) $ stmts
    [ assume (("a" `ixi` vi "i") ==. ("a" `ixi` vi "j" ) /\ (neg $ vi "i" ==. vi "j"))
    , asg  [ati "a" (vi "i") ("a" `ixi` vi "i" +. li 1)]
    , asg  [ati "a" (vi "j") ("a" `ixi` vi "j" +. li 1)]
    , assert (("a" `ixi` vi "i") ==. ("a" `ixi` vi "j"))]

{-
(a[i]=a[j]) ==> ((((j=i) ==> ((a[i]+1)=(1+(a[i]+1)))) /\ (~(j=i) ==> (a[i]+1)=(1+a[j]))))
-}


{-- | Example D1
var x:int, y:iny in
  assume 0<x ;
  inv 0<=x while 0<x { x := x-1 } ;
  y := x ;
  assert y=0;
end
-}
d1 :: Stmt
d1 = var ("x" ::: int) $ var ("y" ::: int) $ stmts
      [ assume (li 0 <. vi "x")
      , while  (li 0 <=. vi "x")
               (li 0 <. vi"x")
               (asg [i "x" .:= vi "x" -. li 1])
      , asg [i "y" .:= vi "x"]
      , assert (vi "y" ==. li 0)]

{-- | Example D2
var x:int, y:iny in
  assume 2<=x ;
  inv 0<=x while 0<x { x := x-2 } ;
  y := x ;
  assert y=0 ;
end
-}
d2 :: Stmt
d2 = var ("x" ::: int) $ var ("y" ::: int) $ stmts
      [ assume (li 2 <=. vi "x")
      , while  (li 0 <=. vi "x")
               (li 0 <. vi"x")
               (asg [i "x" .:= vi "x" -. li 2])
      , asg [i "y" .:= vi "x"]
      , assert (vi "y" ==. li 0)]

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
minind =
  var ("a" ::: intarr) $ var ("i" ::: int) $ var ("N" ::: int) $ var ("r" ::: int) $ stmts
    [ assume (vi "i" <. vi "N" /\ li 0 <=. vi "i")
    , var ("min" ::: int) $ stmts
        [ asg [i "r" .:= vi "i", i "min" .:= "a" `ixi` vi "i"]
        , while  (vi "i" <=. vi "N") (vi "i" <. vi "N")
            (stmts
              [choice
                [stmts [ assume (("a" `ixi` vi "i") <. vi "min")
                       , asg [i "r" .:= vi "i", i "min" .:=  "a" `ixi` vi "i"]]
                ,stmts [assume (neg (("a" `ixi` vi "i") <. vi "min"))
                       ,skip]]
              ,asg [i "i" .:= vi "i" +. li 1]])]
          , assert (forall ("k" ::: int) (vi "i" <=. vi "k" /\ vi "k" <. vi "N" ==>
                                         (("a" `ixi` vi "r") <=. ("a" `ixi` vi "k") )))]

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
loop1 :: (Expr BOOL -> Stmt -> Stmt) -> Int -> Stmt
loop1 while' n =
  var ("a" ::: intarr) $ var ("i" ::: int) $ var ("s" ::: int) $ var ("N" ::: int) $ stmts
    [ assume (vi "i" ==. li 0 /\ vi "s" ==. li 0 /\ li 0 <=. vi "N")
    , while'  (vi "i" <. vi "N")
       (stmts [ assert (vi "i" >=. li 0 /\ vi "i" <. vi "N")
              , asg [i "s" .:= vi "s" +. "a" `ixi` vi "i"]
              , asg [i "i" .:= vi "i" +. li 1]])
          , assert (lb True)]

{-- | Loop2
var a:[int], i:int, N:int, k:int in
  assume 0=i /\ 0<=N /\ 0<=k /\ k<N ;
  while i<N { i := i+1 }
  assert 0<=k /\ k<N ;
  s = a[k]
  assert true
--}
loop2 :: (Expr BOOL -> Stmt -> Stmt) -> Int -> Stmt
loop2 while' n =
  var ("a" ::: intarr) $ var ("i" ::: int) $ var ("s" ::: int) $
  var ("N" ::: int) $ var ("k" ::: int) $ stmts
    [ assume (vi "i" ==. li 0 /\ li 0 <=. vi "N" /\ li 0 <=. vi "k" /\ vi "k" <. vi "N" /\ vi "N" ==. li n)
    , while' (vi "i" <. vi "N") (asg [i "i" .:=  vi "i" +. li 1])
    , assert (li 0 <=. vi "k" /\ vi "k" <. vi "N")
    , asg [i "s" .:= "a" `ixi` vi "k"]
    , assert (lb True)]

--------------------------------------------------------------------------------
-- Program call
--------------------------------------------------------------------------------

inc :: Prog
inc = prog "inc"
      [u (i "i")]
      [u (i "r")]
      (stmts [ asg [i "r" .:= vi "i" +. li 1]
             , assert ( vi "r" ==. vi "i" +. li 1)])

incspec :: Prog
incspec =
  spec "incspec"
  [u (i "i")]
  [u (i "r")]
  (lb True)
  (vi "r" ==. vi "i" +. li 1)

prog1 :: Prog
prog1 =
  prog "inccall"
  []
  []
  (var ("x" ::: int) $
    var ("y"  ::: int) $ stmts
      [ assume (vi "x" ==. vi "y")
      --, pcall [ut (tv (i "x"))] "incspec" [ue (vi "x")]
      , pcall [ut (tv (i "x"))] "inc" [ue (vi "x")]
      , assert (vi "x" ==. vi "y" +. li 1)])

incenv :: [Prog]
incenv = [inc, incspec]

dropspec :: Prog
dropspec =
  spec "dropspec"
  [u (i "x")]
  [u (i "r")]
  (vi "x" >. li 0)
  (vi "r" <. vi "x")

prog2 :: Prog
prog2 =
  prog "dropcall"
  []
  []
  (var ("x" ::: int) $ stmts
      [ pcall [ut (tv (i "x"))] "dropspec" [ue (vi "x")]
      , assert (vi "x" <. li 7)])

dropenv :: [Prog]
dropenv = [dropspec]
{-- | Sort (as Stmt)
sort (a, N | a' ){
  var i in
    i := 0 ;
    while i < N −1 do {
      m := minind(a, i+1, N ) ;
      if a[m]<a[i] then a := swap(a, i, m) else skip ;
      i++
    }
    a' := a
  end
}

-}

sort :: Prog
sort =
  prog "sort"
  [u ("a"  ::: intarr), u ("N" ::: int)]
  [u ("b" ::: intarr)] $ stmts
    [var (i "i") $ stmts
      [ assume (vi "N" >. li 0)
      , asg [i "i" .:= li 0]
      , while (vi "i" <. vi "N" /\ vi "i" >=. li 0)
              (vi "i" <. vi "N" -. li 1) $ stmts
          [ pcall [ut (tv (i "m"))] "minind_spec" [ue (vai "a"), ue (vi "i" +. li 1), ue (vi "N")]
          , ifS ("a" `ixi` (vi "m") <. "a" `ixi` (vi "i") )
                (pcall [ut (tv (ai "a"))] "swap" [ue (vai "a"), ue (vi "i"), ue (vi "m")])
                skip
          , asg [i "i" .:= vi "i" +. li 1]]]
    , assert (forall ("k" ::: int) (li 0 <=. vi "k" /\ vi "k" <. vi "N" -. li 1 ==>
             (("a" `ixi` vi "k") <=. ("a" `ixi` (vi "k" +. li 1)) )))
    , asg [ai "b'" .:= vai "a"]]

swap :: Prog
swap = prog "swap" [u ("a''" ::: intarr), u (i "i''"), u (i "j''")] [u ("ret" ::: intarr)] $
  var ("x" ::: int) $ var ("y" ::: int) $ stmts
      [ assume ((("a''" `ixi` vi "i''") ==. vi "x") /\ (("a''" `ixi` vi "j''") ==. vi "y"))
      , var ("tmp" ::: int) $ stmts
          [ asg  [i "tmp" .:= "a''" `ixi` vi "i''"]
          , asg  [ati "a''" (vi "i''") ("a''" `ixi` vi "j''")]
          , asg  [ati "a''" (vi "j''") (vi "tmp")]]
      , asg [ai "ret" .:= vai "a''"]
      , assert ((("ret" `ixi` vi "i''") ==. vi "y") /\ (("ret" `ixi` vi "j''") ==. vi "x"))]

minind_spec :: Prog
minind_spec =
  spec "minind_spec"
  [u (ai "a'"), u (i "i'"), u (i "N'")]
  [u (i "r")]
  (li 0 <=. vi "i'" /\ vi "i'" <. vi "N'")
  (forall (i "k") ((vi "k" >=. vi "i" /\ vi "k" <. vi "N") ==> ("a'" `ixi` vi "r" <=. "a'" `ixi` vi "k")))

sortenv :: [Prog]
sortenv = [swap, minind_spec]
