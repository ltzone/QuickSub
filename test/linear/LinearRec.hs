import Data.List
import Prelude hiding (rem)

data Typ = TInt | Top | Fun Typ Typ | Mu Typ | Var Int deriving (Eq)

instance Show Typ where
  show TInt = "int"
  show Top = "T"
  show (Fun a b) = "" ++ show a ++ " -> " ++ show b ++ ""
  show (Var s) = show s
  show (Mu t) = "(mu ." ++ show t ++ ")"


data Cmp = Less | Equal [Int] deriving (Show, Eq)

data Mode = Plus | Minus deriving (Show, Eq)

type Env = [Mode]

eq = Equal []
lt = Less

neg Plus  = Minus
neg Minus = Plus

rem :: Int -> Cmp  -> Cmp
rem i Less       = Less
rem i (Equal l)  = Equal (map ((-) 1) (delete 0 l))

(&&&) :: Cmp -> Cmp -> Maybe Cmp
Less        &&& Less          = Just Less
Less        &&& (Equal [])    = Just Less
(Equal [])  &&& Less          = Just Less
(Equal xs)  &&& (Equal ys)    = Just (Equal (union xs ys))
_           &&& _             = Nothing

-- check x e m a b
--
-- x ==> the current de Bruijn index
-- e ==> the current environment
-- m ==> the current mode
-- a ==> first type
-- b ==> second type

check :: Int -> Env -> Mode -> Typ -> Typ -> Maybe Cmp
check x e m TInt       TInt         = Just eq
check x e m Top        Top          = Just eq
check x e m a          Top          = Just lt
check x e m (Var i)    (Var j)
   | i == j && e !! i == m          = Just eq
   | i == j && e !! i == neg m      = Just (Equal [i])
check x e m (Mu a)     (Mu b)       = fmap (rem x) $ check (x+1) (m : e) m a b
check x e m (Fun a b)  (Fun c d)    =
   do cmp1 <- check x e (neg m) c a
      cmp2 <- check x e m b d
      (cmp1 &&& cmp2)
check x e m _          _            = Nothing 

chk :: Typ -> Typ -> Maybe Cmp
chk = check 0 [] Plus

judge_chk :: Maybe Cmp -> Bool
judge_chk (Just (Equal [])) = True
judge_chk (Just Less) = True
judge_chk _ = False

-- Example 1

t1 = Mu (Fun Top (Var 0))
t2 = Mu (Fun (Var 0) (Var 0))

test1 = chk t1 t2

-- Example 2

t3 = Mu (Fun (Var 0) TInt)
t4 = Mu (Fun (Var 0) Top)

test2 = chk t3 t4

-- Example 3

test3 = chk t2 t2

-- Example 4

t5 = Fun t2 TInt
t6 = Fun t2 Top

test4 = chk t5 t6

-- Example 5

t7 = Mu (Fun Top (Fun (Var 0) (Var 0)))
t8 = Mu (Fun TInt (Fun (Var 0) (Var 0)))

test5 = chk t7 t8



type Env2 = [Maybe Typ]


wf_typ :: Env2 -> Typ -> Bool
wf_typ e TInt                 = True
wf_typ e Top                 = True
wf_typ (Nothing:xs) (Var 0)   = True
wf_typ (Just x : xs) (Var 0)  = True -- wf_typ xs x  
wf_typ (x:xs) (Var i)         = wf_typ xs (Var (i-1))  
wf_typ e (Fun a b)            = wf_typ e a && wf_typ e b
wf_typ e (Mu a)               = wf_typ (Just a:e) a
wf_typ e t                    = error (show e ++ " |- " ++ show t)


wf :: Env2 -> Env2 -> Bool
wf [] []                      = True
wf (Nothing:xs) (Nothing:ys)  = wf xs ys
wf (Just x:xs) (Just y:ys)    = {- wf_typ xs x && wf_typ ys y && -} wf xs ys
wf _ _                        = False


replace :: Int -> a -> [a] -> [a]
replace i x []      = []
replace 0 x (_:xs)  = x:xs
replace i x (y:xs)  = y:(replace (i-1) x xs) 


subRec :: Env2 -> Typ -> Env2 -> Typ -> Bool
subRec e1 a e2 Top                               = wf e1 e2
subRec e1 TInt e2 TInt                            = wf e1 e2
subRec (Nothing:xs) (Var 0) (Nothing:ys) (Var 0)  = wf xs ys
subRec (Just x:xs) (Var 0) (Just y:ys) (Var 0)    = subRec (Nothing:xs) x (Nothing:ys) y
subRec (Just x:xs) (Var i) (Just y:ys) (Var j)
   | i == j    = subRec xs (Var (i-1)) ys (Var (j-1))
   | otherwise = False
subRec e1 (Fun a b) e2 (Fun c d)                  = subRec e2 c e1 a && subRec e1 b e2 d
subRec e1 (Mu a) e2 (Mu b)                        = subRec (Just a : e1) a (Just b : e2) b
subRec e1 t1 e2 t2 = False
    -- error (show e1 ++ " |- " ++ show t1 ++ " <: " ++ show t2 ++ " -| " ++ show e2) 


{-
​
E ::= . | E, a | E, a |-> A
​
==================
E1 |- A <: B -| E2
==================
​
E1 |- A <: Top -| E2
​
E1 |- Int <: Int -| E2
​
a in E1    a in E2    
-------------------
E1 |- a <: a -| E2
​
E1', a, E1'' |- A <: B  -| E2', a, E2''
--------------------------------------------------
E1', a |-> A, E1'' |- a <: a -| E2', a |-> B, E2''
​
E2 |- C <: A -| E1    E1 |- B <: D -| E2
----------------------------------------
E1 |- A -> B <: C -> D |- E2
​
E1, a |-> A |- A <: B -| E2, a |-> B
------------------------------------
E1 |- mu a . A <: mu a. B -| E2
​
-}


sub :: Typ -> Typ -> Bool
sub t1 t2 = subRec [] t1 [] t2





level = 4

generate :: Int -> Int -> [Typ]
generate 0 0 = [Mu x | x <- generate 1 0]
generate n k = if (n==level)
  then
    [TInt, Top] ++ [Var x | x <- [0..k]]
  else
    let x = generate (n+1) k in
      let y = generate (n+1) (k+1) in
    [TInt, Top] ++ [Var x | x <- [0..k]] ++ [Fun a b| a <- x, b <- x]
    ++ [Mu a | a <- y]

types = generate 0 0 -- 81324 types




counter_example = [(a,b) | a <- types, b <- types, sub a b, not (judge_chk (chk a b))]
counter_example2 = [(a,b) | a <- types, b <- types, (judge_chk (chk a b)), not (sub a b)]