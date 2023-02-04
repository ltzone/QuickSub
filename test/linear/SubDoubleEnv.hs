data Typ = TTop | TInt | Fun Typ Typ | Mu Typ | Var Int deriving Show


type Env = [Maybe Typ]


wf_typ :: Env -> Typ -> Bool
wf_typ e TInt                 = True
wf_typ e TTop                 = True
wf_typ (Nothing:xs) (Var 0)   = True
wf_typ (Just x : xs) (Var 0)  = True -- wf_typ xs x  
wf_typ (x:xs) (Var i)         = wf_typ xs (Var (i-1))  
wf_typ e (Fun a b)            = wf_typ e a && wf_typ e b
wf_typ e (Mu a)               = wf_typ (Just a:e) a
wf_typ e t                    = error (show e ++ " |- " ++ show t)


wf :: Env -> Env -> Bool
wf [] []                      = True
wf (Nothing:xs) (Nothing:ys)  = wf xs ys
wf (Just x:xs) (Just y:ys)    = {- wf_typ xs x && wf_typ ys y && -} wf xs ys
wf _ _                        = False


replace :: Int -> a -> [a] -> [a]
replace i x []      = []
replace 0 x (_:xs)  = x:xs
replace i x (y:xs)  = y:(replace (i-1) x xs) 


subRec :: Env -> Typ -> Env -> Typ -> Bool
subRec e1 a e2 TTop                               = wf e1 e2
subRec e1 TInt e2 TInt                            = wf e1 e2
subRec (Nothing:xs) (Var 0) (Nothing:ys) (Var 0)  = wf xs ys
subRec (Just x:xs) (Var 0) (Just y:ys) (Var 0)    = subRec (Nothing:xs) x (Nothing:ys) y
subRec (Just x:xs) (Var i) (Just y:ys) (Var j)
   | i == j    = subRec xs (Var (i-1)) ys (Var (j-1))
   | otherwise = False
subRec e1 (Fun a b) e2 (Fun c d)                  = subRec e2 c e1 a && subRec e1 b e2 d
subRec e1 (Mu a) e2 (Mu b)                        = subRec (Just a : e1) a (Just b : e2) b
subRec e1 t1 e2 t2 = error (show e1 ++ " |- " ++ show t1 ++ " <: " ++ show t2 ++ " -| " ++ show e2) 


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


t1 = Mu (Fun (Var 0) TInt) -- mu a. a -> Int


t2 = Mu (Fun (Var 0) TTop) -- mu a . a -> Top


test1 = sub t1 t1


test2 = sub t1 t2