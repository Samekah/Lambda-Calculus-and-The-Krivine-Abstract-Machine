

-------------------------
-------- PART A --------- 
-------------------------

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
 --deriving Show

instance Show Term where
    show = pretty

example :: Term
example = Lambda "a" (Lambda "x" (Apply (Apply (Lambda "y" (Variable "a")) (Variable "x")) (Variable "b")))

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m


------------------------- Assignment 1
--Lambda "f" (Lambda "x" (Variable "x"))

numeral :: Int -> Term
numeral a = Lambda "f" (Lambda "x" (lmbd a))

lmbd :: Int -> Term
lmbd i 
        | i /= 0    = Apply (Variable "f") (lmbd (i - 1))
        | i == 0    = (Variable "x")
-------------------------

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys


------------------------- Assignment 2
variables :: [Var]
variables = [[z]| z <- ['a'..'z']] ++ [[n] ++ (show x)|x <- [1..], n <- ['a'..'z']]

check :: Var -> [Var] -> Bool
check x [] = False
check x (y:ys)
            |x /= y     = check x ys
            |x == y     = True
            

filterVariables :: [Var] -> [Var] -> [Var]
filterVariables [] _ = [] 
filterVariables xs [] = xs
filterVariables (x:xs) (y:ys)
                | check x (y:ys) == False   = x : filterVariables xs (y:ys)
                | check x (y:ys) == True    = filterVariables xs (y:ys) 


fresh :: [Var] -> Var
fresh [] = []
fresh (x:xs) = head(filterVariables variables (x:xs))

used :: Term -> [Var]
used (Variable v) = [v]
used (Lambda v t) = merge [v] (used t)
used (Apply t a) = merge (used t) (used a)

------------------------- Assignment 3

rename :: Var -> Var -> Term -> Term
rename x y (Variable z )
                        | z /= x    = Variable z
                        | z == x    = Variable y
rename x y (Lambda z n )
                        | z /= x    = Lambda z (rename x y n)
                        | z == x    = Lambda z n
rename x y (Apply  n m ) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x  z (Variable y )
                            | y /= x    = Variable y
                            | y == x    = z
substitute x  n (Lambda y z )
                            | y /= x    = Lambda k ( substitute x n (rename y k z))
                            | y == x    = Lambda y z
                               where
                                k = fresh (( used z) ++ ( used  n) ++ [x])
substitute x  a (Apply  z m ) = Apply (substitute x a z) (substitute x a m)


------------------------- Assignment 4

beta :: Term -> [Term]
beta (Variable y ) = []
beta (Lambda y z ) = [Lambda y bz | bz <- beta z]
beta (Apply (Lambda y z ) n) = [substitute y n z] ++ [Apply (Lambda y bz ) n | bz <- beta z] ++ [Apply (Lambda y z ) bn | bn <- beta n]
beta (Apply  z m ) = [Apply bz m | bz <- beta z] ++ [Apply z bm | bm <- beta m]


normalize :: Term -> IO ()
normalize z = do
                print z
                let b = (beta z)
                if null b
                then return ()
                else normalize (b !! 0)


------------------------- 

a_beta :: Term -> [Term]
a_beta (Variable y ) = []
a_beta (Lambda y z ) = [Lambda y bz | bz <- a_beta z]
a_beta (Apply (Lambda y z ) n) = [Apply (Lambda y bz ) n | bz <- a_beta z] ++ [Apply (Lambda y z ) bn | bn <- a_beta n] ++ [substitute y n z]
a_beta (Apply  z m ) = [Apply bz m | bz <- a_beta z] ++ [Apply z bm | bm <- a_beta m]

a_normalize :: Term -> IO ()
a_normalize z = do
                print z
                let b = (a_beta z)
                if null b
                then return ()
                else a_normalize (b !! 0)


-------------------------

example1 :: Term
example1 = ( Apply (Lambda "x" ( Apply ( Apply ( Variable "x" ) (Variable "x" ) ) ( Variable "x" ) ) ) ( Apply ( Lambda "a" ( Variable "a")) ( Variable "b"))) 

example2 :: Term
example2 = ( Apply (numeral 0) (example1))


-------------------------
-------- PART B --------- 
-------------------------


------------------------- Assignment 5 (PAM)


state1 = (Lambda "x" (Lambda "y" (Variable "x")) , [Variable "Yes", Variable "No"])

term1 = Apply (Apply (Lambda "x" (Lambda "y" (Variable "x"))) (Variable "Yes")) (Variable "No")

term2 = Apply (Apply (Lambda "b" (Apply example (Variable "Yes"))) (Lambda "z" (Variable "z"))) (Variable "No")

type PState = (Term,[Term])


p_start :: Term -> PState
p_start t = (t,[])

--do this :3
p_step :: PState -> PState
p_step (Lambda x n, m:s) =  ( substitute x m n, s)
p_step (Apply n m, s) =  ( n, m:s)

p_final :: PState -> Bool
p_final (Lambda x n, [])= True
p_final (Variable x, s) = True
p_final _ = False

p_run :: Term -> IO ()
p_run t = do
            let p = (p_start t)
            p_loop p

p_loop :: PState -> IO ()
p_loop l = do
            print l
            if (p_final l) == True
            then print (p_readback l)
            else p_loop ((p_step l))

p_readback :: PState -> Term
p_readback (t, []) = t
p_readback (t, xs) = Apply  (p_readback ( t, init xs))(last xs)


------------------------- Assignment 6 (KAM)

state2 = State (((Apply ( Lambda "x" (Variable "x")) (Variable "y")), (Env ( "y", ((Lambda "z" (Variable "z")), Empty)) Empty)), [])

state3 = State (((Apply ( Variable "x") (Variable "x")), (Env ( "x", ((Lambda "x" (Apply ( Variable "x") (Variable "x"))), Empty)) Empty)), [])

state4 = State (((Lambda "y" (Variable "x")), Empty ),[( Variable "z", Env  ("z", (( Lambda "a" (Variable "b")), Env ("b", ( Variable "c", Empty)) Empty)) Empty)])

data Env = Empty | Env (Var, Closure) Env
instance Show Env where
    show = env_show

data State = Sempty | State ((Closure), [Closure])
instance Show State where
    show = state_show

type Closure = (Term, Env)

env_show :: Env -> String
env_show (Empty) = "[]"
env_show (Env (x, (a, b)) Empty) = "[" ++ "(" ++ show x ++ "," ++ show a ++ "," ++ show b ++ ")" ++ "]"
env_show (Env (x, (a, b)) z) = "[" ++ "(" ++ show x ++ "," ++ show a ++ "," ++ show b ++ ")" ++ dotheish z ++ "]"

dotheish :: Env -> String
dotheish (Env (x, (a, b)) z) = ",(" ++ show x ++ "," ++ show a ++ "," ++ show b ++ ")"

state_show :: State -> String
state_show (State (((x,y), xs))) = "(" ++ show x ++ "," ++ show y ++ "," ++ show xs ++ ")"


start :: Term -> State
start t = State((t, Empty),[])

step :: State -> State
step (State ((((Variable x),(Env (v, (a, b)) z)), xs)))
                                            |x == v         = State ((a,b), xs)
                                            |otherwise      = State (((Variable x),z), xs)
step (State (((Lambda m n),z), ((x,y):xs))) = State (((n,( Env (m, (x, y)) z)), xs))
step (State (((Apply m n), z), xs)) = State ((m,z), ((n,z):xs))

final :: State -> Bool
final (State (((Lambda m n), e), [])) = True
final (State (((Variable v), Empty), xs)) = True
final _ = False

run :: Term -> IO ()
run t = do
            let p = (start t)
            loop p

loop :: State -> IO ()
loop l = do
            print l
            if (final l) == True
            then print (readback l)
            else loop ((step l))
            
readback :: State -> Term
readback (State((t, e),[])) = (help(t, e))
readback (State((t, e), xs)) = Apply  (readback(State((t, e), init xs))) (help(last xs))

help :: Closure -> Term
help (Variable x,Empty) = Variable x
help (Variable x, (Env (y, (n, e)) f))
                                    | x == y    = help (n, e)
                                    |otherwise  = help (Variable x, f)
help ((Lambda x n), xs) = (Lambda x (help (n, (Env(x,(Variable x, Empty)) xs))))
help ((Apply n m), xs) = Apply(help( n, xs)) (help( m, xs))