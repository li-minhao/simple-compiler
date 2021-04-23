G52AFP Coursework 2 - Monadic Compiler

Your full name(s)
Minhao Li
Jou-Yin Huang

Your full email address(es)
scyml4@nottingham.ac.uk
scyjh2@nottingham.ac.uk

--------------------------------------------------------------------------------

We use some functions from the following libraries.

> import Data.Char
> import Control.Monad.Trans.Writer
> import Control.Monad.Trans


Imperative language:

> data Prog = Assign Name Expr
>           | If Expr Prog Prog
>           | While Expr Prog
>           | Seqn [Prog]
>             deriving Show
>
> data Expr = Val Int | Var Name | App Op Expr Expr
>             deriving Show
>
> type Name = Char
>
> data Op   = Add | Sub | Mul | Div
>             deriving Show

Factorial example:

> fac :: Int -> Prog
> fac n = Seqn [Assign 'A' (Val 1),
>               Assign 'B' (Val n),
>               While (Var 'B') (Seqn
>                  [Assign 'A' (App Mul (Var 'A') (Var 'B')),
>                   Assign 'B' (App Sub (Var 'B') (Val 1))])]

Virtual machine:

> type Stack = [Int]
>
> type Mem   = [(Name,Int)]
>
> type Code  = [Inst]
> 
> data Inst  = PUSH Int
>            | PUSHV Name
>            | POP Name
>            | DO Op
>            | JUMP Label
>            | JUMPZ Label
>            | LABEL Label
>              deriving Show
> 
> type Label = Int

State monad:

> type State = Label
>
> newtype ST a = S (State -> (a, State))
>
> app :: ST a -> State -> (a,State)
> app (S st) x 	=  st x
>
> instance Functor ST where
>    -- fmap :: (a -> b) -> ST a -> ST b
>    fmap g st = S (\s -> let (x,s') = app st s in (g x, s'))
>
> instance Applicative ST where
>    -- pure :: a -> ST a
>    pure x = S (\s -> (x,s))
>
>    -- (<*>) :: ST (a -> b) -> ST a -> ST b
>    stf <*> stx = S (\s ->
>       let (f,s')  = app stf s
>           (x,s'') = app stx s' in (f x, s''))
>
> instance Monad ST where
>    -- return :: a -> ST a
>    return x = S (\s -> (x,s))
>
>    -- (>>=) :: ST a -> (a -> ST b) -> ST b
>    st >>= f = S (\s -> let (x,s') = app st s in app (f x) s')

--------------------------------------------------------------------------------

> fresh :: ST Int 
> fresh = S (\n -> (n, n+1))


> compexpr :: Expr -> Code
> compexpr (Val i)        = [PUSH i]
> compexpr (Var n)        = [PUSHV n]
> compexpr (App op e1 e2) = compexpr e1 ++ compexpr e2 ++ [DO op]
                              

> compprog :: Prog -> WriterT Code ST ()
> compprog (Assign c e)  = do tell (compexpr e) >> tell [POP c]
> compprog (If e p1 p2)  = do l <- lift fresh
>                             l1 <- lift fresh
>                             tell (compexpr e) >> tell (JUMPZ l1 : (comp p1)) >> tell (LABEL l : (comp p2))
> compprog (While e p)   = do l <- lift fresh
>                             l1 <- lift fresh 
>                             tell (LABEL l : compexpr e) >> tell (JUMPZ l1 : (comp p)) >> tell [JUMP l, LABEL l1]
> compprog (Seqn [])     = tell []
> compprog (Seqn (p:ps)) = tell (comp p) >> tell (comp (Seqn ps))


> comp :: Prog -> Code
> comp p = fst (app (execWriterT (compprog p)) 0)



> testP :: Int -> Int -> Prog
> testP a b = Seqn [Assign 'A' (Val a),
>                  Assign 'B' (Val b),
>                  If (App Sub (Var 'B') (Var 'A')) 
>                     (Seqn [Assign 'A' (App Mul (Var 'A') (Var 'B'))])
>                     (Assign 'A' (App Add (Var 'A') (Var 'B')))]

> getVar :: Char -> Mem -> Int
> getVar c1 ((c2,i):ms)
>   | c1 == c2 = i
>   | otherwise = getVar c1 ms

> popVar :: Mem -> Char -> Int -> Mem
> popVar ((c1,v):ms) c2 i
>   | c1 == c2 = (c1,i):ms
>   | otherwise = (c1,v):(popVar ms c2 i)
> popVar [] c i = [(c,i)]

> op2func :: Op -> (Int -> Int -> Int)
> op2func Add = (+)
> op2func Sub = (-)
> op2func Mul = (*)
> op2func Div = div

> doOpr :: Stack -> Op -> Stack
> doOpr (i1:(i2:is)) o = heads ++ [op l2 l1]
>   where 
>       heads = init (init (i1:(i2:is)))
>       l2 = last (init (i1:(i2:is)))
>       l1 = last (i1:(i2:is))
>       op = op2func o

> jumpLbl :: Int -> Code -> Label -> Int 
> jumpLbl i ((LABEL l1):cs) l2
>   | l1 == l2 = i 
>   | otherwise = jumpLbl (i+1) cs l2
> jumpLbl i (c:cs) l = jumpLbl (i+1) cs l
> jumpLbl _ _ _ = 0

> execHelper :: Code -> Int -> Mem -> Stack -> Mem
> execHelper c p m s 
>   | p >= length c = m 
>   | otherwise = case (c!!p) of 
>       PUSH i    -> execHelper c (p+1) m (s ++ [i])
>       PUSHV v   -> execHelper c (p+1) m (s ++ [getVar v m])
>       POP v     -> execHelper c (p+1) (popVar m v (last s)) (init s)
>       DO o      -> execHelper c (p+1) m (doOpr s o)
>       JUMP l    -> execHelper c (jumpLbl 0 c l) m s
>       JUMPZ l   -> execHelper c (if last s == 0 then (jumpLbl 0 c l) else (p+1)) m (init s)
>       otherwise -> execHelper c (p+1) m s

> exec :: Code -> Mem
> exec c = execHelper c 0 [] []

