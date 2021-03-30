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
> compexpr (Val i) = [PUSH i]
> compexpr (Var n) = [PUSHV n]
> compexpr (App op e1 e2) = (compexpr e1) ++ (compexpr e2) ++ [DO op]


> comp :: Prog -> Code
> comp p = fst (app (compprog p) 0)
                              

> compprog :: Prog -> ST (Code)
> compprog (Assign c e) = return ((compexpr e) ++ [POP c])
> compprog (If e p1 p2) = do l <- fresh
>                            pp1 <- compprog p1
>                            pp2 <- compprog p2
>                            return ((compexpr e) ++ [JUMPZ l] ++ pp1 ++ [LABEL 0] ++ pp2)
> compprog (While e p) = do l <- fresh
>                           l1 <- fresh 
>                           pp <- compprog p
>                           return ((LABEL l : (compexpr e)) ++ [JUMPZ l1] ++ pp ++ [JUMP l, LABEL l1])
> compprog (Seqn []) = return []
> compprog (Seqn (p:ps)) = do pp <- compprog p 
>                             pps <- compprog (Seqn ps)
>                             return (pp ++ pps)

> testP :: Int -> Int -> Prog
> testP a b = Seqn [Assign 'A' (Val a),
>                   Assign 'B' (Val b),
>                   If (App Sub (Var 'B') (Var 'A')) 
>                      (Seqn [Assign 'A' (App Mul (Var 'A') (Var 'B'))])
>                      (Assign 'A' (App Add (Var 'A') (Var 'B')))]


