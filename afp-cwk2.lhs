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
                              

> compprog :: Prog -> ST Code
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


> instType :: Inst -> Int
> instType (PUSH i) = 0
> instType (PUSHV n) = 1
> instType (POP n) = 2
> instType (DO o) = 3
> instType (JUMP l) = 4
> instType (JUMPZ l) = 5
> instType _ = 6
> -- instType (LABEL l) = 6

> pushInt :: Inst -> Int
> pushInt (PUSH i) = i
> pushInt _ = 0

> pushVar :: Inst -> Mem -> Int
> pushVar (PUSHV c1) ((c2,i):ms)
>   | c1 == c2 = i
>   | otherwise = pushVar (PUSHV c1) ms
> pushVar _ _ = 0

> popVar :: Mem -> Inst -> Int -> Mem
> popVar ((c1,v):ms) (POP c2) i
>   | c1 == c2 = (c1,i):ms
>   | otherwise = (c1,v):(popVar ms (POP c2) i)
> popVar [] (POP c) i = [(c,i)]
> popVar ms _ _ = ms

> op2func :: Op -> (Int -> Int -> Int)
> op2func Add = (+)
> op2func Sub = (-)
> op2func Mul = (*)
> op2func Div = div

> doOpr :: Stack -> Inst -> Stack
> doOpr (i1:(i2:is)) (DO o) = heads ++ [op l2 l1]
>   where 
>       heads = init (init (i1:(i2:is)))
>       l2 = last (init (i1:(i2:is)))
>       l1 = last (i1:(i2:is))
>       op = op2func o
> doOpr s _ = s

> jumpLbl :: Int -> Code -> Inst -> Int 
> jumpLbl i ((LABEL l1):cs)  (JUMP l2)
>   | l1 == l2 = i 
>   | otherwise = jumpLbl (i+1) cs (JUMP l2)
> jumpLbl i (c:cs) (JUMP l) = jumpLbl (i+1) cs (JUMP l)
> jumpLbl i ((LABEL l1):cs)  (JUMPZ l2)
>   | l1 == l2 = i 
>   | otherwise = jumpLbl (i+1) cs (JUMPZ l2)
> jumpLbl i (c:cs) (JUMPZ l) = jumpLbl (i+1) cs (JUMPZ l)
> jumpLbl _ _ _ = 0

execHelper :: Code -> Int -> Mem -> Stack -> Mem
execHelper c p m s 
  | p >= length c = m
  | instType (c!!p) == 0 = execHelper c (p+1) m (s ++ [pushInt (c!!p)])
  | instType (c!!p) == 1 = execHelper c (p+1) m (s ++ [pushVar (c!!p) m])
  | instType (c!!p) == 2 = execHelper c (p+1) (popVar m (c!!p) (last s)) (init s)
  | instType (c!!p) == 3 = execHelper c (p+1) m (doOpr s (c!!p))
  | instType (c!!p) == 4 = execHelper c (jumpLbl 0 c (c!!p)) m s
  | instType (c!!p) == 5 = execHelper c (if last s == 0 then (jumpLbl 0 c (c!!p)) else (p+1)) m (init s)
  | otherwise = execHelper c (p+1) m s

exec :: Code -> Mem
exec c = execHelper c 0 [] []


> execHelper :: Code -> Int -> Mem -> Stack -> WriterT Mem ST ()
> execHelper c p m s 
>   | p >= length c = tell m
>   | instType (c!!p) == 0 = execHelper c (p+1) m (s ++ [pushInt (c!!p)])
>   | instType (c!!p) == 1 = execHelper c (p+1) m (s ++ [pushVar (c!!p) m])
>   | instType (c!!p) == 2 = execHelper c (p+1) (popVar m (c!!p) (last s)) (init s)
>   | instType (c!!p) == 3 = execHelper c (p+1) m (doOpr s (c!!p))
>   | instType (c!!p) == 4 = execHelper c (jumpLbl 0 c (c!!p)) m s
>   | instType (c!!p) == 5 = execHelper c (if last s == 0 then (jumpLbl 0 c (c!!p)) else (p+1)) m (init s)
>   | otherwise = execHelper c (p+1) m s


> exec :: Code -> Mem
> exec c = fst (app (execWriterT (execHelper c 0 [] [])) 0)

