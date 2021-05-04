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
> import Data.List
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
>             deriving (Show, Eq)

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
>              deriving (Show, Eq)
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

fresh: to update the state and output a fresh integer accordingly.

> fresh :: ST Int 
> fresh = S (\n -> (n, n+1))


compexpr: to compile a single expression to assembly code by pattern matching.

> compexpr :: Expr -> Code
> compexpr (Val i)        = [PUSH i]
> compexpr (Var n)        = [PUSHV n]
> compexpr (App op e1 e2) = compexpr e1 ++ compexpr e2 ++ [DO op]

                              
compprog: to compile a program to machine code by pattern matching. compprog
compiles the program by compiling each expression with compexpr and combined the
results. compprog is acchieved by a writer monad transformer to log the code to
be outputted by tell. The code is recorded at the backend and updated in each 
compiling by adding new compiled outcomes. The state monad is updated at the 
backend during each compiling as well. compprog also makes used of fresh to 
generate fresh labels added to the code. 

> compprog :: Prog -> WriterT Code ST ()
> compprog (Assign c e)  = do tell (compexpr e) 
>                             tell [POP c]
> compprog (If e p1 p2)  = do l <- lift fresh
>                             l1 <- lift fresh
>                             l2 <- lift fresh
>                             tell (compexpr e) 
>                             tell [JUMPZ l1,LABEL l]
>                             compprog p1 
>                             tell [JUMP l2, LABEL l1]
>                             compprog p2
>                             tell [LABEL l2]
> compprog (While e p)   = do l <- lift fresh
>                             l1 <- lift fresh 
>                             tell (LABEL l : compexpr e) 
>                             tell [JUMPZ l1]
>                             compprog p 
>                             tell [JUMP l, LABEL l1]
> compprog (Seqn [])     = return ()
> compprog (Seqn (p:ps)) = do compprog p
>                             compprog (Seqn ps)


comp: the main function of the compiler. It executes compprog, which is
implemented by a writer monad transformer, and extracts the resulted code out.

> comp :: Prog -> Code
> comp p = fst (app (execWriterT (compprog p)) 0)


popVar: to assign the new value to the specified variable in the memory

> popVar :: Mem -> Char -> Int -> Mem
> popVar ((c1,v):ms) c2 i
>   | c1 == c2 = (c1,i):ms
>   | otherwise = (c1,v):(popVar ms c2 i)
> popVar [] c i = [(c,i)]


op2func: to convert the specified 'Op' into its corresponding function

> op2func :: Op -> (Int -> Int -> Int)
> op2func Add = (+)
> op2func Sub = (-)
> op2func Mul = (*)
> op2func Div = div

doOpr: to do the specified operation on the stack and return the changed stack

> doOpr :: Stack -> Op -> Stack
> doOpr (i1:(i2:is)) o = (op i2 i1):is
>   where op = op2func o

execHelper: to execute the code from the first instruction and returns the final memory,
and a program counter is used to specify which instruction to execute next

> execHelper :: Code -> Int -> Mem -> Stack -> Mem
> execHelper c p m s 
>   | p >= length c = m 
>   | otherwise = case (c!!p) of 
>       PUSH i    -> execHelper c (p+1) m (i:s)
>       PUSHV v   -> execHelper c (p+1) m ((case (lookup v m) of Just x -> x):s)
>       POP v     -> execHelper c (p+1) (popVar m v (head s)) (tail s)
>       DO o      -> execHelper c (p+1) m (doOpr s o)
>       JUMP l    -> execHelper c (case (elemIndex (LABEL l) c) of Just x -> x) m s
>       JUMPZ l   -> execHelper c (if head s == 0 then (case (elemIndex (LABEL l) c) of Just x -> x) else (p+1)) m (tail s)
>       LABEL l -> execHelper c (p+1) m s


exec: to execute the program

> exec :: Code -> Mem
> exec c = execHelper c 0 [] []