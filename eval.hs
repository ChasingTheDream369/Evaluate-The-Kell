module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax                                   
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type VEnv = E.Env Value


data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
		   | Closure VEnv Id [Id] Exp
           deriving (Show)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)
  pretty _ = undefined -- should not ever be used

evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE E.empty e
evaluate bs = evalE E.empty (Let bs (Var "main"))


evalE :: VEnv -> Exp -> Value

-- Constants and Boolean Constructors.

evalE envrmnt (Num c) = I c 
evalE envrmnt (Con "True") = B True
evalE envrmnt (Con "False") = B False
evalE envrmnt (Con "Nil") = Nil

-- Variable Bindings with Let.

evalE envrmnt (Let b e) = 

  case b of 
	[] -> evalE envrmnt e;
	[(Bind x _ [] e1)] -> evalE newEnvrmt e where 
 			      newEnvrmt = E.add envrmnt (x, evalE envrmnt e1); 
	[(Bind func _ args e1)] -> evalE newEnvrmt e where 
 				   newEnvrmt = E.add envrmnt (func, Closure envrmnt func args e1);
	(Bind x _ [] e1):bindings -> evalE newEnvrmt (Let bindings e) where 
 				     newEnvrmt = E.add envrmnt (x, evalE envrmnt e1);   
	(Bind func _ args e1):bindings -> evalE newEnvrmt (Let bindings e) where 
 					  newEnvrmt = E.add envrmnt (func, Closure envrmnt func args e1);   

-- Primitive operations

-- Primitive operations with one expression.

--Neg
evalE envrmnt (App (Prim Neg) (Num n)) = I (-n)
evalE envrmnt (App (Prim Neg) e) = evalE envrmnt (App (Prim Neg) (Num c)) where I c = evalE envrmnt e

--Null
evalE envrmnt (App (Prim Null) exp) = 

	let s = (evalE envrmnt exp) in
		case s of
			Nil -> B True
			undefined -> B False

-- Head 
evalE envrmnt (App (Prim Head) exp) = 

	case evalE envrmnt exp of
		Cons head tail -> I head
		Closure env f args e1 -> case evalE env e1 of Cons h t -> I h
		_ -> error "head undefined"

-- Tail 
evalE envrmnt (App (Prim Tail) exp) = 

	case evalE envrmnt exp of
		Cons head tail -> tail
		Closure env f args e1 -> case evalE env e1 of Cons h t -> t
		_ -> error "tail undefined"

-- Primitive operations with two expressions.

evalE envrmnt (App (App (Prim Add) e1) e2) = I (a + b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Sub) e1) e2) = I (a - b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Mul) e1) e2) = I (a * b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Rem) e1) e2) = I (rem a b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Ge) e1) e2) = B (a >= b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Gt) e1) e2) = B (a > b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Lt) e1) e2) = B (a < b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Le) e1) e2) = B (a <= b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Eq) e1) e2) = B (a == b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
-- not equals in haskell is written as: /= or not (x == y), 
evalE envrmnt (App (App (Prim Ne) e1) e2) = B (a /= b) where I a = evalE envrmnt e1; I b = evalE envrmnt e2;
evalE envrmnt (App (App (Prim Quot) e1) e2) = if b == 0 then error "division by zero" else I (quot a b) 
					      where I a = evalE envrmnt e1; I b = evalE envrmnt e2;

-- Evaluation of if -expression
evalE envrmnt (If e b1 b2) = 
	
	let B t = evalE envrmnt e in
		
		if t == True	
		then evalE envrmnt b1 
		else evalE envrmnt b2 


-- List constructors and primops
evalE envrmnt (App (App (Con "Cons") exp1) exp2) = 
	let I d = evalE envrmnt exp1 in
		Cons d (evalE envrmnt exp2)

-- Variables

evalE envrmnt (Var x) =

	case E.lookup envrmnt x of
		Just v -> v
		Just (Closure env f args e1) -> evalE env e1
		Nothing -> error("No value of the variable x is found")

--Recfun

evalE envrmnt (Recfun binding) =

	case binding of
		Bind func t args exp -> (Closure newEnvrmt func args exp) where 
					newEnvrmt = E.add envrmnt (func, Closure envrmnt func args exp);
		_ -> error " Not a function"
	
-- Function Application
evalE envrmnt (App (Var func) exp) =

	case E.lookup envrmnt func of
		Just (Closure env f args e)  -> if (length args == 1) then (evalE newEnvrmt e) 0
  						else if (length args == 0) then (evalE newEnvrmt1 e)
						else (Closure newEnvrmt f (tail args) e) 
      						where newEnvrmt1 = E.add envrmnt (f, (Closure env f args e)); 
	    					newEnvrmt = E.add newEnvrmt1 (args !! 0, evalE envrmnt exp);
		Nothing -> error "This does not evaluate to any value." 

evalE envrmnt (App exp1 exp) =

	case evalE envrmnt exp1 of
		(Closure env f args e) -> if (length args == 1) then (evalE newEnvrmt e) 
  					  else if (length args == 0) then (evalE newEnvrmt1 e) 
	 				  else (Closure newEnvrmt f (tail args) e) 
	                                  where newEnvrmt1 = E.add envrmnt (f, (Closure env f args e)); 
				          newEnvrmt = E.add newEnvrmt1 (args !! 0, evalE envrmnt exp);

-- error handling, for the non- handled cases.
evalE envrmnt e = error "implement me!"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         
