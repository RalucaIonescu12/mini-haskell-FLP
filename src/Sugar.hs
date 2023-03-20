
module Sugar where

import Exp
-- newtype Var = Var { getVar :: String } deriving (Show)
-- data Exp = X IndexedVar | Lam IndexedVar Exp | App Exp Exp deriving (Show)
-- data IndexedVar = IndexedVar { ivName :: String , ivCount :: Int } deriving (Eq, Read, Show)

desugarVar :: Var -> IndexedVar
desugarVar (Var name) = IndexedVar { ivName = name, ivCount = 0 }


-- >>> desugarVar (Var "x")
-- IndexedVar {ivName = "x", ivCount = 0}

sugarVar :: IndexedVar -> Var
sugarVar (IndexedVar name 0) = Var name
sugarVar (IndexedVar name index) = Var $ name ++ "_" ++ show index


-- >>> sugarVar (IndexedVar "x" 0)
-- Var {getVar = "x"}

-- >>> sugarVar (IndexedVar "x" 3)
-- Var {getVar = "x_3"}

consExp, nilExp, zeroExp, succExp, fixExp :: Exp
consExp = X (makeIndexedVar ":")  -- : :: a -> List a -> List a  list constructor
nilExp = X (makeIndexedVar "Nil") -- Nil :: List a               empty list
zeroExp = X (makeIndexedVar "Z")  -- Z :: Natural                zero
succExp = X (makeIndexedVar "S")  -- S :: Natural -> Natural     successor
fixExp = X (makeIndexedVar "fix") -- fix :: (a -> a) -> a        fixpoint fn.

-- CApp,CLam și CX se transformă în App,Lam, și respectiv X
-- listele se transformă în aplicări repetate ale lui:peste Nil
-- de exemplu,[a,b]se transformă în: a (: b Nil)
-- numerele naturale se transformă în aplicări repetate ale lui S peste Z
-- de exemplu,3 se transformă în S (S (S Z))
-- let x = ex in e se transformă în(\x -> e) ex
-- letrec f = ef in e se transformă în let f = fix (\f -> ef) in e, deci în(\f -> e)(fix (\f -> ef))
-- data ComplexExp                         --  ComplexExp ::= "(" ComplexExp ")"
--   = CX Var                              --          |   Var
--   | Nat Natural                           --        |   Natural
--   | CLam Var ComplexExp                 --          |   "\" Var "->" ComplexExp
--   | CApp ComplexExp ComplexExp          --          |   ComplexExp ComplexExp
--   | Let Var ComplexExp ComplexExp       --          |   "let" Var ":=" ComplexExp "in"
--   | LetRec Var ComplexExp ComplexExp    --          |   "letrec" Var ":=" ComplexExp "in"
--   | List [ComplexExp]                   --          |   "[" {ComplexExp ","}* "]"
--   deriving (Show)
-- data Exp
--   = X IndexedVar
--   | Lam IndexedVar Exp
--   | App Exp Exp
--   deriving (Show)

desugarExp :: ComplexExp -> Exp
desugarExp (CX var) = X (desugarVar var) 
desugarExp (Nat n) = foldr (\_ e -> App succExp e) zeroExp [1..n]
desugarExp (CLam v e) = Lam (desugarVar v) (desugarExp e)
desugarExp (CApp e1 e2) = App (desugarExp e1) (desugarExp e2)
desugarExp (Let v e1 e2) = App (Lam (desugarVar v) (desugarExp e2)) (desugarExp e1)
desugarExp (LetRec v e1 e2) = App (Lam (desugarVar v) (desugarExp e2)) (App fixExp (Lam (desugarVar v) (desugarExp e1)))
desugarExp (List es) = foldr (\e acc -> App (App consExp (desugarExp e)) acc) (X (makeIndexedVar "Nil")) es


-- >>> desugarExp (CApp (CLam (Var "x") (CX (Var "y"))) (CX (Var "z"))) 
-- App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "y", ivCount = 0}))) (X (IndexedVar {ivName = "z", ivCount = 0}))

-- >>> desugarExp (Nat 3)
-- App (X (IndexedVar {ivName = "S", ivCount = 0})) (App (X (IndexedVar {ivName = "S", ivCount = 0})) (App (X (IndexedVar {ivName = "S", ivCount = 0})) (X (IndexedVar {ivName = "Z", ivCount = 0}))))

-- >>> desugarExp (List [CX (Var "y"), CX (Var "x")])
-- App (App (X (IndexedVar {ivName = ":", ivCount = 0})) (X (IndexedVar {ivName = "y", ivCount = 0}))) (App (App (X (IndexedVar {ivName = ":", ivCount = 0})) (X (IndexedVar {ivName = "x", ivCount = 0}))) (X (IndexedVar {ivName = "Nil", ivCount = 0})))


-- >>> desugarExp (Let (Var "y") (CX (Var "x")) (CX (Var "z")))
-- App (Lam (IndexedVar {ivName = "y", ivCount = 0}) (X (IndexedVar {ivName = "z", ivCount = 0}))) (X (IndexedVar {ivName = "x", ivCount = 0}))

-- >>> desugarExp (LetRec (Var "y") (CX (Var "x")) (CX (Var "z")))
-- App (Lam (IndexedVar {ivName = "y", ivCount = 0}) (X (IndexedVar {ivName = "z", ivCount = 0}))) (App (X (IndexedVar {ivName = "fix", ivCount = 0})) (Lam (IndexedVar {ivName = "y", ivCount = 0}) (X (IndexedVar {ivName = "x", ivCount = 0}))))

sugarExp :: Exp -> ComplexExp
sugarExp (X x) = CX (sugarVar x)
sugarExp (Lam x e) = CLam (sugarVar x) (sugarExp e)
sugarExp (App e1 e2) = CApp (sugarExp e1) (sugarExp e2)
sugarExp (App (App (X (IndexedVar ":" _)) e1) e2) = List (sugarExp e1 : listExp e2)
    where listExp (App (App (X (IndexedVar ":" _)) e1) e2) = sugarExp e1 : listExp e2
          listExp (X (IndexedVar "Nil" _)) = []
          listExp e = error $ "sugarExp: not a list: " ++ show e
sugarExp (App (X (IndexedVar "fix" _)) (Lam x e)) = LetRec (sugarVar x) (sugarExp e) (CX (sugarVar x))
sugarExp (App (Lam x e) e2) = Let (sugarVar x) (sugarExp e2) (sugarExp e)
sugarExp (App e1 e2) = CApp (sugarExp e1) (sugarExp e2)
sugarExp e = error $ "sugarExp: not a complex expression: " ++ show e

-- >>> sugarExp (App (X (IndexedVar "x" 0)) (X (IndexedVar "y" 1)))
-- CApp (CX (Var {getVar = "x"})) (CX (Var {getVar = "y_1"}))

-- >>> sugarExp (App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "y", ivCount = 0}))) (X (IndexedVar {ivName = "z", ivCount = 0})))
-- (CApp (CLam (Var "x") (CX (Var "y"))) (CX (Var "z"))) 
