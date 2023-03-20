
module Eval where

import Exp
import Data.List ( union, delete )

-- newtype Var = Var { getVar :: String }
--   deriving (Show)

-- data ComplexExp                         --  ComplexExp ::= "(" ComplexExp ")"
--   = CX Var                              --          |   Var
--   | Nat Natural                           --        |   Natural
--   | CLam Var ComplexExp                 --          |   "\" Var "->" ComplexExp
--   | CApp ComplexExp ComplexExp          --          |   ComplexExp ComplexExp
--   | Let Var ComplexExp ComplexExp       --          |   "let" Var ":=" ComplexExp "in"
--   | LetRec Var ComplexExp ComplexExp    --          |   "letrec" Var ":=" ComplexExp "in"
--   | List [ComplexExp]                   --          |   "[" {ComplexExp ","}* "]"
--   deriving (Show)


-- data IndexedVar = IndexedVar
--   { ivName :: String
--   , ivCount :: Int
--   } deriving (Eq, Read, Show)

-- makeIndexedVar :: String -> IndexedVar
-- makeIndexedVar name = IndexedVar name 0

-- data Exp
--   = X IndexedVar
--   | Lam IndexedVar Exp
--   | App Exp Exp
--   deriving (Show)


vars :: Exp -> [IndexedVar]
vars (X indexedVar) = [indexedVar]
vars (Lam indexedVar exp) = indexedVar : vars exp
vars (App exp1 exp2) = vars exp1 ++ vars exp2

  
-- >>> vars (Lam (makeIndexedVar "x") (X (makeIndexedVar "y"))) == [IndexedVar {ivName = "x", ivCount = 0},IndexedVar {ivName = "y", ivCount = 0}]

-- >>> vars (App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "y", ivCount = 0}))) (X (IndexedVar {ivName = "z", ivCount = 0})))
-- [IndexedVar {ivName = "x", ivCount = 0},IndexedVar {ivName = "y", ivCount = 0},IndexedVar {ivName = "z", ivCount = 0}]

-- >>> vars (App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "x", ivCount = 0}))) (X (IndexedVar {ivName = "x", ivCount = 0})))
-- [IndexedVar {ivName = "x", ivCount = 0}]

freeVars :: Exp -> [IndexedVar]
freeVars exp = filter (not . isBound exp) (vars exp)
  where
    isBound (Lam iv _) iv' = iv == iv'
    isBound _ _ = False

-- >>> freeVars (Lam (makeIndexedVar "x") (X (makeIndexedVar "y")))
-- [IndexedVar {ivName = "y", ivCount = 0}]

-- >>> freeVars  (App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "y", ivCount = 0}))) (X (IndexedVar {ivName = "z", ivCount = 0})))
-- [IndexedVar {ivName = "y", ivCount = 0},IndexedVar {ivName = "z", ivCount = 0}]

-- >>> freeVars (App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "x", ivCount = 0}))) (X (IndexedVar {ivName = "x", ivCount = 0})))
-- [IndexedVar {ivName = "x", ivCount = 0}]

-- >>> freeVars (Lam (IndexedVar {ivName = "x", ivCount = 0}) (App (X (IndexedVar {ivName = "x", ivCount = 0})) (X (IndexedVar {ivName = "x", ivCount = 0}))))
-- []

occursFree :: IndexedVar -> Exp -> Bool
occursFree var (X v) = var == v
occursFree var (Lam v exp) = var /= v && occursFree var exp
occursFree var (App exp1 exp2) = occursFree var exp1 || occursFree var exp2
-- >>> makeIndexedVar "x" `occursFree` Lam (makeIndexedVar "x") (X (makeIndexedVar "y"))
-- False

-- >>> makeIndexedVar "y" `occursFree` Lam (makeIndexedVar "x") (X (makeIndexedVar "y"))
-- True

freshVar :: IndexedVar -> [IndexedVar] -> IndexedVar
freshVar iv [] = iv
freshVar iv (iv':ivs)
  | iv == iv' = freshVar (incrementCount iv) ivs
  | otherwise = freshVar iv ivs
  where
    incrementCount (IndexedVar name count) = IndexedVar name (count + 1)


-- >>> freshVar (makeIndexedVar "x") [makeIndexedVar "x"]
-- IndexedVar {ivName = "x", ivCount = 1}

-- >>> freshVar (makeIndexedVar "x") [makeIndexedVar "x", IndexedVar {ivName = "x", ivCount = 1}, IndexedVar {ivName = "y", ivCount = 2}] 
-- IndexedVar {ivName = "x", ivCount = 2}

renameVar :: IndexedVar -> IndexedVar -> Exp -> Exp
renameVar toReplace replacement (X v)
  | toReplace == v = X replacement
  | otherwise = X v
renameVar toReplace replacement (Lam v e)
  | toReplace == v = Lam replacement (renameVar toReplace replacement e)
  | otherwise = Lam v (renameVar toReplace replacement e)
renameVar toReplace replacement (App e1 e2) =
  App (renameVar toReplace replacement e1) (renameVar toReplace replacement e2)
-- >>> renameVar (IndexedVar {ivName = "x", ivCount = 0}) (IndexedVar {ivName = "z", ivCount = 0}) (App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "x", ivCount = 0}))) (X (IndexedVar {ivName = "x", ivCount = 0})))
-- App (Lam (IndexedVar {ivName = "z", ivCount = 0}) (X (IndexedVar {ivName = "z", ivCount = 0}))) (X (IndexedVar {ivName = "z", ivCount = 0}))

substitute :: IndexedVar -> Exp -> Exp -> Exp
substitute toReplace replacement (X v)
    | v == toReplace = replacement
    | otherwise = X v
substitute toReplace replacement (App e1 e2) = App (substitute toReplace replacement e1) (substitute toReplace replacement e2)
substitute toReplace replacement (Lam v e)
    | v == toReplace = Lam v e
    | v `occursFree` replacement = substitute toReplace replacement (Lam newVar (renameVar v newVar e))
    | otherwise = Lam v (substitute toReplace replacement e)
    where newVar = freshVar v (freeVars replacement ++ freeVars e)  


-- >>> substitute (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "z", ivCount = 0})) (App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "x", ivCount = 0}))) (X (IndexedVar {ivName = "x", ivCount = 0})))
-- App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "x", ivCount = 0}))) (X (IndexedVar {ivName = "z", ivCount = 0}))

-- >>> substitute (IndexedVar {ivName = "y", ivCount = 0}) (X (IndexedVar {ivName = "x", ivCount = 0})) (App (Lam (IndexedVar {ivName = "x", ivCount = 0}) (X (IndexedVar {ivName = "y", ivCount = 0}))) (X (IndexedVar {ivName = "z", ivCount = 0})))
-- App (Lam (IndexedVar {ivName = "x", ivCount = 1}) (X (IndexedVar {ivName = "x", ivCount = 0}))) (X (IndexedVar {ivName = "z", ivCount = 0}))

normalize :: Exp -> Exp
normalize  e = maybe e normalize (step e)
    where 
            step (X x) = Nothing
            step (Lam x e) = Lam x <$> step e
            step (App (Lam x ex) e) = Just (substitute x e ex)
            step (App e1 e2) = 
                case step e1 of 
                    Nothing -> App e1 <$> step e2
                    Just e1' -> Just (App e1' e2)
-- >>> normalize (X (makeIndexedVar "x"))
-- X (IndexedVar {ivName = "x", ivCount = 0})

-- >>> normalize (App (Lam (IndexedVar {ivName = "y", ivCount = 0}) (X (IndexedVar {ivName = "x", ivCount = 0}))) (App (Lam (IndexedVar {ivName = "y", ivCount = 0}) (App (X (IndexedVar {ivName = "y", ivCount = 0})) (X (IndexedVar {ivName = "y", ivCount = 0})))) (Lam (IndexedVar {ivName = "y", ivCount = 0}) (App (X (IndexedVar {ivName = "y", ivCount = 0})) (X (IndexedVar {ivName = "y", ivCount = 0}))))))
-- X (IndexedVar {ivName = "x", ivCount = 0})
