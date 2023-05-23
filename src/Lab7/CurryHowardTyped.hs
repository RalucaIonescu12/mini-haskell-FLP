import Prelude (undefined)

data False                                        -- empty type

data True = True                                  -- unit type

data And a b = And { proj1 :: a, proj2 :: b }     -- product

data Or a b                                       -- sum
  = Left a
  | Right b

type Not a = a -> False
type Iff a b = And (a -> b) (b -> a)

-- Natural deduction introduction and elimination rules

trueIntro :: True                                   -- true introduction
trueIntro = True

falseElim :: False -> b                             -- false elimination
falseElim x = case x of

implIntro :: (a -> b) -> (a -> b)                   -- implication introduction
implIntro f x = f x

implElim :: (a -> b) -> a -> b                      -- implication elimination
implElim f x = f x

andIntro :: a -> b -> And a b                       -- and introduction
andIntro x y = And x y

andElimL :: And a b -> a                            -- and elimination 1
andElimL (And x _) = x

andElimR :: And a b -> b                            -- and elimination 2
andElimR (And _ y) = y

orIntroL :: a -> Or a b                             -- or introduction 1
orIntroL x = Left x

orIntroR :: b -> Or a b                             -- or introduction 2
orIntroR y = Right y

orElim :: Or a b -> (a -> c) -> (b -> c) -> c       -- or elimination
orElim (Left x) f _ = f x
orElim (Right y) _ g = g y

notElim :: Not p -> p -> c                          -- not elimination 
notElim f x = case f x of

notIntro :: (forall p. a -> p) -> Not a             -- not introduction
notIntro f x = case f x of

iffIntro :: (a -> b) -> (b -> a) -> Iff a b         -- iff introduction
iffIntro f g = And f g

iffElimL :: Iff a b -> a -> b                       -- iff elimination 1
iffElimL (And f _) x = f x

iffElimR :: Iff a b -> b -> a                       -- iff elimination 1
iffElimR (And _ g) y = g y

-- Hilbert-style axiomatization for intuitionistic propositional logic

ax1 :: a -> b -> a
ax1 x _ = x

ax2 :: (a -> b) -> (a -> (b -> c)) -> a -> c
ax2 f g x = g x (f x)

ax3 :: a -> b -> And a b
ax3 x y = And x y

ax4 :: And a b -> a
ax4 (And x _) = x

ax5 :: And a b -> b
ax5 (And _ y) = y

ax6 :: a -> Or a b
ax6 x = Left x

ax7 :: b -> Or a b
ax7 y = Right y

ax8 :: (a -> c) -> (b -> c) -> Or a b -> c
ax8 f _ (Left x) = f x
ax8 _ g (Right y) = g y

ax9 :: (a -> b) -> (a -> Not b) -> Not a
ax9 f g x = g x (f x)

ax10 :: Not a -> a -> b
ax10 f x = case f x of

modusPonens :: (a -> b) -> a -> b
modusPonens f x = f x

-- Several tautologies

pNPFalse :: p -> Not p -> False
pNPFalse x f = f x

deMorgan1 :: And (Not p) (Not q) -> Not (Or p q)
deMorgan1 (And f g) = \case
  Left x -> f x
  Right y -> g y

deMorgan2 :: Not (Or p q) -> And (Not p) (Not q)
deMorgan2 f = And (\x -> f (Left x)) (\y -> f (Right y))

deMorgan3 :: Or (Not p) (Not q) -> Not (And p q)
deMorgan3 = \case
  Left f -> \case
    And x _ -> f x
  Right g -> \case
    And _ y -> g y

type DeMorgan4 = forall p q. Not (And p q) -> Or (Not p) (Not q)

-- Classical axioms

type ExcludedMiddle = forall a. Or a (Not a)
type DoubleNegation = forall a. Not (Not a) -> a
type PeirceLaw = forall p q. ((p -> q) -> p) -> p

excludedMiddleImplDoubleNeg :: ExcludedMiddle -> DoubleNegation
excludedMiddleImplDoubleNeg em f = case em of
  Left x -> x
  Right g -> f g

doubleNegImplExcludedMiddle :: DoubleNegation -> ExcludedMiddle
doubleNegImplExcludedMiddle dn = Right (dn (\x -> case x of))

classicDeMorgan4 :: ExcludedMiddle -> DeMorgan4
classicDeMorgan4 em f = case em of
  Left x -> Left (f x)
  Right g -> Right (f g)
