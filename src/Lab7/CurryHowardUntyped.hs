import Prelude (undefined)
import Distribution.Compat.Lens (_1)

newtype False = False { getFalse :: forall t. t }
newtype True = True { getTrue :: forall t . t -> t }
newtype And a b = And { getAnd :: forall t. (a -> b -> t) -> t }
newtype Or a b = Or { getOr :: forall t . (a -> t) -> (b -> t) -> t}
type Not a = a -> False
type Iff a b = And (a -> b) (b -> a)


-- Natural deduction introduction and elimination rules

trueIntro :: True                                   -- true introduction
trueIntro = True (\x -> x)

falseElim :: False -> b                             -- false elimination
falseElim f = getFalse f 

implIntro :: (a -> b) -> (a -> b)                   -- implication introduction
implIntro f x = f x

implElim :: (a -> b) -> a -> b                      -- implication elimination
implElim f x = f x

andIntro :: a -> b -> And a b                       -- and introduction
andIntro x y = And (\f -> f x y)

andElimL :: And a b -> a                            -- and elimination 1
andElimL (And f) = f (\x _ -> x)

andElimR :: And a b -> b                            -- and elimination 2
andElimR (And f) = f (\_ y -> y)

orIntroL :: a -> Or a b                             -- or introduction 1
orIntroL x = Or (\f _ -> f x)

orIntroR :: b -> Or a b                             -- or introduction 2
orIntroR y = Or (\_ f -> f y)

orElim :: Or a b -> (a -> c) -> (b -> c) -> c       -- or elimination
orElim (Or f) g h = f g h

notElim :: Not p -> p -> c                          -- not elimination 
notElim f x = case f x of

notIntro :: (forall p. a -> p) -> Not a             -- not introduction
notIntro f x = case f x of

iffIntro :: (a -> b) -> (b -> a) -> Iff a b         -- iff introduction
iffIntro f g = And (\x -> f x) (\y -> g y)

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
ax3 x y = And (\f -> f x y)

ax4 :: And a b -> a
ax4 (And f) = f (\x _ -> x)

ax5 :: And a b -> b
ax5 (And f) = f (\_ y -> y)

ax6 :: a -> Or a b
ax6 x = Or (\f _ -> f x)

ax7 :: b -> Or a b
ax7 y = Or (\_ f -> f y)

ax8 :: (a -> c) -> (b -> c) -> Or a b -> c
ax8 f g (Or h1 h2) = h1 f `orElim` g

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
deMorgan1 (And f) = \case
  Or g h -> f g `notElim` h

deMorgan2 :: Not (Or p q) -> And (Not p) (Not q)
deMorgan2 f = And (\x -> f (Or x (\_ -> undefined))) (\y -> f (Or (\_ -> undefined) y))

deMorgan3 :: Or (Not p) (Not q) -> Not (And p q)
deMorgan3 = \case
  Or f g -> \case
    And x y -> f x `notElim` g y

excludedMiddleImplDoubleNeg :: Or a (Not a) -> (Not (Not a) -> a)
excludedMiddleImplDoubleNeg = \case
  Or x _ -> \f -> x `notElim` f

doubleNegImplExcludedMiddle :: (forall a. Not (Not a) -> a) -> Or b (Not b)
doubleNegImplExcludedMiddle dn = Or (\x -> dn (\f -> x `notElim` f)) (\_ -> undefined)
