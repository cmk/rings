{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE Safe #-}

module Data.Semiring.Module where

import safe Data.Distributive
import safe Data.Functor.Compose
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Functor.Rep
import safe Data.Semiring
import safe Data.Group
import safe Data.Ring
import safe Data.Prd
import safe Data.Tuple
import safe Prelude hiding (sum, negate)

-- | Free semimodule over a generating set.
--
-- See < https://en.wikipedia.org/wiki/Free_module > and < https://en.wikipedia.org/wiki/Semimodule >.
-- 
type Free f = (Foldable1 f, Representable f, Eq (Rep f))

lensRep :: Eq (Rep f) => Representable f => Rep f -> forall g. Functor g => (a -> g a) -> f a -> g (f a)
lensRep i f s = setter s <$> f (getter s)
  where getter = flip index i
        setter s' b = tabulate (\j -> if i == j then b else index s' j)
{-# INLINE lensRep #-}

grateRep :: Representable f => forall g. Functor g => (Rep f -> g a -> b) -> g (f a) -> f b
grateRep iab s = tabulate $ \i -> iab i (fmap (`index` i) s)
{-# INLINE grateRep #-}

-- | The zero vector.
--
fempty :: Monoid a => Representable f => f a
fempty = pureRep mempty
{-# INLINE fempty #-}

infixl 6 `sum`

-- | Sum of two vectors.
--
-- >>> V2 1 2 `sum` V2 3 4
-- V2 4 6
--
-- >>> V2 1 2 <> V2 3 4
-- V2 4 6
--
-- >>> V2 (V2 1 2) (V2 3 4) <> V2 (V2 1 2) (V2 3 4)
-- V2 (V2 2 4) (V2 6 8)
--
sum :: Semigroup a => Representable f => f a -> f a -> f a
sum = liftR2 (<>)
{-# INLINE sum #-}

infixl 6 `diff`

-- | Difference between two vectors.
--
-- >>> V2 4 5 `diff` V2 3 1
-- V2 1 4
--
-- >>> V2 4 5 << V2 3 1
-- V2 1 4
--
diff :: Group a => Representable f => f a -> f a -> f a
diff x y = x `sum` fmap negate y
{-# INLINE diff #-}

-- | Outer (tensor) product.
--
outer :: Semiring a => Functor f => Functor g => f a -> g a -> f (g a)
outer a b = fmap (\x->fmap (><x) b) a
{-# INLINE outer #-}

infixl 6 <.>

-- | Dot product.
--
(<.>) :: Semiring a => Free f => f a -> f a -> a
(<.>) a b = fold1 $ liftR2 (><) a b 
{-# INLINE (<.>) #-}

-- | Squared /l2/ norm of a vector.
--
quadrance :: Semiring a => Free f => f a -> a
quadrance f = f <.> f
{-# INLINE quadrance #-}

-- | Squared /l2/ norm of the difference between two vectors.
--
qd :: Ring a => Free f => f a -> f a -> a
qd f g = quadrance $ f `diff` g
{-# INLINE qd #-}

-- | Linearly interpolate between two vectors.
--
lerp :: Ring a => Representable f => a -> f a -> f a -> f a
lerp a f g = fmap (a ><) f `sum` fmap ((sunit << a) ><) g
{-# INLINE lerp #-}

-- | Dirac delta function.
--
dirac :: Eq i => Unital a => i -> i -> a
dirac i j = if i == j then sunit else mempty
{-# INLINE dirac #-}

-- | Create a unit vector.
--
-- >>> unit I21 :: V2 Int
-- V2 1 0
--
-- >>> unit I42 :: V4 Int
-- V4 0 1 0 0
--
unit :: Unital a => Free f => Rep f -> f a
unit i = tabulate $ dirac i
{-# INLINE unit #-}
