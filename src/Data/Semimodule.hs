{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
-- {-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE StandaloneDeriving         #-}
-- | < https://ncatlab.org/nlab/show/module >
module Data.Semimodule (
  -- * Left modules
    type LeftModule
  , LeftSemimodule(..)
  , (*.)
  , lerp
  , (*^)
  , (/^)
  , negateDef
  -- * Right modules
  , type RightModule
  , RightSemimodule(..)
  , (.*)
  , (^*)
  , (^/)
  -- * Bimodules
  , type Bimodule
  , Bisemimodule(..)
) where

import safe Control.Applicative
import safe Control.Category ((<<<), (>>>))
import safe Data.Bool
import safe Data.Complex
import safe Data.Functor.Alt
import safe Data.Functor.Contravariant
import safe Data.Int
import safe Data.Monoid hiding (Alt(..), Sum(..), Product(..))
import safe Data.Ring
import safe Data.Semiring
import safe Data.Semigroup.Additive
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..))
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)

-------------------------------------------------------------------------------
-- Left modules
-------------------------------------------------------------------------------

type LeftModule l a = (Ring l, (Additive-Group) a, LeftSemimodule l a)

-- | < https://en.wikipedia.org/wiki/Semimodule Left semimodule > over a commutative monoid.
--
-- All instances must satisfy the following identities:
-- 
-- @
-- 'lscale' s (x '+' y) = 'lscale' s x '+' 'lscale' s y
-- 'lscale' (s1 '+' s2) x = 'lscale' s1 x '+' 'lscale' s2 x
-- 'lscale' (s1 '*' s2) = 'lscale' s1 . 'lscale' s2
-- 'lscale' 'zero' = 'const' 'zero'
-- 'lscale' 'one' = 'id'
-- @
-- 
class (Semiring l, (Additive-Monoid) a) => LeftSemimodule l a where

  -- | Left-multiply by a scalar.
  --
  lscale :: l -> a -> a

infixr 7 *., *^, /^

-- | Left-multiply a module element by a scalar.
--
(*.) :: LeftSemimodule l a => l -> a -> a
(*.) = lscale

-- | Default definition of 'lscale' for a free semimodule.
--
(*^) :: (Semiring a, Functor f) => a -> f a -> f a
(*^) a f = (a *) <$> f

-- | Right-divide a vector by a scalar (on the left).
--
(/^) :: (Semifield a, Functor f) => a -> f a -> f a
a /^ f = (/ a) <$> f

-- | Linearly interpolate between two vectors.
--
-- >>> u = V3 (1 :% 1) (2 :% 1) (3 :% 1) :: V3 Rational
-- >>> v = V3 (2 :% 1) (4 :% 1) (6 :% 1) :: V3 Rational
-- >>> r = 1 :% 2 :: Rational
-- >>> lerp r u v
-- V3 (6 % 4) (12 % 4) (18 % 4)
--
lerp :: LeftModule r a => r -> a -> a -> a
lerp r f g = r *. f + (one - r) *. g

-- | Default negation for a commutative group.
--
negateDef :: LeftModule Integer a => a -> a
negateDef a = negate @Integer one *. a

-------------------------------------------------------------------------------
-- Right modules
-------------------------------------------------------------------------------

type RightModule r a = (Ring r, (Additive-Group) a, RightSemimodule r a)

-- | < https://en.wikipedia.org/wiki/Semimodule Right semimodule > over a commutative monoid.
--
-- The laws for right semimodules are analagous to those of left semimodules.
--
class (Semiring r, (Additive-Monoid) a) => RightSemimodule r a where

  -- | Right-multiply by a scalar.
  --
  rscale :: r -> a -> a

infixl 7 .*, ^*, ^/

-- | Right-multiply a module element by a scalar.
--
(.*) :: RightSemimodule r a => a -> r -> a
(.*) = flip rscale

-- | Default definition of 'rscale' for a free semimodule.
--
(^*) :: (Semiring a, Functor f) => a -> f a -> f a
(^*) a f = (* a) <$> f

-- | Right-divide a vector by a scalar.
--
(^/) :: (Semifield a, Functor f) => f a -> a -> f a
(^/) = flip (/^)

-------------------------------------------------------------------------------
-- Bimodules
-------------------------------------------------------------------------------

type Bimodule l r a = (LeftModule l a, RightModule r a, Bisemimodule l r a)

-- | < https://en.wikipedia.org/wiki/Bimodule Bisemimodule > over a commutative monoid.
--
-- Note that left and right multiplications must be compatible:
-- @
-- 'lscale' l . 'rscale' r = 'rscale' r . 'lscale' l
-- @
--
class (LeftSemimodule l a, RightSemimodule r a) => Bisemimodule l r a where

  -- | Left and right-multiply by two scalars.
  --
  discale :: l -> r -> a -> a
  discale l r = lscale l . rscale r

-------------------------------------------------------------------------------
-- Module Instances
-------------------------------------------------------------------------------



--instance (Alternative f, LeftSemimodule l a) => LeftSemimodule l (A1 f a) where
--  lscale l = fmap (l *.)

--deriving via (Co ((->)e) a) instance LeftSemimodule l a => LeftSemimodule l (e -> a)
--deriving via (A1 (Map.Map k) a) instance LeftSemimodule l a => LeftSemimodule l (Map.Map k a)
--instance Semiring a => LeftSemimodule b (Map.Map a b) where scale b = fmap (b <.>)

instance LeftSemimodule l a => RightSemimodule (Dual l) a where
  rscale (Dual l) = lscale l
instance LeftSemimodule l a => Bisemimodule l (Dual l) a


instance Semiring a => LeftSemimodule a a where
  lscale = (*)
instance Semiring a => RightSemimodule a a where
  rscale = (*)
instance Semiring a => Bisemimodule a a a


instance Semiring l => LeftSemimodule l () where
  lscale _ = const ()
instance Semiring r => RightSemimodule r () where
  rscale _ = const ()
instance (Semiring l, Semiring r) => Bisemimodule l r ()


-- > LeftSemimodule Bool (Predicate a)
--
instance Monoid (Additive a) => LeftSemimodule Bool a where
  lscale l x = bool zero x l
instance Monoid (Additive a) => RightSemimodule Bool a where
  rscale r x = bool zero x r
instance Monoid (Additive a) => Bisemimodule Bool Bool a


instance Monoid (Additive a) => LeftSemimodule Natural a where
  lscale l x = getAdd $ mreplicate l (Add x)
instance Monoid (Additive a) => RightSemimodule Natural a where
  rscale r x = getAdd $ mreplicate r (Add x)
instance Monoid (Additive a) => Bisemimodule Natural Natural a


instance (Monoid (Additive a), Group (Additive a)) => LeftSemimodule Integer a where
  lscale l x = getAdd $ pow (Add x) l
instance (Monoid (Additive a), Group (Additive a)) => RightSemimodule Integer a where
  rscale r x = getAdd $ pow (Add x) r
instance (Monoid (Additive a), Group (Additive a)) => Bisemimodule Integer Integer a


instance Semiring a => LeftSemimodule a (Ratio a) where 
  lscale l (x :% y) = (l * x) :% y
instance Semiring a => RightSemimodule a (Ratio a) where 
  rscale r (x :% y) = (r * x) :% y
instance Semiring a => Bisemimodule a a (Ratio a)


instance Ring a => LeftSemimodule a (Complex a) where 
  lscale = (*^)
instance Ring a => RightSemimodule a (Complex a) where 
  rscale = (^*)
instance Ring a => Bisemimodule a a (Complex a)


instance LeftSemimodule l a => LeftSemimodule l (Endo2 a) where
  lscale l (Endo f) = Endo $ \e -> Endo $ \a -> lscale l (appEndo (f e) a)
instance RightSemimodule r a => RightSemimodule r (Endo2 a) where
  rscale r (Endo f) = Endo $ \e -> Endo $ \a -> rscale r (appEndo (f e) a)
instance Bisemimodule l r a => Bisemimodule l r (Endo2 a)


instance LeftSemimodule l a => LeftSemimodule l (i -> a) where
  lscale l = fmap (l *.)
instance RightSemimodule r a => RightSemimodule r (i -> a) where
  rscale r = fmap (.* r)
instance Bisemimodule l r a => Bisemimodule l r (i -> a)


instance LeftSemimodule l a => LeftSemimodule l (Op a e) where 
  lscale l (Op f) = Op $ fmap (l *.) f
instance RightSemimodule r a => RightSemimodule r (Op a e) where 
  rscale r (Op f) = Op $ fmap (.* r) f
instance Bisemimodule l r a => Bisemimodule l r (Op a e)


instance (LeftSemimodule l a, LeftSemimodule l b) => LeftSemimodule l (a, b) where
  lscale n (a, b) = (n *. a, n *. b)
instance (RightSemimodule r a, RightSemimodule r b) => RightSemimodule r (a, b) where
  rscale n (a, b) = (a .* n, b .* n)
instance (Bisemimodule l r a, Bisemimodule l r b) => Bisemimodule l r (a, b)


instance (LeftSemimodule l a, LeftSemimodule l b, LeftSemimodule l c) => LeftSemimodule l (a, b, c) where
  lscale n (a, b, c) = (n *. a, n *. b, n *. c)
instance (RightSemimodule r a, RightSemimodule r b, RightSemimodule r c) => RightSemimodule r (a, b, c) where
  rscale n (a, b, c) = (a .* n, b .* n, c .* n)
instance (Bisemimodule l r a, Bisemimodule l r b, Bisemimodule l r c) => Bisemimodule l r (a, b, c)


{-
deriving via (Alt [] a) instance LeftSemimodule Natural [a]

instance Semiring a => LeftSemimodule a (Commutative a) where
  lscale = (*^)

instance Alternative f => LeftSemimodule Natural (Alt f a) where
  lscale = mreplicate

instance (Representable f, LeftSemimodule l a) => LeftSemimodule l (Co f a) where
  lscale l = fmap (l *.)

instance LeftSemimodule Natural [a] where
  lscale l x = getAlt $ mreplicate l (Alt x)
  A1 x * A1 y = A1 $ liftF2 (<>) x y
  A1 x + A1 y = A1 $  x <!> y

--instance Ord a => LeftSemimodule Bool (Set.Set a) where
--  lscale b f = bool zero f b

instance Semiring a => LeftSemimodule a (Op a e) where 
  lscale l (Op f) = Op $ fmap (l *) f

instance Semiring a => RightSemimodule a (Op a e) where 
  rscale r (Op f) = Op $ fmap (* r) f

instance Semiring a => Bisemimodule a a (Op a e)
-}



