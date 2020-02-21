{-# Language AllowAmbiguousTypes #-}
-- | See the /connections/ package for idempotent & selective semirings, and lattices.
module Data.Semiring.Property (
  -- * Required properties of pre-semirings
    nonunital_on
  , morphism_presemiring
  , associative_addition_on
  , commutative_addition_on
  , associative_multiplication_on
  , distributive_on
  , distributive_finite1_on
  , morphism_distribitive_on
  -- * Required properties of semirings
  , morphism_semiring
  , neutral_addition_on
  , neutral_multiplication_on
  , annihilative_multiplication_on
  , distributive_finite_on
  -- * Left-distributive presemirings and semirings
  , distributive_xmult_on
  , distributive_xmult1_on
  -- * Commutative presemirings & semirings 
  , commutative_multiplication_on
  -- * Cancellative presemirings & semirings 
  , cancellative_addition_on 
  , cancellative_multiplication_on 
) where


import Data.Semiring
import Test.Logic (Rel)
import Data.Foldable (Foldable)
import Data.Functor.Apply (Apply)
import Data.Semigroup.Foldable (Foldable1)
import Data.Semigroup.Property
import qualified Test.Operation as Prop

import Prelude hiding (Num(..), sum)


------------------------------------------------------------------------------------
-- Required properties of pre-semirings & semirings

-- | \( \forall a, b \in R: a * b \sim a * b + b \)
--
-- If /R/ is non-unital (i.e. /one/ is not distinct from /zero/) then it will instead satisfy 
-- a right-absorbtion property. 
--
-- This follows from right-neutrality and right-distributivity.
--
-- When /R/ is also left-distributive we get: \( \forall a, b \in R: a * b = a + a * b + b \)
--
-- See also 'Data.Warning' and < https://blogs.ncl.ac.uk/andreymokhov/united-monoids/#whatif >.
--
nonunital_on :: Presemiring r => Rel r b -> r -> r -> b
nonunital_on (~~) a b = (a * b) ~~ (a * b + b)

-- | Presemiring morphisms are distributive semigroup morphisms.
--
-- This is a required property for presemiring morphisms.
--
morphism_presemiring :: Eq s => Presemiring r => Presemiring s => (r -> s) -> r -> r -> r -> Bool
morphism_presemiring f x y z =
  morphism_additive_on (==) f x y &&
  morphism_multiplicative_on (==) f x y &&
  morphism_distribitive_on (==) f x y z

------------------------------------------------------------------------------------
-- Required properties of semirings

-- | \( \forall a, b, c \in R: (a + b) * c \sim (a * c) + (b * c) \)
--
-- /R/ must right-distribute multiplication.
--
-- When /R/ is a functor and the semiring structure is derived from 'Control.Applicative.Alternative', 
-- this translates to: 
--
-- @
-- (a 'Control.Applicative.<|>' b) '*>' c = (a '*>' c) 'Control.Applicative.<|>' (b '*>' c)
-- @  
--
-- See < https://en.wikibooks.org/wiki/Haskell/Alternative_and_MonadPlus >.
--
-- This is a required property.
--
distributive_on :: Presemiring r => Rel r b -> r -> r -> r -> b
distributive_on (~~) = Prop.distributive_on (~~) (+) (*) 

-- | \( \forall M \geq 1; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b \sim \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication over finite (non-empty) sums.
--
-- For types with exact arithmetic this follows from 'distributive_on' and the universality of folds.
--
distributive_finite1_on :: Presemiring r => Foldable1 f => Rel r b -> f r -> r -> b
distributive_finite1_on (~~) as b = (sum1 as * b) ~~ (sumWith1 (* b) as)

-- | \( \forall a, b, c \in R: f ((a + b) * c) \sim f (a * c) + f (b * c) \)
-- 
-- Presemiring morphisms must be compatible with right-distribution.
--
morphism_distribitive_on :: Presemiring r => Presemiring s => Rel s b -> (r -> s) -> r -> r -> r -> b
morphism_distribitive_on (~~) f x y z = (f $ (x + y) * z) ~~ (f (x * z) + f (y * z))

------------------------------------------------------------------------------------
-- Required properties of semirings

-- | Semiring morphisms are monoidal presemiring morphisms.
--
-- This is a required property for semiring morphisms.
--
morphism_semiring :: Eq s => Semiring r => Semiring s => (r -> s) -> r -> r -> r -> Bool
morphism_semiring f x y z =
  morphism_presemiring f x y z &&
  morphism_additive_on' (==) f &&
  morphism_multiplicative_on' (==) f

-- | \( \forall a \in R: (z * a) \sim u \)
--
-- A /R/ is semiring then its addititive one must be right-annihilative, i.e.:
--
-- @
-- 'zero' '*' a = 'zero'
-- @
--
-- For 'Control.Applicative.Alternative' instances this property translates to:
--
-- @
-- 'Control.Applicative.empty' '*>' a = 'Control.Applicative.empty'
-- @
--
-- This is a required property.
--
annihilative_multiplication_on :: Semiring r => Rel r b -> r -> b
annihilative_multiplication_on (~~) r = Prop.annihilative_on (~~) (*) zero r

-- | \( \forall M \geq 0; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b \sim \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication between finite sums.
--
-- For types with exact arithmetic this follows from 'distributive_on' & 'Data.Semigroup.neutral_multiplication_on'.
--
distributive_finite_on :: Semiring r => Foldable f => Rel r b -> f r -> r -> b
distributive_finite_on (~~) as b = (sum as * b) ~~ (sumWith (* b) as)

------------------------------------------------------------------------------------
-- Left-distributive presemirings and semirings

-- | \( \forall M,N \geq 0; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) \sim \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports xmult-multiplication.
--
distributive_xmult_on :: Semiring r => Applicative f => Foldable f => Rel r b -> f r -> f r -> b
distributive_xmult_on (~~) as bs = (sum as * sum bs) ~~ (xmult as bs)

-- | \( \forall M,N \geq 1; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) = \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports (non-empty) xmult-multiplication.
--
distributive_xmult1_on :: Presemiring r => Apply f => Foldable1 f => Rel r b -> f r -> f r -> b
distributive_xmult1_on (~~) as bs = (sum1 as * sum1 bs) ~~ (xmult1 as bs)
