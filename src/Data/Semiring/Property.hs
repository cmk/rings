{-# Language AllowAmbiguousTypes #-}

module Data.Semiring.Property (
  -- * Properties of general pre-semirings & semirings
    neutral_addition_on
  , neutral_multiplication_on
  , associative_addition_on 
  , associative_multiplication_on
  , commutative_addition_on 
  , commutative_multiplication_on
  , distributive_on 
  , nonunital_on
  , annihilative_multiplication_on 
  -- * Properties of cancellative pre-semirings & semirings 
  , cancellative_addition_on 
  , cancellative_multiplication_on 
  -- * Properties of distributive pre-semirings & semirings 
  , distributive_finite_on
  , distributive_finite1_on 
  , distributive_cross_on
  , distributive_cross1_on 
) where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Semiring
import Test.Util
import Data.Semigroup.Additive
import Data.Semigroup.Multiplicative
import qualified Test.Function  as Prop
import qualified Test.Operation as Prop

import Prelude hiding (Num(..), sum)

------------------------------------------------------------------------------------
-- Properties of pre-semirings & semirings

-- | \( \forall a \in R: (z + a) \sim a \)
--
-- A (pre-)semiring with a right-neutral additive one must satisfy:
--
-- @
-- 'neutral_addition' 'zero' ~~ const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'zero' '+' r ~~ r
-- @
--
-- This is a required property.
--
neutral_addition_on :: (Additive-Monoid) r => Rel r -> r -> Bool
neutral_addition_on (~~) = Prop.neutral_on (~~) add zero

-- | \( \forall a \in R: (o * a) \sim a \)
--
-- A (pre-)semiring with a right-neutral multiplicative one must satisfy:
--
-- @
-- 'neutral_multiplication' 'one' ~~ const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'one' '*' r ~~ r
-- @
--
-- This is a required property.
--
neutral_multiplication_on :: (Multiplicative-Monoid) r => Rel r -> r -> Bool
neutral_multiplication_on (~~) = Prop.neutral_on (~~) mul one

-- | \( \forall a, b, c \in R: (a + b) + c \sim a + (b + c) \)
--
-- /R/ must right-associate addition.
--
-- This should be verified by the underlying 'Semigroup' instance,
-- but is included here for completeness.
--
-- This is a required property.
--
associative_addition_on :: (Additive-Semigroup) r => Rel r -> r -> r -> r -> Bool
associative_addition_on (~~) = Prop.associative_on (~~) add 

-- | \( \forall a, b, c \in R: (a * b) * c \sim a * (b * c) \)
--
-- /R/ must right-associate multiplication.
--
-- This is a required property.
--
associative_multiplication_on :: (Multiplicative-Semigroup) r => Rel r -> r -> r -> r -> Bool
associative_multiplication_on (~~) = Prop.associative_on (~~) mul 

-- | \( \forall a, b \in R: a + b \sim b + a \)
--
-- This is a required property.
--
commutative_addition_on :: (Additive-Semigroup) r => Rel r -> r -> r -> Bool
commutative_addition_on (~~) = Prop.commutative_on (~~) add 

-- | \( \forall a, b \in R: a * b \sim b * a \)
--
-- This is an /optional/ property.
--
commutative_multiplication_on :: (Multiplicative-Semigroup) r => Rel r -> r -> r -> Bool
commutative_multiplication_on (~~) = Prop.commutative_on (~~) mul 

-- | \( \forall a, b, c \in R: (a + b) * c \sim (a * c) + (b * c) \)
--
-- /R/ must right-distribute multiplication.
--
-- When /R/ is a functor and the semiring structure is derived from 'Alternative', 
-- this translates to: 
--
-- @
-- (a '<|>' b) '*>' c = (a '*>' c) '<|>' (b '*>' c)
-- @  
--
-- See < https://en.wikibooks.org/wiki/Haskell/Alternative_and_MonadPlus >.
--
-- This is a required property.
--
distributive_on :: PresemiringLaw r => Rel r -> r -> r -> r -> Bool
distributive_on (~~) = Prop.distributive_on (~~) add mul 

------------------------------------------------------------------------------------
-- Properties of non-unital semirings (aka near-semirings)

-- | \( \forall a, b \in R: a * b \sim a * b + b \)
--
-- If /R/ is non-unital (i.e. /one/ is not distinct from /zero/) then it will instead satisfy 
-- a right-absorbtion property. 
--
-- This follows from right-neutrality and right-distributivity.
--
-- Compare 'codistributive' and 'closed_stable'.
--
-- When /R/ is also left-distributive we get: \( \forall a, b \in R: a * b = a + a * b + b \)
--
-- See also 'Data.Warning' and < https://blogs.ncl.ac.uk/andreymokhov/united-monoids/#whatif >.
--
nonunital_on :: Presemiring r => Rel r -> r -> r -> Bool
nonunital_on (~~) a b = (a * b) ~~ (a * b + b)

------------------------------------------------------------------------------------
-- Properties of unital semirings

-- | \( \forall a \in R: (z * a) \sim u \)
--
-- A /R/ is unital then its addititive one must be right-annihilative, i.e.:
--
-- @
-- 'zero' '*' a ~~ 'zero'
-- @
--
-- For 'Alternative' instances this property translates to:
--
-- @
-- 'empty' '*>' a ~~ 'empty'
-- @
--
-- All right semirings must have a right-absorbative addititive one,
-- however note that depending on the 'Prd' instance this does not preclude 
-- IEEE754-mandated behavior such as: 
--
-- @
-- 'zero' '*' NaN ~~ NaN
-- @
--
-- This is a required property.
--
annihilative_multiplication_on :: Semiring r => Rel r -> r -> Bool
annihilative_multiplication_on (~~) r = Prop.annihilative_on (~~) (*) zero r

{-
-- | 'fromBoolean' must be a semiring homomorphism into /R/.
--
-- This is a required property.
--
homomorphism_boolean :: forall r. (Eq r, Unital r) => Bool -> Bool -> Bool
homomorphism_boolean i j =
  fromBoolean True     == (one @r)  &&
  fromBoolean False    == (zero @r) &&
  fromBoolean (i && j) == fi * fj    && 
  fromBoolean (i || j) == fi + fj 

  where fi :: r = fromBoolean i
        fj :: r = fromBoolean j
-}

------------------------------------------------------------------------------------
-- Properties of cancellative semirings

-- | \( \forall a, b, c \in R: b + a \sim c + a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt addition then for all /a/
-- the section /(a +)/ is injective.
--
cancellative_addition_on :: (Additive-Semigroup) r => Rel r -> r -> r -> r -> Bool
cancellative_addition_on (~~) a = Prop.injective_on (~~) (`add` a)

-- | \( \forall a, b, c \in R: b * a \sim c * a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt multiplication then for all /a/
-- the section /(a *)/ is injective.
--
cancellative_multiplication_on :: (Multiplicative-Semigroup) r => Rel r -> r -> r -> r -> Bool
cancellative_multiplication_on (~~) a = Prop.injective_on (~~) (`mul` a)

------------------------------------------------------------------------------------
-- Properties of distributive & co-distributive semirings

-- | \( \forall M \geq 0; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b \sim \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication between finite sums.
--
-- For types with exact arithmetic this follows from 'distributive' & 'neutral_multiplication'.
--
distributive_finite_on :: Semiring r => Rel r -> [r] -> r -> Bool
distributive_finite_on (~~) as b = (sum as * b) ~~ (sumWith (* b) as)

-- | \( \forall M \geq 1; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b \sim \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication over finite (non-empty) sums.
--
-- For types with exact arithmetic this follows from 'distributive' and the universality of 'fold1'.
--
distributive_finite1_on :: Presemiring r => Rel r -> NonEmpty r -> r -> Bool
distributive_finite1_on (~~) as b = (sum1 as * b) ~~ (sumWith1 (* b) as)

-- | \( \forall M,N \geq 0; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) \sim \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports cross-multiplication.
--
distributive_cross_on :: Semiring r => Rel r -> [r] -> [r] -> Bool
distributive_cross_on (~~) as bs = (sum as * sum bs) ~~ (cross as bs)

-- | \( \forall M,N \geq 1; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) = \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports (non-empty) cross-multiplication.
--
distributive_cross1_on :: Presemiring r => Rel r -> NonEmpty r -> NonEmpty r -> Bool
distributive_cross1_on (~~) as bs = (sum1 as * sum1 bs) ~~ (cross1 as bs)
