{-# Language AllowAmbiguousTypes #-}

module Data.Semiring.Property (
  -- * Properties of pre-semirings & semirings
    neutral_addition_on
  , neutral_addition_on'
  , neutral_multiplication_on
  , neutral_multiplication_on'
  , associative_addition_on 
  , associative_multiplication_on 
  , distributive_on 
  -- * Properties of non-unital (near-)semirings
  , nonunital_on
  -- * Properties of unital semirings
  , annihilative_multiplication_on 
  , homomorphism_boolean
  -- * Properties of cancellative semirings 
  , cancellative_addition_on 
  , cancellative_multiplication_on 
  -- * Properties of commutative semirings 
  , commutative_addition_on 
  , commutative_multiplication_on
  -- * Properties of distributive semirings 
  , distributive_finite_on
  , distributive_finite1_on 
  , distributive_cross_on
  , distributive_cross1_on 
{-
  -- * Properties of closed semirings
  , closed_pstable
  , closed_paffine 
  , closed_stable 
  , closed_affine 
  , idempotent_star
-}
) where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Foldable
import Data.Semiring
import Data.Semigroup.Foldable
import Test.Property.Util
import qualified Test.Property as Prop

------------------------------------------------------------------------------------
-- Properties of pre-semirings & semirings

-- | \( \forall a \in R: (z + a) \sim a \)
--
-- A (pre-)semiring with a right-neutral additive unit must satisfy:
--
-- @
-- 'neutral_addition' 'mempty' ~~ const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'mempty' '<>' r ~~ r
-- @
--
-- This is a required property.
--
neutral_addition_on :: Semigroup r => Rel r -> r -> r -> Bool
neutral_addition_on (~~) = Prop.neutral_on (~~) (<>)

neutral_addition_on' :: Monoid r => Rel r -> r -> Bool
neutral_addition_on' (~~) = Prop.neutral_on (~~) (<>) mempty

-- | \( \forall a \in R: (o * a) \sim a \)
--
-- A (pre-)semiring with a right-neutral multiplicative unit must satisfy:
--
-- @
-- 'neutral_multiplication' 'unit' ~~ const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'unit' '><' r ~~ r
-- @
--
-- This is a required property.
--
neutral_multiplication_on :: Semiring r => Rel r -> r -> r -> Bool
neutral_multiplication_on (~~) = Prop.neutral_on (~~) (><) 

neutral_multiplication_on' :: (Monoid r, Semiring r) => Rel r -> r -> Bool
neutral_multiplication_on' (~~) = Prop.neutral_on (~~) (><) unit

-- | \( \forall a, b, c \in R: (a + b) + c \sim a + (b + c) \)
--
-- /R/ must right-associate addition.
--
-- This should be verified by the underlying 'Semigroup' instance,
-- but is included here for completeness.
--
-- This is a required property.
--
associative_addition_on :: Semigroup r => Rel r -> r -> r -> r -> Bool
associative_addition_on (~~) = Prop.associative_on (~~) (<>)

-- | \( \forall a, b, c \in R: (a * b) * c \sim a * (b * c) \)
--
-- /R/ must right-associate multiplication.
--
-- This is a required property.
--
associative_multiplication_on :: Semiring r => Rel r -> r -> r -> r -> Bool
associative_multiplication_on (~~) = Prop.associative_on (~~) (><)

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
distributive_on :: Semiring r => Rel r -> r -> r -> r -> Bool
distributive_on (~~) = Prop.distributive_on (~~) (<>) (><)

------------------------------------------------------------------------------------
-- Properties of non-unital semirings (aka near-semirings)

-- | \( \forall a, b \in R: a * b \sim a * b + b \)
--
-- If /R/ is non-unital (i.e. /unit/ is not distinct from /mempty/) then it will instead satisfy 
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
nonunital_on :: (Monoid r, Semiring r) => Rel r -> r -> r -> Bool
nonunital_on (~~) a b = (a >< b) ~~ (a >< b <> b)


------------------------------------------------------------------------------------
-- Properties of unital semirings

-- | \( \forall a \in R: (z * a) \sim u \)
--
-- A /R/ is unital then its addititive unit must be right-annihilative, i.e.:
--
-- @
-- 'mempty' '><' a ~~ 'mempty'
-- @
--
-- For 'Alternative' instances this property translates to:
--
-- @
-- 'empty' '*>' a ~~ 'empty'
-- @
--
-- All right semirings must have a right-absorbative addititive unit,
-- however note that depending on the 'Prd' instance this does not preclude 
-- IEEE754-mandated behavior such as: 
--
-- @
-- 'mempty' '><' NaN ~~ NaN
-- @
--
-- This is a required property.
--
annihilative_multiplication_on :: (Monoid r, Semiring r) => Rel r -> r -> Bool
annihilative_multiplication_on (~~) r = Prop.annihilative_on (~~) (><) mempty r

-- | 'fromBoolean' must be a semiring homomorphism into /R/.
--
-- This is a required property.
--
homomorphism_boolean :: forall r. (Eq r, Monoid r, Semiring r) => Bool -> Bool -> Bool
homomorphism_boolean i j =
  fromBoolean True     == (unit @r)  &&
  fromBoolean False    == (mempty @r) &&
  fromBoolean (i && j) == fi >< fj    && 
  fromBoolean (i || j) == fi <> fj 

  where fi :: r = fromBoolean i
        fj :: r = fromBoolean j

------------------------------------------------------------------------------------
-- Properties of cancellative & commutative semirings


-- | \( \forall a, b, c \in R: b + a \sim c + a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt addition then for all /a/
-- the section /(a <>)/ is injective.
--
cancellative_addition_on :: Semigroup r => Rel r -> r -> r -> r -> Bool
cancellative_addition_on (~~) a = Prop.injective_on (~~) (<> a)


-- | \( \forall a, b, c \in R: b * a \sim c * a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt multiplication then for all /a/
-- the section /(a ><)/ is injective.
--
cancellative_multiplication_on :: Semiring r => Rel r -> r -> r -> r -> Bool
cancellative_multiplication_on (~~) a = Prop.injective_on (~~) (>< a)


-- | \( \forall a, b \in R: a + b \sim b + a \)
--
commutative_addition_on :: Semigroup r => Rel r -> r -> r -> Bool
commutative_addition_on (~~) = Prop.commutative_on (~~) (<>)


-- | \( \forall a, b \in R: a * b \sim b * a \)
--
commutative_multiplication_on :: Semiring r => Rel r -> r -> r -> Bool
commutative_multiplication_on (~~) = Prop.commutative_on (~~) (><)

------------------------------------------------------------------------------------
-- Properties of distributive & co-distributive semirings

-- | \( \forall M \geq 0; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b \sim \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication between finite sums.
--
-- For types with exact arithmetic this follows from 'distributive' & 'neutral_multiplication'.
--
distributive_finite_on :: (Monoid r, Semiring r) => Rel r -> [r] -> r -> Bool
distributive_finite_on (~~) as b = fold as >< b ~~ foldMap (>< b) as

-- | \( \forall M \geq 1; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b \sim \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication over finite (non-empty) sums.
--
-- For types with exact arithmetic this follows from 'distributive' and the universality of 'fold1'.
--
distributive_finite1_on :: (Semiring r) => Rel r -> NonEmpty r -> r -> Bool
distributive_finite1_on (~~) as b = fold1 as >< b ~~ foldMap1 (>< b) as

-- | \( \forall M,N \geq 0; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) \sim \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports cross-multiplication.
--
distributive_cross_on :: (Monoid r, Semiring r) => Rel r -> [r] -> [r] -> Bool
distributive_cross_on (~~) as bs = fold as >< fold bs ~~ cross as bs


-- | \( \forall M,N \geq 1; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) = \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports (non-empty) cross-multiplication.
--
distributive_cross1_on :: Semiring r => Rel r -> NonEmpty r -> NonEmpty r -> Bool
distributive_cross1_on (~~) as bs = fold1 as >< fold1 bs ~~ cross1 as bs

------------------------------------------------------------------------------------
-- Properties of closed semirings

{-
-- | \( 1 + \sum_{i=1}^{P+1} a^i = 1 + \sum_{i=1}^{P} a^i \)
--
-- If /a/ is p-stable for some /p/, then we have:
--
-- @
-- 'powers' p a ~~ a '><' 'powers' p a '<>' 'unit'  ~~ 'powers' p a '><' a '<>' 'unit' 
-- @
--
-- If '<>' and '><' are idempotent then every element is 1-stable:
--
-- @ a '><' a '<>' a '<>' 'unit' = a '<>' a '<>' 'unit' = a '<>' 'unit' @
--
closed_pstable :: (Eq r, Prd r, Monoid r, Semiring r) => Natural -> r -> Bool
closed_pstable p a = powers p a ~~ powers (p <> unit) a

-- | \( x = a * x + b \Rightarrow x = (1 + \sum_{i=1}^{P} a^i) * b \)
--
-- If /a/ is p-stable for some /p/, then we have:
--
closed_paffine :: (Prd r, Monoid r, Semiring r) => Natural -> r -> r -> Bool
closed_paffine p a b = closed_pstable p a ==> x ~~ a >< x <> b 
  where x = powers p a >< b

-- | \( \forall a \in R : a^* = a^* * a + 1 \)
--
-- Closure is /p/-stability for all /a/ in the limit as \( p \to \infinity \).
--
-- One way to think of this property is that all geometric series
-- "converge":
--
-- \( \forall a \in R : 1 + \sum_{i \geq 1} a^i \in R \)
--
closed_stable :: (Prd r, Monoid r, Closed r) => r -> Bool
closed_stable a = star a ~~ star a >< a <> unit

closed_stable' :: (Prd r, Monoid r, Closed r) => r -> Bool
closed_stable' a = star a ~~ unit <> a >< star a

closed_affine :: (Prd r, Monoid r, Closed r) => r -> r -> Bool
closed_affine a b = x ~~ a >< x <> b where x = star a >< b

-- If /R/ is closed then 'star' must be idempotent:
--
-- @'star' ('star' a) ~~ 'star' a@
--
idempotent_star :: (Prd r, Monoid r, Closed r) => r -> Bool
idempotent_star = Prop.idempotent star

-- If @r@ is a closed dioid then 'star' must be monotone:
--
-- @x '<~' y ==> 'star' x '<~' 'star' y@
--
monotone_star :: (Prd r, Monoid r, Closed r) => r -> r -> Bool
monotone_star = Prop.monotone_on (<~) star

-}
