{-# Language AllowAmbiguousTypes #-}
{-# LANGUAGE Safe #-}

module Data.Semigroup.Property (
  -- * Required properties of semigroups
    associative_addition_on 
  , associative_multiplication_on
  -- * Required properties of monoids
  , neutral_addition_on
  , neutral_multiplication_on
  -- * Properties of commuative semigroups
  , commutative_addition_on 
  , commutative_multiplication_on
  -- * Properties of cancellative semigroups
  , cancellative_addition_on
  , cancellative_multiplication_on
  -- * Properties of idempotent semigroups
  , idempotent_addition_on
  , idempotent_multiplication_on
  -- * Required properties of semigroup & monoid morphisms
  , morphism_additive_on
  , morphism_multiplicative_on
  , morphism_additive_on'
  , morphism_multiplicative_on'
) where


import safe Test.Logic (Rel)
import safe Data.Semigroup.Additive
import safe qualified Test.Function  as Prop
import safe qualified Test.Operation as Prop hiding (distributive_on)

import safe Prelude hiding (Num(..), sum)


------------------------------------------------------------------------------------
-- Required properties of semigroups

-- | \( \forall a, b, c \in R: (a + b) + c \sim a + (b + c) \)
--
-- All semigroups must right-associate addition.
--
-- This is a required property.
--
associative_addition_on :: (Additive-Semigroup) r => Rel r b -> r -> r -> r -> b
associative_addition_on (~~) = Prop.associative_on (~~) (+) 

-- | \( \forall a, b, c \in R: (a * b) * c \sim a * (b * c) \)
--
-- All semigroups must right-associate multiplication.
--
-- This is a required property.
--
associative_multiplication_on :: (Multiplicative-Semigroup) r => Rel r b -> r -> r -> r -> b
associative_multiplication_on (~~) = Prop.associative_on (~~) (*) 

------------------------------------------------------------------------------------
-- Required properties of monoids

-- | \( \forall a \in R: (z + a) \sim a \)
--
-- A semigroup with a right-neutral additive identity must satisfy:
--
-- @
-- 'neutral_addition' 'zero' = const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'zero' '+' r = r
-- @
--
-- This is a required property for additive monoids.
--
neutral_addition_on :: (Additive-Monoid) r => Rel r b -> r -> b
neutral_addition_on (~~) = Prop.neutral_on (~~) (+) zero

-- | \( \forall a \in R: (o * a) \sim a \)
--
-- A semigroup with a right-neutral multiplicative identity must satisfy:
--
-- @
-- 'neutral_multiplication' 'one' = const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'one' '*' r = r
-- @
--
-- This is a required propert for multiplicative monoids.
--
neutral_multiplication_on :: (Multiplicative-Monoid) r => Rel r b -> r -> b
neutral_multiplication_on (~~) = Prop.neutral_on (~~) (*) one

------------------------------------------------------------------------------------
-- Properties of commutative semigroups

-- | \( \forall a, b \in R: a + b \sim b + a \)
--
-- This is a an /optional/ property for semigroups, and a /required/ property for semirings.
--
commutative_addition_on :: (Additive-Semigroup) r => Rel r b -> r -> r -> b
commutative_addition_on (~~) = Prop.commutative_on (~~) (+) 

-- | \( \forall a, b \in R: a * b \sim b * a \)
--
-- This is a an /optional/ property for semigroups, and a /optional/ property for semirings.
-- It is a /required/ property for rings.
--
commutative_multiplication_on :: (Multiplicative-Semigroup) r => Rel r b -> r -> r -> b
commutative_multiplication_on (~~) = Prop.commutative_on (~~) (*) 

------------------------------------------------------------------------------------
-- Properties of cancellative semigroups

-- | \( \forall a, b, c \in R: b + a \sim c + a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt addition then for all /a/
-- the section /(a +)/ is injective.
--
-- See < https://en.wikipedia.org/wiki/Cancellation_property >
--
cancellative_addition_on :: (Additive-Semigroup) r => Rel r Bool -> r -> r -> r -> Bool
cancellative_addition_on (~~) a = Prop.injective_on (~~) (+ a)

-- | \( \forall a, b, c \in R: b * a \sim c * a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt multiplication then for all /a/
-- the section /(a *)/ is injective.
--
cancellative_multiplication_on :: (Multiplicative-Semigroup) r => Rel r Bool -> r -> r -> r -> Bool
cancellative_multiplication_on (~~) a = Prop.injective_on (~~) (* a)

------------------------------------------------------------------------------------
-- Properties of idempotent semigroups

-- | Idempotency property for additive semigroups.
--
-- @ 'idempotent_addition' = 'absorbative_addition' 'one' @
-- 
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a required property for lattices.
--
idempotent_addition_on :: (Additive-Semigroup) r => Rel r b -> r -> b
idempotent_addition_on (~~) r = (r + r) ~~ r

-- | Idempotency property for multplicative semigroups.
--
-- @ 'idempotent_multiplication' = 'absorbative_multiplication' 'zero' @
-- 
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a an /optional/ property for semigroups, and a /optional/ property for semirings.
--
-- This is a /required/ property for lattices.
--
idempotent_multiplication_on :: (Multiplicative-Semigroup) r => Rel r b -> r -> b
idempotent_multiplication_on (~~) r = (r * r) ~~ r

------------------------------------------------------------------------------------
-- Properties of semigroup morphisms

morphism_additive_on :: (Additive-Semigroup) r => (Additive-Semigroup) s => Rel s b -> (r -> s) -> r -> r -> b
morphism_additive_on (~~) f x y = (f $ x + y) ~~ (f x + f y)

morphism_multiplicative_on :: (Multiplicative-Semigroup) r => (Multiplicative-Semigroup) s => Rel s b -> (r -> s) -> r -> r -> b
morphism_multiplicative_on (~~) f x y = (f $ x * y) ~~ (f x * f y)

morphism_additive_on' :: (Additive-Monoid) r => (Additive-Monoid) s => Rel s b -> (r -> s) -> b
morphism_additive_on' (~~) f = (f zero) ~~ zero

morphism_multiplicative_on' :: (Multiplicative-Monoid) r => (Multiplicative-Monoid) s => Rel s b -> (r -> s) -> b
morphism_multiplicative_on' (~~) f = (f one) ~~ one

{-
morphism_additive_on :: (Additive-Semigroup) r => (Additive-Semigroup) s => Rel s b -> (r -> s) -> r -> r -> b
morphism_additive_on (~~) f x y = (f $ x `add` y) ~~ (f x `add` f y)

morphism_multiplicative_on :: (Multiplicative-Semigroup) r => (Multiplicative-Semigroup) s => Rel s b -> (r -> s) -> r -> r -> b
morphism_multiplicative_on (~~) f x y = (f $ x `mul` y) ~~ (f x `mul` f y)

morphism_additive_on' :: (Additive-Monoid) r => (Additive-Monoid) s => Rel s b -> (r -> s) -> b
morphism_additive_on' (~~) f = (f zero) ~~ zero

morphism_multiplicative_on' :: (Multiplicative-Monoid) r => (Multiplicative-Monoid) s => Rel s b -> (r -> s) -> b
morphism_multiplicative_on' (~~) f = (f one) ~~ one


-- | \( \forall a, b \in R: a * b \sim b * a \)
--
-- This is a an /optional/ property for semigroups, and a /optional/ property for semirings.
-- It is a /required/ property for rings.
--
commutative_multiplication_on :: (Multiplicative-Semigroup) r => Rel r b -> r -> r -> b
commutative_multiplication_on (~~) = Prop.commutative_on (~~) mul 

-}



