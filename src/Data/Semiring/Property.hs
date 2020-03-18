{-# Language AllowAmbiguousTypes #-}
{-# LANGUAGE Safe #-}

-- | See the /connections/ package for idempotent & selective semirings, and lattices.
module Data.Semiring.Property (
  -- * Generic properties of arithmetic operators
    neutral
  , neutral'
  , associative
  , annihilative
  , annihilative'
  , commutative
  , distributive
  , distributive'
  -- * Required properties of pre-semirings
  , nonunital
  , morphism_presemiring
  , associative_addition
  , commutative_addition
  , associative_multiplication
  , distributive_addition
  , distributive_finite1
  , morphism_additive
  , morphism_multiplicative
  , morphism_distribitive
  -- * Required properties of semirings
  , neutral_addition
  , neutral_multiplication
  , annihilative_multiplication
  , distributive_finite
  , morphism_additive'
  , morphism_multiplicative'
  , morphism_semiring
  -- * Left-distributive presemirings and semirings
  , distributive_xmult
  , distributive_xmult1
  -- * Commutative presemirings & semirings 
  , commutative_multiplication
  -- * Cancellative presemirings & semirings 
  , cancellative_addition 
  , cancellative_multiplication 
  -- * Properties of idempotent semigroups
  , idempotent_addition
  , idempotent_multiplication
) where


import safe Data.Semiring
import safe Data.Foldable (Foldable)
import safe Data.Functor.Apply (Apply)
import safe Data.Semigroup.Foldable (Foldable1)
--import Data.Semigroup.Property

import safe Prelude hiding (Num(..), sum)

import safe Data.Prd.Property
import safe Data.Prd.Connectionn
--import safe qualified Test.Operation as Prop hiding (distributive)

{-

prop_cojoined (~~) f = (codiagonal !# f) ~~ (Compose . tabulate $ \i -> tabulate $ \j -> cojoined (index f) i j)

-- trivial coalgebra
prop_codiagonal' (~~) f = (codiagonal !# f) ~~ (Compose $ flip imapRep f $ \i x -> flip imapRep f $ \j _ -> bool zero x $ (i == j))

-- trivial coalgebra
prop_codiagonal (~~) f = (codiagonal !# f) ~~ (flip bindRep id . getCompose $ f)

prop_diagonal (~~) f = (diagonal !# f) ~~ (tabulate $ joined (index . index (getCompose f)))
-}

------------------------------------------------------------------------------------
-- Properties of generic arithmetic operators

-- | \( \forall a: (u \# a) \equiv a \)
--
-- Right neutrality of a unit /u/ with respect to an operator /#/.
--
-- For example, an implementation of 'Monoid' must satisfy @neutral (<>) mempty@
--
neutral :: Rel r b -> Rel r r -> r -> r -> b
neutral (~~) (#) u a = (u # a) ~~ a

-- | \( \forall a: (a \# u) \equiv a \)
--
-- Left neutrality of a unit /u/ with respect to an operator /#/.
--
-- For example, an implementation of 'Monoid' must satisfy @neutral (<>) mempty@
--
neutral' :: Rel r b -> Rel r r -> r -> r -> b
neutral' (~~) (#) u a = (a # u) ~~ a

-- | \( \forall a, b, c: (a \# b) \# c \doteq a \# (b \# c) \)
--
associative :: Rel r b -> Rel r r -> r -> r -> r -> b
associative (~~) (#) a b c = ((a # b) # c) ~~ (a # (b # c)) 

-- | \( \forall a: (u \# a) \equiv u \)
--
-- Right annihilativity of an element /u/ with respect to an operator /#/.
--
-- For example, @False@ is a right annihilative element of @||@.
--
annihilative :: Rel r b -> Rel r r -> r -> r -> b
annihilative (~~) (#) u a = (u # a) ~~ u

-- | \( \forall a: (a \# u) \equiv u \)
--
-- Left annihilativity of an element /u/ with respect to an operator /#/.
--
-- For example, @Nothing@ is a right annihilative element of @*>@.
--
annihilative' :: Rel r b -> Rel r r -> r -> r -> b
annihilative' (~~) (#) u a = (a # u) ~~ u

-- | \( \forall a, b: a \# b \doteq b \# a \)
--
commutative :: Rel r b -> Rel r r -> r -> r -> b
commutative (~~) (#) a b = (a # b) ~~ (b # a)

-- | \( \forall a, b, c: (a \# b) \% c \equiv (a \% c) \# (b \% c) \)
--
distributive :: Rel r b -> Rel r r -> Rel r r -> r -> r -> r -> b
distributive (~~) (#) (%) a b c = ((a # b) % c) ~~ ((a % c) # (b % c))

-- | \( \forall a, b, c: c \% (a \# b) \equiv (c \% a) \# (c \% b) \)
--
distributive' :: Rel r b -> Rel r r -> Rel r r -> r -> r -> r -> b
distributive' (~~) (#) (%) a b c = (c % (a # b)) ~~ ((c % a) # (c % b))

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
nonunital :: Presemiring r => Rel r b -> r -> r -> b
nonunital (~~) a b = (a * b) ~~ (a * b + b)

-- | Presemiring morphisms are distributive semigroup morphisms.
--
-- This is a required property for presemiring morphisms.
--
morphism_presemiring :: Eq s => Presemiring r => Presemiring s => (r -> s) -> r -> r -> r -> Bool
morphism_presemiring f x y z =
  morphism_additive (==) f x y &&
  morphism_multiplicative (==) f x y &&
  morphism_distribitive (==) f x y z

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
distributive_addition :: Presemiring r => Rel r b -> r -> r -> r -> b
distributive_addition (~~) = distributive (~~) (+) (*) 

-- | \( \forall M \geq 1; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b \sim \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication over finite (non-empty) sums.
--
-- For types with exact arithmetic this follows from 'distributive' and the universality of folds.
--
distributive_finite1 :: Presemiring r => Foldable1 f => Rel r b -> f r -> r -> b
distributive_finite1 (~~) as b = (sum1 as * b) ~~ (sumWith1 (* b) as)

-- | \( \forall a, b, c \in R: f ((a + b) * c) \sim f (a * c) + f (b * c) \)
-- 
-- Presemiring morphisms must be compatible with right-distribution.
--
morphism_distribitive :: Presemiring r => Presemiring s => Rel s b -> (r -> s) -> r -> r -> r -> b
morphism_distribitive (~~) f x y z = (f $ (x + y) * z) ~~ (f (x * z) + f (y * z))

------------------------------------------------------------------------------------
-- Required properties of semirings

-- | Semiring morphisms are monoidal presemiring morphisms.
--
-- This is a required property for semiring morphisms.
--
morphism_semiring :: Eq s => Semiring r => Semiring s => (r -> s) -> r -> r -> r -> Bool
morphism_semiring f x y z =
  morphism_presemiring f x y z &&
  morphism_additive' (==) f &&
  morphism_multiplicative' (==) f

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
annihilative_multiplication :: Semiring r => Rel r b -> r -> b
annihilative_multiplication (~~) r = annihilative (~~) (*) zero r

-- | \( \forall M \geq 0; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b \sim \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication between finite sums.
--
-- For types with exact arithmetic this follows from 'distributive' & 'Data.Semigroup.neutral_multiplication'.
--
distributive_finite :: Semiring r => Foldable f => Rel r b -> f r -> r -> b
distributive_finite (~~) as b = (sum as * b) ~~ (sumWith (* b) as)

------------------------------------------------------------------------------------
-- Left-distributive presemirings and semirings

-- | \( \forall M,N \geq 0; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) \sim \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports xmult-multiplication.
--
distributive_xmult :: Semiring r => Applicative f => Foldable f => Rel r b -> f r -> f r -> b
distributive_xmult (~~) as bs = (sum as * sum bs) ~~ (xmult as bs)

-- | \( \forall M,N \geq 1; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) = \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports (non-empty) xmult-multiplication.
--
distributive_xmult1 :: Presemiring r => Apply f => Foldable1 f => Rel r b -> f r -> f r -> b
distributive_xmult1 (~~) as bs = (sum1 as * sum1 bs) ~~ (xmult1 as bs)

------------------------------------------------------------------------------------
-- Required properties of semigroups

-- | \( \forall a, b, c \in R: (a + b) + c \sim a + (b + c) \)
--
-- A semigroup must right-associate addition.
--
-- This is a required property for semigroups.
--
associative_addition :: Presemiring r => Rel r b -> r -> r -> r -> b
associative_addition (~~) = associative (~~) (+) 

-- | \( \forall a, b, c \in R: (a * b) * c \sim a * (b * c) \)
--
-- A semigroup must right-associate multiplication.
--
-- This is a required property for semigroups.
--
associative_multiplication :: Presemiring r => Rel r b -> r -> r -> r -> b
associative_multiplication (~~) = associative (~~) (*) 

------------------------------------------------------------------------------------
-- Required properties of monoids

-- | \( \forall a \in R: (z + a) \sim a \)
--
-- A semigroup with a right-neutral additive identity must satisfy:
--
-- @
-- 'neutral_addition' ('==') 'zero' r = 'True'
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
neutral_addition :: Semiring r => Rel r b -> r -> b
neutral_addition (~~) = neutral (~~) (+) zero

-- | \( \forall a \in R: (o * a) \sim a \)
--
-- A semigroup with a right-neutral multiplicative identity must satisfy:
--
-- @
-- 'neutral_multiplication' ('==') 'one' r = 'True'
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'one' '*' r = r
-- @
--
-- This is a required property for multiplicative monoids.
--
neutral_multiplication :: Semiring r => Rel r b -> r -> b
neutral_multiplication (~~) = neutral (~~) (*) one

------------------------------------------------------------------------------------
-- Properties of commutative semigroups

-- | \( \forall a, b \in R: a + b \sim b + a \)
--
-- This is a an optional property for semigroups, and a required property for semirings.
--
commutative_addition :: Presemiring r => Rel r b -> r -> r -> b
commutative_addition (~~) = commutative (~~) (+) 

-- | \( \forall a, b \in R: a * b \sim b * a \)
--
-- This is a an optional property for semigroups, and a optional property for semirings and rings.
--
commutative_multiplication :: Presemiring r => Rel r b -> r -> r -> b
commutative_multiplication (~~) = commutative (~~) (*) 

------------------------------------------------------------------------------------
-- Properties of cancellative semigroups

-- | \( \forall a, b, c \in R: b + a \sim c + a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt addition then for all /a/
-- the section /(a +)/ is injective.
--
-- See < https://en.wikipedia.org/wiki/Cancellation_property >
--
cancellative_addition :: Presemiring r => Rel r Bool -> r -> r -> r -> Bool
cancellative_addition (~~) a = injective (~~) (+ a)

-- | \( \forall a, b, c \in R: b * a \sim c * a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt multiplication then for all /a/
-- the section /(a *)/ is injective.
--
cancellative_multiplication :: Presemiring r => Rel r Bool -> r -> r -> r -> Bool
cancellative_multiplication (~~) a = injective (~~) (* a)

------------------------------------------------------------------------------------
-- Properties of idempotent semigroups

-- | Idempotency property for additive semigroups.
--
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a an optional property for semigroups and semirings.
--
-- This is a required property for lattices.
--
idempotent_addition :: Presemiring r => Rel r b -> r -> b
idempotent_addition (~~) r = (r + r) ~~ r

-- | Idempotency property for multplicative semigroups.
--
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a an optional property for semigroups and semirings.
--
-- This is a required property for lattices.
--
idempotent_multiplication :: Presemiring r => Rel r b -> r -> b
idempotent_multiplication (~~) r = (r * r) ~~ r

------------------------------------------------------------------------------------
-- Properties of semigroup morphisms

-- |
--
-- This is a required property for additive semigroup morphisms.
--
morphism_additive :: Presemiring r => Presemiring s => Rel s b -> (r -> s) -> r -> r -> b
morphism_additive (~~) f x y = (f $ x + y) ~~ (f x + f y)

-- |
--
-- This is a required property for multiplicative semigroup morphisms.
--
morphism_multiplicative :: Presemiring r => Presemiring s => Rel s b -> (r -> s) -> r -> r -> b
morphism_multiplicative (~~) f x y = (f $ x * y) ~~ (f x * f y)

-- |
--
-- This is a required property for additive monoid morphisms.
--
morphism_additive' :: Semiring r => Semiring s => Rel s b -> (r -> s) -> b
morphism_additive' (~~) f = (f zero) ~~ zero

-- |
--
-- This is a required property for multiplicative monoid morphisms.
--
morphism_multiplicative' :: Semiring r => Semiring s => Rel s b -> (r -> s) -> b
morphism_multiplicative' (~~) f = (f one) ~~ one
