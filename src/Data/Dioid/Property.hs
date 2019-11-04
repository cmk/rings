{-# Language AllowAmbiguousTypes #-}

module Data.Dioid.Property (
  -- * Properties of pre-semirings & semirings
    neutral_addition
  , neutral_addition'
  , neutral_multiplication
  , neutral_multiplication'
  , associative_addition 
  , associative_multiplication 
  , distributive 
  -- * Properties of non-unital (near-)semirings
  , nonunital
  -- * Properties of unital semirings
  , annihilative_multiplication 
  , Prop.homomorphism_boolean
  -- * Properties of cancellative semirings 
  , cancellative_addition 
  , cancellative_multiplication 
  -- * Properties of commutative semirings 
  , commutative_addition 
  , commutative_multiplication
  -- * Properties of absorbative semirings 
  , absorbative_addition
  , absorbative_addition'
  , idempotent_addition
  , absorbative_multiplication
  , absorbative_multiplication' 
  -- * Properties of annihilative semirings 
  , annihilative_addition 
  , annihilative_addition' 
  , codistributive
  -- * Properties of ordered semirings 
  , ordered_preordered
  , ordered_monotone_zero
  , ordered_monotone_addition
  , ordered_positive_addition
  , ordered_monotone_multiplication
  , ordered_annihilative_unit 
  , ordered_idempotent_addition
  , ordered_positive_multiplication
) where

import Data.Prd
import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semiring hiding (nonunital)
import Data.Semigroup.Orphan ()
import Test.Property.Util ((<==>),(==>))
import qualified Test.Property as Prop hiding (distributive_on)
import qualified Data.Semiring.Property as Prop


------------------------------------------------------------------------------------
-- Properties of pre-semirings & semirings

-- | \( \forall a \in R: (z + a) = a \)
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
neutral_addition :: (Eq r, Prd r, Semigroup r) => r -> r -> Bool
neutral_addition = Prop.neutral_addition_on (~~)

neutral_addition' :: (Eq r, Prd r, Monoid r, Semigroup r) => r -> Bool
neutral_addition' = Prop.neutral_addition_on' (~~)

-- | \( \forall a \in R: (o * a) = a \)
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
neutral_multiplication :: (Eq r, Prd r, Semiring r) => r -> r -> Bool
neutral_multiplication = Prop.neutral_multiplication_on (~~)

neutral_multiplication' :: (Eq r, Prd r, Monoid r, Semiring r) => r -> Bool
neutral_multiplication' = Prop.neutral_multiplication_on' (~~)

-- | \( \forall a, b, c \in R: (a + b) + c = a + (b + c) \)
--
-- /R/ must right-associate addition.
--
-- This should be verified by the underlying 'Semigroup' instance,
-- but is included here for completeness.
--
-- This is a required property.
--
associative_addition :: (Eq r, Prd r, Semigroup r) => r -> r -> r -> Bool
associative_addition = Prop.associative_addition_on (~~)

-- | \( \forall a, b, c \in R: (a * b) * c = a * (b * c) \)
--
-- /R/ must right-associate multiplication.
--
-- This is a required property.
--
associative_multiplication :: (Eq r, Prd r, Semiring r) => r -> r -> r -> Bool
associative_multiplication = Prop.associative_multiplication_on (~~)

-- | \( \forall a, b, c \in R: (a + b) * c = (a * c) + (b * c) \)
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
distributive :: (Eq r, Prd r, Semiring r) => r -> r -> r -> Bool
distributive = Prop.distributive_on (~~)

------------------------------------------------------------------------------------
-- Properties of non-unital semirings (aka near-semirings)

-- | \( \forall a, b \in R: a * b = a * b + b \)
--
-- If /R/ is non-unital (i.e. /unit/ equals /mempty/) then it will instead satisfy 
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
nonunital :: forall r. (Eq r, Prd r, Monoid r, Semiring r) => r -> r -> Bool
nonunital = Prop.nonunital_on (~~)

------------------------------------------------------------------------------------
-- Properties of unital semirings

-- | \( \forall a \in R: (z * a) = u \)
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
annihilative_multiplication :: (Eq r, Prd r, Monoid r, Semiring r) => r -> Bool
annihilative_multiplication = Prop.annihilative_multiplication_on (~~)

------------------------------------------------------------------------------------
-- Properties of cancellative & commutative semirings


-- | \( \forall a, b, c \in R: b + a = c + a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt addition then for all /a/
-- the section /(a <>)/ is injective.
--
cancellative_addition :: (Eq r, Prd r, Semigroup r) => r -> r -> r -> Bool
cancellative_addition = Prop.cancellative_addition_on (~~)


-- | \( \forall a, b, c \in R: b * a = c * a \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt multiplication then for all /a/
-- the section /(a ><)/ is injective.
--
cancellative_multiplication :: (Eq r, Prd r, Semiring r) => r -> r -> r -> Bool
cancellative_multiplication = Prop.cancellative_multiplication_on (~~)

-- | \( \forall a, b \in R: a + b = b + a \)
--
commutative_addition :: (Eq r, Prd r, Semigroup r) => r -> r -> Bool
commutative_addition = Prop.commutative_addition_on (=~)


-- | \( \forall a, b \in R: a * b = b * a \)
--
commutative_multiplication :: (Eq r, Prd r, Semiring r) => r -> r -> Bool
commutative_multiplication = Prop.commutative_multiplication_on (=~)


------------------------------------------------------------------------------------
-- Properties of idempotent & absorbative semirings

-- | \( \forall a, b \in R: a * b + b = b \)
--
-- Right-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'unit' a ~~ a <> a ~~ a
-- @
--
absorbative_addition :: (Eq r, Prd r, Semiring r) => r -> r -> Bool
absorbative_addition a b = a >< b <> b ~~ b

idempotent_addition :: (Eq r, Prd r, Monoid r, Semiring r) => r -> Bool
idempotent_addition = absorbative_addition unit
 
-- | \( \forall a, b \in R: b + b * a = b \)
--
-- Left-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'unit' a ~~ a <> a ~~ a
-- @
--
absorbative_addition' :: (Eq r, Prd r, Semiring r) => r -> r -> Bool
absorbative_addition' a b = b <> b >< a ~~ b

-- | \( \forall a, b \in R: (a + b) * b = b \)
--
-- Right-mulitplicative absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_multiplication' 'mempty' a ~~ a '><' a ~~ a
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law >.
--
absorbative_multiplication :: (Eq r, Prd r, Semiring r) => r -> r -> Bool
absorbative_multiplication a b = (a <> b) >< b ~~ b

--absorbative_multiplication a b c = (a <> b) >< c ~~ c
--closed a = 
--  absorbative_multiplication (star a) unit a && absorbative_multiplication unit (star a) a 

-- | \( \forall a, b \in R: b * (b + a) = b \)
--
-- Left-mulitplicative absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_multiplication'' 'mempty' a ~~ a '><' a ~~ a
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law >.
--
absorbative_multiplication' :: (Eq r, Prd r, Semiring r) => r -> r -> Bool
absorbative_multiplication' a b = b >< (b <> a) ~~ b

-- | \( \forall a \in R: o + a = o \)
--
-- A unital semiring with a right-annihilative muliplicative unit must satisfy:
--
-- @
-- 'unit' <> a ~~ 'unit'
-- @
--
-- For a dioid this is equivalent to:
-- 
-- @
-- ('unit' '<~') ~~ ('unit' '~~')
-- @
--
-- For 'Alternative' instances this is known as the left-catch law:
--
-- @
-- 'pure' a '<|>' _ ~~ 'pure' a
-- @
--
annihilative_addition :: (Eq r, Prd r, Monoid r, Semiring r) => r -> Bool
annihilative_addition r = Prop.annihilative_on (~~) (<>) unit r


-- | \( \forall a \in R: a + o = o \)
--
-- A unital semiring with a left-annihilative muliplicative unit must satisfy:
--
-- @
-- a '<>' 'unit' ~~ 'unit'
-- @
--
-- Note that the left-annihilative property is too strong for many instances. 
-- This is because it requires that any effects that /r/ generates be undunit.
--
-- See < https://winterkoninkje.dreamwidth.org/90905.html >.
--
annihilative_addition' :: (Eq r, Prd r, Monoid r, Semiring r) => r -> Bool
annihilative_addition' r = Prop.annihilative_on' (~~) (<>) unit r

-- | \( \forall a, b, c \in R: c + (a * b) \equiv (c + a) * (c + b) \)
--
-- A right-codistributive semiring has a right-annihilative muliplicative unit:
--
-- @ 'codistributive' 'unit' a 'mempty' ~~ 'unit' ~~ 'unit' '<>' a @
--
-- idempotent mulitiplication:
--
-- @ 'codistributive' 'mempty' 'mempty' a ~~ a ~~ a '><' a @
--
-- and idempotent addition:
--
-- @ 'codistributive' a 'mempty' a ~~ a ~~ a '<>' a @
--
-- Furthermore if /R/ is commutative then it is a right-distributive lattice.
--
codistributive :: (Eq r, Prd r, Semiring r) => r -> r -> r -> Bool
codistributive = Prop.distributive_on' (~~) (><) (<>)

------------------------------------------------------------------------------------
-- Properties of ordered semirings (aka dioids).

-- | '<~' is a preordered relation relative to '<>'.
--
-- This is a required property.
--
ordered_preordered :: (Prd r, Semiring r) => r -> r -> Bool
ordered_preordered a b = a <~ (a <> b)

-- | 'mempty' is a minimal or least element of @r@.
--
-- This is a required property.
--
ordered_monotone_zero :: (Prd r, Monoid r) => r -> Bool
ordered_monotone_zero a = mempty ?~ a ==> mempty <~ a 

-- | \( \forall a, b, c: b \leq c \Rightarrow b + a \leq c + a
--
-- In an ordered semiring this follows directly from the definition of '<~'.
--
-- Compare 'cancellative_addition'.
-- 
-- This is a required property.
--
ordered_monotone_addition :: (Prd r, Semiring r) => r -> r -> r -> Bool
ordered_monotone_addition a = Prop.monotone_on (<~) (<~) (<> a)

-- |  \( \forall a, b: a + b = 0 \Rightarrow a = 0 \wedge b = 0 \)
--
-- This is a required property.
--
ordered_positive_addition :: (Prd r, Monoid r) => r -> r -> Bool
ordered_positive_addition a b = a <> b =~ mempty ==> a =~ mempty && b =~ mempty

-- | \( \forall a, b, c: b \leq c \Rightarrow b * a \leq c * a
--
-- In an ordered semiring this follows directly from 'distributive' and the definition of '<~'.
--
-- Compare 'cancellative_multiplication'.
--
-- This is a required property.
--
ordered_monotone_multiplication :: (Prd r, Semiring r) => r -> r -> r -> Bool
ordered_monotone_multiplication a = Prop.monotone_on (<~) (<~) (>< a)

------------------------------------------------------------------------------------
-- Properties of idempotent and annihilative dioids.

-- | '<~' is consistent with annihilativity.
--
-- This means that a dioid with an annihilative multiplicative unit must satisfy:
--
-- @
-- ('one' <~) ≡ ('one' ==)
-- @
--
ordered_annihilative_unit :: (Prd r, Monoid r, Semiring r) => r -> Bool
ordered_annihilative_unit a = unit <~ a <==> unit =~ a

-- | \( \forall a, b: a \leq b \Rightarrow a + b = b
--
ordered_idempotent_addition :: (Prd r, Monoid r) => r -> r -> Bool
ordered_idempotent_addition a b = (a <~ b) <==> (a <> b =~ b)

-- |  \( \forall a, b: a * b = 0 \Rightarrow a = 0 \vee b = 0 \)
--
ordered_positive_multiplication :: (Prd r, Monoid r, Semiring r) => r -> r -> Bool
ordered_positive_multiplication a b = a >< b =~ mempty ==> a =~ mempty || b =~ mempty
