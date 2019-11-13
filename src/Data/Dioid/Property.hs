{-# Language AllowAmbiguousTypes #-}

module Data.Dioid.Property (
  -- * Properties of dioids (aka ordered semirings) 
    ordered_preordered
  , ordered_monotone_zero
  , ordered_monotone_addition
  , ordered_positive_addition
  , ordered_monotone_multiplication
  , ordered_annihilative_unit 
  , ordered_idempotent_addition
  , ordered_positive_multiplication
  -- * Properties of absorbative dioids 
  , absorbative_addition
  , absorbative_addition'
  , idempotent_addition
  , absorbative_multiplication
  , absorbative_multiplication' 
  -- * Properties of annihilative dioids 
  , annihilative_addition 
  , annihilative_addition' 
  , codistributive
  -- * Properties of closed dioids
  , closed_pstable
  , closed_paffine 
  , closed_stable 
  , closed_affine 
  , idempotent_star
) where

import Data.Prd
import Data.Dioid
import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semiring hiding (nonunital)
import Data.Semigroup.Orphan ()
import Numeric.Natural
import Test.Property.Util ((<==>),(==>))
import qualified Test.Property as Prop hiding (distributive_on)
import qualified Data.Semiring.Property as Prop

------------------------------------------------------------------------------------
-- Properties of ordered semirings (aka dioids).

-- | '<~' is a preordered relation relative to '<>'.
--
-- This is a required property.
--
ordered_preordered :: Dioid r => r -> r -> Bool
ordered_preordered a b = a <~ (a <> b)

-- | 'mempty' is a minimal or least element of @r@.
--
-- This is a required property.
--
ordered_monotone_zero :: (Monoid r, Dioid r) => r -> Bool
ordered_monotone_zero a = mempty ?~ a ==> mempty <~ a 

-- | \( \forall a, b, c: b \leq c \Rightarrow b + a \leq c + a
--
-- In an ordered semiring this follows directly from the definition of '<~'.
--
-- Compare 'cancellative_addition'.
-- 
-- This is a required property.
--
ordered_monotone_addition :: Dioid r => r -> r -> r -> Bool
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
ordered_monotone_multiplication :: Dioid r => r -> r -> r -> Bool
ordered_monotone_multiplication a = Prop.monotone_on (<~) (<~) (>< a)

-- | '<~' is consistent with annihilativity.
--
-- This means that a dioid with an annihilative multiplicative unit must satisfy:
--
-- @
-- ('one' <~) ≡ ('one' ==)
-- @
--
ordered_annihilative_unit :: (Monoid r, Dioid r) => r -> Bool
ordered_annihilative_unit a = unit <~ a <==> unit =~ a

-- | \( \forall a, b: a \leq b \Rightarrow a + b = b
--
ordered_idempotent_addition :: (Prd r, Monoid r) => r -> r -> Bool
ordered_idempotent_addition a b = (a <~ b) <==> (a <> b =~ b)

-- |  \( \forall a, b: a * b = 0 \Rightarrow a = 0 \vee b = 0 \)
--
ordered_positive_multiplication :: (Monoid r, Dioid r) => r -> r -> Bool
ordered_positive_multiplication a b = a >< b =~ mempty ==> a =~ mempty || b =~ mempty

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
absorbative_addition :: (Eq r, Dioid r) => r -> r -> Bool
absorbative_addition a b = a >< b <> b ~~ b

idempotent_addition :: (Eq r, Monoid r, Dioid r) => r -> Bool
idempotent_addition = absorbative_addition unit
 
-- | \( \forall a, b \in R: b + b * a = b \)
--
-- Left-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'unit' a ~~ a <> a ~~ a
-- @
--
absorbative_addition' :: (Eq r, Dioid r) => r -> r -> Bool
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
absorbative_multiplication :: (Eq r, Dioid r) => r -> r -> Bool
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
absorbative_multiplication' :: (Eq r, Dioid r) => r -> r -> Bool
absorbative_multiplication' a b = b >< (b <> a) ~~ b

------------------------------------------------------------------------------------
-- Properties of idempotent and annihilative dioids.

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
annihilative_addition :: (Eq r, Monoid r, Dioid r) => r -> Bool
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
annihilative_addition' :: (Eq r, Monoid r, Dioid r) => r -> Bool
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
codistributive :: (Eq r, Dioid r) => r -> r -> r -> Bool
codistributive = Prop.distributive_on' (~~) (><) (<>)

------------------------------------------------------------------------------------
-- Properties of closed dioids

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
closed_pstable :: (Eq r, Prd r, Monoid r, Dioid r) => Natural -> r -> Bool
closed_pstable p a = powers p a ~~ powers (p <> unit) a

-- | \( x = a * x + b \Rightarrow x = (1 + \sum_{i=1}^{P} a^i) * b \)
--
-- If /a/ is p-stable for some /p/, then we have:
--
closed_paffine :: (Eq r, Monoid r, Dioid r) => Natural -> r -> r -> Bool
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
closed_stable :: (Eq r, Monoid r, Dioid r, Closed r) => r -> Bool
closed_stable a = star a ~~ star a >< a <> unit

closed_stable' :: (Eq r, Monoid r, Dioid r, Closed r) => r -> Bool
closed_stable' a = star a ~~ unit <> a >< star a

closed_affine :: (Eq r, Monoid r, Dioid r, Closed r) => r -> r -> Bool
closed_affine a b = x ~~ a >< x <> b where x = star a >< b

-- If /R/ is closed then 'star' must be idempotent:
--
-- @'star' ('star' a) ~~ 'star' a@
--
idempotent_star :: (Eq r, Monoid r, Dioid r, Closed r) => r -> Bool
idempotent_star = Prop.idempotent star

-- If @r@ is a closed dioid then 'star' must be monotone:
--
-- @x '<~' y ==> 'star' x '<~' 'star' y@
--
monotone_star :: (Monoid r, Dioid r, Closed r) => r -> r -> Bool
monotone_star = Prop.monotone_on (<~) (<~) star
