{-# Language ConstraintKinds #-}
{-# Language DefaultSignatures #-}

module Data.Dioid where

import Data.Connection.Yoneda
import Data.Semiring




{-
An idempotent dioid is a dioid in which the addition /<>/ is idempotent. A frequently encountered special case is one where addition /<>/ is not only idempotent but also selective. A selective dioid is a dioid in which the addition /<>/ is selective (i.e.: ∀a, b ∈ E: a /<>/ b = a or b).

Idempotent dioids form a particularly rich class of dioids which contains many sub-classes, in particular:
– Doubly-idempotent dioids and distributive lattices
– Doubly selective dioids
– Idempotent-cancellative dioids and selective-cancellative dioids
– Idempotent-invertible dioids and selective-invertible dioids

Dioids (idempotent dioids in particular) play an important role in many applications in computer science, ranging from regular languages and Kleene algebras to shortest path algorithms using tropical semirings such as the max-plus semiring. They are also generalizations of distributive lattices, quantales, residuated lattices and relation algebras, each of which have been studied extensively in mathematics and logic.

-}

-- | Right pre-dioids and dioids.
--
-- A right-dioid is a semiring with a right-canonical pre-order relation relative to '<>':
-- @a <~ b@ iff @b ≡ a <> c@ for some @c@.
-- 
-- In other words we have that:
--
-- @
-- a '<~' (a '<>' b) ≡ 'True'
-- @
--
-- Consequently '<~' is both reflexive and transitive:
--
-- @
-- a '<~' a ≡ 'True'
-- a '<~' b && b '<~' c ==> a '<~' c ≡ 'True'
-- @
--
-- Finally '<~' is an order relation:
--
-- @(a '=~' b) <==> (a '==' b)@
--
-- See 'Data.Dioid.Property'
--
class (Yoneda a, Semiring a) => Dioid a where



-------------------------------------------------------------------------------
-- 'Closed'
-------------------------------------------------------------------------------

-- | Infinite closures of a semiring.
--
-- 'Closed' adds a Kleene 'star' operator to a 'Semiring', with an infinite closure property:
--
-- @'star' x ≡ 'star' x '><' x '<>' 'unit' ≡ x '><' 'star' x '<>' 'unit'@
--
-- If @r@ is a dioid then 'star' must be monotonic:
--
-- @x '<~' y ==> 'star' x '<~' 'star' y
--
-- See also <https://en.wikipedia.org/wiki/Semiring#Closed_semirings closed semiring>
--
class Semiring a => Closed a where
  {-# MINIMAL star | plus #-} 

  star :: a -> a
  default star :: Monoid a => a -> a
  star a = unit <> plus a

  plus :: a -> a
  plus a = a >< star a

-- This only works if * is idempotent (a lattice?), as it just sums w/o powers
--star = fmap fold . many
--plus = fmap fold . some

--interior :: (r -> r) -> r -> r
--interior f r = (r ><) . f
--adjoint . star = plus . adjoint

--star = (>< mempty) . (<> mempty)
--plus = (<> unit) . (>< unit)



instance Closed () where
  star  _ = ()
  plus _ = ()
  {-# INLINE star #-}
  {-# INLINE plus #-}

instance Closed Bool where
  star = const True -- == (|| True)
  plus = id -- == (&& True)
  {-# INLINE star #-}
  {-# INLINE plus #-}

instance (Monoid b, Closed b) => Closed (a -> b) where
  plus = fmap plus
  {-# INLINE plus #-}

  star = fmap star
  {-# INLINE star #-}
