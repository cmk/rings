{-# Language ConstraintKinds #-}

module Data.Dioid where

import Data.Connection.Yoneda
import Data.Semiring
import Data.Prd
import Numeric.Natural

-- A constraint kind for topological dioids
type Topological a = (Dioid a, Kleene a, Yoneda a)

{-
An idempotent dioid is a dioid in which the addition /<>/ is idempotent. A frequently encountered special case is one where addition /<>/ is not only idempotent but also selective. A selective dioid is a dioid in which the addition /<>/ is selective (i.e.: ∀a, b ∈ E: a /<>/ b = a or b).

Idempotent dioids form a particularly rich class of dioids which contains many sub-classes, in particular:
– Doubly-idempotent dioids and distributive lattices
– Doubly selective dioids
– Idempotent-cancellative dioids and selective-cancellative dioids
– Idempotent-invertible dioids and selective-invertible dioids

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
class (Prd r, Semiring r) => Dioid r where

  -- | A dioid homomorphism from the naturals to /r/.
  fromNatural :: Natural -> r
{-
  psignum :: Monoid r => r -> Maybe r
  psignum x = case pcomparePrd mempty x
     Just GT -> Just sunit
     Just EQ -> Just mempty
     _ -> Nothing
-}


instance (Monoid a, Monoid b, Dioid a, Dioid b) => Dioid (a, b)

instance (Monoid a, Monoid b, Monoid c, Dioid a, Dioid b, Dioid c) => Dioid (a, b, c)
