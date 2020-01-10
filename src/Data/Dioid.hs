{-# Language ConstraintKinds #-}
{-# LANGUAGE Safe            #-}

module Data.Dioid where

import safe Data.Word
import safe Data.Connection
import safe Data.Connection.Word
import safe Data.Connection.Yoneda
import safe Data.Ring
import safe Data.Prd
import safe Numeric.Natural
import safe GHC.Real

import safe Prelude hiding (Num(..))
import safe qualified Prelude as N

-- A constraint kind for topological dioids
--type Topological a = (Dioid a, Kleene a, Yoneda a)

type Positive = Ratio Natural


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
class (Prd a, Semiring a) => Dioid a where

  -- | A dioid homomorphism from the naturals to /a/.
  fromNatural :: Natural -> a

instance Dioid () where
  fromNatural _ = ()

instance Dioid Bool where
  fromNatural 0 = False
  fromNatural _ = True

instance Dioid Word8 where
  fromNatural = connr w08nat

instance Dioid Word16 where
  fromNatural = connr w16nat

instance Dioid Word32 where
  fromNatural = connr w32nat

instance Dioid Word64 where
  fromNatural = connr w64nat

instance Dioid Natural where
  fromNatural = id

instance Dioid Positive where
  fromNatural x = x :% sunit

instance (Monoid a, Monoid b, Dioid a, Dioid b) => Dioid (a, b) where
  fromNatural x = (fromNatural x, fromNatural x)

instance (Monoid a, Monoid b, Monoid c, Dioid a, Dioid b, Dioid c) => Dioid (a, b, c) where
  fromNatural x = (fromNatural x, fromNatural x, fromNatural x)
