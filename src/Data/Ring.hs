{-# LANGUAGE CPP  #-}
{-# LANGUAGE Safe #-}

module Data.Ring (
    (<<)
  , (><)
  , (<>)
  , negate
  , Ring(..)
) where

import safe Data.Complex
import safe Data.Fixed
import safe Data.Int
import safe Data.Group
import safe Data.Semiring
import safe GHC.Real
import safe Prelude hiding (Num(..))
import safe qualified Prelude as N

-- | Rings.
--
-- A ring /R/ is a commutative group with a second monoidal operation /></ that distributes over /<>/.
--
-- The basic properties of a ring follow immediately from the axioms:
-- 
-- @ r '><' 'mempty' ≡ 'mempty' ≡ 'mempty' '><' r @
--
-- @ 'negate' 'sunit' '><' r ≡ 'negate' r @
--
-- Furthermore, the binomial formula holds for any commuting pair of elements (that is, any /a/ and /b/ such that /a >< b = b >< a/).
--
-- If /mempty = sunit/ in a ring /R/, then /R/ has only one element, and is called the zero ring.
-- Otherwise the additive identity, the additive inverse of each element, and the multiplicative identity are unique.
--
-- See < https://en.wikipedia.org/wiki/Ring_(mathematics) >.
--
-- If the ring is < https://en.wikipedia.org/wiki/Ordered_ring ordered > (i.e. has an 'Ord' instance), then the following additional properties must hold:
--
-- @ a <= b ==> a <> c <= b <> c @
--
-- @ mempty <= a && mempty <= b ==> mempty <= a >< b @
--
-- See the properties module for a detailed specification of the laws.
--
class (Group a, Semiring a) => Ring a where

  -- | A ring homomorphism from the integers to /a/.
  fromInteger :: Integer -> a

  -- | Absolute value of an element.
  --
  -- @ abs r ≡ r >< signum r @
  --
  abs :: Ord a => a -> a
  abs x = if mempty <= x then x else negate x

  -- satisfies trichotomy law:
  -- Exactly one of the following is true: a is positive, -a is positive, or a = 0.
  -- This property follows from the fact that ordered rings are abelian, linearly ordered groups with respect to addition.
  signum :: Ord a => a -> a
  signum x = if mempty <= x then sunit else negate sunit

instance Ring Rational where
  fromInteger x = fromInteger x :% sunit
  {-# INLINE fromInteger #-}

instance Ring a => Ring (Complex a) where
  fromInteger x = fromInteger x :+ mempty
  {-# INLINE fromInteger #-}

#define deriveRing(ty)             \
instance Ring (ty) where {         \
   fromInteger = N.fromInteger     \
;  abs = N.abs                     \
;  signum = N.signum               \
;  {-# INLINE abs #-}              \
;  {-# INLINE signum #-}           \
}

deriveRing(Int)
deriveRing(Int8)
deriveRing(Int16)
deriveRing(Int32)
deriveRing(Int64)
deriveRing(Integer)

deriveRing(Uni)
deriveRing(Deci)
deriveRing(Centi)
deriveRing(Milli)
deriveRing(Micro)
deriveRing(Nano)
deriveRing(Pico)
