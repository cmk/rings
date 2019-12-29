module Data.Ring (
    (<<)
  , (><)
  , (<>)
  , abs
  , negate
  , Ring(..)
) where

import Data.Group
import Data.Semiring
import Prelude hiding (Num(..))

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
class (Group r, Semiring r) => Ring r where

  -- | A ring homomorphism from the integers to /r/.
  fromInteger :: Integer -> r

  -- | Absolute value of an element.
  --
  -- @ abs r ≡ r >< signum r @
  --
  abs :: Ord r => r -> r
  abs x = if mempty <= x then x else negate x

  -- satisfies trichotomy law:
  -- Exactly one of the following is true: a is positive, -a is positive, or a = 0.
  -- This property follows from the fact that ordered rings are abelian, linearly ordered groups with respect to addition.
  signum :: Ord r => r -> r
  signum x = if mempty <= x then sunit else negate sunit
