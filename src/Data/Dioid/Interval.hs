-- | <https://en.wikipedia.org/wiki/Partially_ordered_set#Intervals>
module Data.Dioid.Interval (
    Interval()
  , (...)
  , endpts
  , singleton
  , upset
  , dnset
  , empty
) where

import Data.Prd
import Data.Prd.Lattice
import Data.Connection

import Prelude

{-

ivllat :: (Lattice a, Bound a) => Trip (Interval a) a
ivllat = Trip f g h where
  f = maybe minimal (uncurry (\/)) . endpts
  g = singleton
  h = maybe maximal (uncurry (/\)) . endpts 

indexed :: Index a => Conn (Interval a) (Maybe (Down a, a))

https://en.wikipedia.org/wiki/Locally_finite_poset
https://en.wikipedia.org/wiki/Incidence_algebra

An interval in a poset P is a subset I of P with the property that, for any x and y in I and any z in P, if x ≤ z ≤ y, then z is also in I. 

-}

data Interval a = I !a !a | Empty deriving (Eq, Show)

-- Interval order
-- https://en.wikipedia.org/wiki/Interval_order
instance Ord a => Prd (Interval a) where
  Empty <~ Empty = True
  Empty <~ _ = False

  i@(I _ x) <~ j@(I y _) = x < y || i == j

{-
-- Containment order
-- https://en.wikipedia.org/wiki/Containment_order
instance Prd a => Prd (Interval a) where
  Empty <~ _ = True
  I x y <~ I x' y' = x' <~ x && y <~ y'
-}


infix 3 ...

-- | Construct an interval from a pair of points.
--
-- If @a <~ b@ then @a ... b = Empty@.
--
(...) :: Prd a => a -> a -> Interval a
a ... b
  | a <~ b = I a b
  | otherwise = Empty
{-# INLINE (...) #-}

-- | Obtain the endpoints of an interval.
--
endpts :: Interval a -> Maybe (a, a)
endpts Empty = Nothing
endpts (I x y) = Just (x, y)
{-# INLINE endpts #-}

-- | Construct an interval containing a single point.
--
-- >>> singleton 1
-- 1 ... 1
--
singleton :: a -> Interval a
singleton a = I a a
{-# INLINE singleton #-}

{-
properties: 

Yoneda lemma for preorders:
x <~ y <==> upset x <~ upset y --containment order

-}

-- | \( X_\geq(x) = \{ y \in X | y \geq x \} \)
--
-- Construct the upper set of an element /x/.
--
-- This function is monotone wrt the containment order.
--
upset :: Max a => a -> Interval a
upset x = x ... maximal
{-# INLINE upset #-}

-- | \( X_\leq(x) = \{ y \in X | y \leq x \} \)
--
-- Construct the lower set of an element /x/.
--
-- This function is antitone wrt the containment order.
--
dnset :: Min a => a -> Interval a
dnset x = minimal ... x
{-# INLINE dnset #-}

-- | The empty interval.
--
-- >>> empty
-- Empty
empty :: Interval a
empty = Empty
{-# INLINE empty #-}
