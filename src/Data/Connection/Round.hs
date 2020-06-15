{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}

module Data.Connection.Round (
    sign
  -- * Trip
  , Trip(..)
  , unit'
  , counit'
  , half
  , tied
  , below
  , above
  , midpoint
  -- * Rounding
  , Mode(..)
  , embed
  , round
  , floor
  , ceiling
  , truncate
  , roundWith
  , roundWith1
  , roundWith2
  , roundWith3
  -- ** TripFloat
  , TripFloat
  , embed32
  , round32
  , floor32
  , ceiling32
  , truncate32
  -- ** TripDouble
  , TripDouble
  , embed64
  , round64
  , floor64
  , ceiling64
  , truncate64
  -- * Re-exports
  , Triple(..)
) where

import safe Control.Applicative
import safe Data.Connection
import safe Data.Connection.Type
import safe Data.Foldable as Foldable (foldl',foldr')
import safe Data.Functor.Identity
import safe Data.Bool
import safe Data.Int
import safe Data.Maybe
import safe Data.Lattice
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Ring
import safe Data.Semiring
import safe Prelude
 ( Eq(..), Ord, Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..)
 , id, flip, const, (.), ($), Integer, Float, Double, Ordering(..) )


sign :: (Bounded a, OrderedSemiring a) => Trip a Ordering
sign = Trip f g h where
  g GT = top
  g LT = bottom
  g EQ = zero
  
  f x | x ~~ bottom  = LT
      | x <~ zero  = EQ
      | otherwise  = GT

  h x | x ~~ top   = GT
      | x >~ zero  = EQ
      | otherwise  = LT
{-# INLINE sign #-}

instance (Bounded a, OrderedSemiring a) => Triple a Ordering where
  triple = sign

---------------------------------------------------------------------
-- Trip
---------------------------------------------------------------------

-- | Determine which half of the interval between two representations of /a/ a particular value lies.
-- 
half :: OrderedRing a => Trip a b -> a -> Maybe Ordering
half t x = pcompare (x - unit' t x) (counit' t x - x) 

-- | Determine whether /x/ lies exactly halfway between two representations.
-- 
-- > 'tied' t x = (x - 'unit'' t x) '~~' ('counit'' t x - x) @
--
tied :: OrderedRing a => Trip a b -> a -> Bool
tied t = maybe False (~~ EQ) . half t

-- | Determine whether /x/ lies below the halfway point between two representations.
-- 
-- > 'below' t x = (x - 'unit'' t x) '<' ('counit'' t x - x) @
--
below :: OrderedRing a => Trip a b -> a -> Bool
below t = maybe False (~~ LT) . half t

-- | Determine whether /x/ lies above the halfway point between two representations.
-- 
-- > 'above' t x = (x - 'unit'' t x) '>' ('counit'' t x - x) @
--
above :: OrderedRing a => Trip a b -> a -> Bool
above t = maybe False (~~ GT) . half t

-- | Return the midpoint of the interval containing x.
--
-- > tied triple $ midpoint triple x = True
--
-- >>> midpoint f32i08 4.3
-- 4.5
-- >>> P.pi - midpoint f64f32 P.pi
-- 3.1786509424591713e-8
-- >>> tied f64f32 $ midpoint f64f32 P.pi
-- True
-- >>> tied f64f32 $ midpoint f64f32 nan
-- True
--
midpoint :: OrderedField a => Trip a b -> a -> a
midpoint t x = unit' t x / two + counit' t x / two where two = one + one

---------------------------------------------------------------------
-- Rounding
---------------------------------------------------------------------

-- | The four primary IEEE rounding modes.
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
--
data Mode = 
    Round  -- ^ round to nearest with ties away from 0
  | Floor -- ^ round towards negative infinity
  | Ceiling -- ^ round towards posative infinity
  | Truncate -- ^ round towards 0
  deriving (Eq, Show)

-- | Return the nearest value to x.
--
-- > round @a @a = id
-- 
-- If x lies halfway between two finite values, then return the value
-- with the larger absolute value (i.e. round away from zero).
--
round :: forall a b. (OrderedRing a, Triple a b) => a -> b
round x =
  case half (triple @a @b) x of
    Just GT -> ceiling x -- upper half interval
    Just LT -> floor x   -- lower half interval
    _       -> truncate x

-- | Truncate towards zero.
--
-- > truncate @a @a = id
--
truncate :: (OrderedSemiring a, Triple a b) => a -> b
truncate x = bool (ceiling x) (floor x) $ x >~ zero

-- | Approximate a value in a less refined number system.
--
-- > round = roundWith Round
-- > floor = roundWith Floor
-- > ceiling = roundWith Ceiling
-- > truncate = roundWith Truncate
--
roundWith :: (OrderedRing a, Triple a b) => Mode -> a -> b
roundWith Round = round
roundWith Floor = floor
roundWith Ceiling = ceiling
roundWith Truncate = truncate

-- | Approximate a unary function in a less refined number system.
--
-- > roundWith1 :: TripRational a => Mode -> (Rational -> Rational) -> a -> a
--
roundWith1 :: (OrderedRing a, Triple a b) => Mode -> (a -> a) -> b -> b
roundWith1 rm f x = roundWith rm $ f (g x) where Trip _ g _ = triple
{-# INLINE roundWith1 #-}

-- | Approximate a binary function in a less refined number system.
--
-- >>> f x y = (x + y) - x 
-- >>> maxOdd32 = 1.6777215e7
-- >>> maxOdd64 = 9.007199254740991e15
-- >>> f maxOdd32 2.0 :: Float
-- 1.0
-- >>> roundWith2 @Rational @Float Round f maxOdd32 2.0
-- 2.0
-- >>> f maxOdd64 2.0 :: Double
-- 1.0
-- >>> roundWith2 @Rational @Double Round f maxOdd64 2.0
-- 2.0
--
roundWith2 :: (OrderedRing a, Triple a b) => Mode -> (a -> a -> a) -> b -> b -> b
roundWith2 rm f x y = roundWith rm $ f (g x) (g y) where Trip _ g _ = triple
{-# INLINE roundWith2 #-}

-- | Approximate a ternary function in a less refined number system.
--
roundWith3 :: (OrderedRing a, Triple a b) => Mode -> (a -> a -> a -> a) -> b -> b -> b -> b
roundWith3 rm f x y z = roundWith rm $ f (g x) (g y) (g z) where Trip _ g _ = triple
{-# INLINE roundWith3 #-}

---------------------------------------------------------------------
-- TripFloat
---------------------------------------------------------------------

type TripFloat a = (Bounded a, Triple Float (Extended a))

embed32 :: TripFloat a => a -> Float
embed32 = embed . Extended

-- | Lawful rounding.
--
-- >>> Prelude.round @Float @Int8 $ 0/0
-- 0
-- >>> round32 @Int8 $ 0/0
-- Nan
-- >>> Prelude.round @Float @Int8 $ 1/0
-- 0
-- >>> round32 @Int8 $ 1/0
-- 127
-- >>> Prelude.round @Float @Int8 129
-- -127
-- >>> round32 @Int8 129
-- 127
-- >>> Prelude.round @Float @Int8 $ -129
-- 127
-- >>> round32 @Int8 $ -129
-- -128
--
round32 :: TripFloat a => Float -> a 
round32 = retract . roundWith Round

floor32 :: TripFloat a => Float -> a 
floor32 = retract . roundWith Floor

ceiling32 :: TripFloat a => Float -> a 
ceiling32 = retract . roundWith Ceiling

truncate32 :: TripFloat a => Float -> a 
truncate32 = retract . roundWith Truncate

retract :: Bounded a => Extended a -> a
retract = extended bottom top id

---------------------------------------------------------------------
-- TripDouble
---------------------------------------------------------------------

type TripDouble a = (Bounded a, Triple Double (Extended a))

embed64 :: TripDouble a => a -> Double
embed64 = embed . Extended

round64 :: TripDouble a => Double -> a 
round64 = retract . roundWith Round

floor64 :: TripDouble a => Double -> a 
floor64 = retract . roundWith Floor

ceiling64 :: TripDouble a => Double -> a 
ceiling64 = retract . roundWith Ceiling

truncate64 :: TripDouble a => Double -> a 
truncate64 = retract . roundWith Truncate
