{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}
{-# Language DeriveFunctor       #-}
{-# Language DeriveGeneric       #-}
{-# Language DerivingVia         #-}
{-# Language StandaloneDeriving  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Ring (
    module Data.Semiring
  , zero, one
  , (+), (*)
  , (-), negate
    -- * Semiring
  , Semiring(..)
    -- * Ring
  , Ring(..)
  , fromInteger
    -- * Semifield
  , Semifield(..)
  , fromPositive
    -- * Field
  , Field(..)
  , fromRational
    -- * Rounding
  , RoundMode(..)
  , lift0
  , lift1
  , lift2
  , lift3
  , round
  , floor
  , ceiling
  , truncate 
  , roundOn
  , floorOn
  , ceilingOn
  , truncateOn
  , half
  , tied
  , below
  , above
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Connection
import safe Data.Connection.Conn
import safe Data.Connection.Trip
import safe Data.Either
import safe Data.Fixed
import safe Data.Foldable as Foldable (Foldable, foldl',foldr')
import safe Data.Functor.Apply
import safe Data.Functor.Compose
import safe Data.Functor.Contravariant
import safe Data.Functor.Identity
import safe Data.Functor.Rep
import safe Data.Group
import safe Data.Int
import safe Data.Maybe
import safe Data.Monoid hiding (Sum(..), Product(..))
import safe Data.Ord (Ordering(..))
import safe Data.Prd
import safe Data.Semiring
import safe GHC.Generics (Generic)
import safe GHC.Real (Ratio(..), Rational)
import safe Numeric.Natural
import safe Prelude
 ( Eq(..), Ord, Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..)
 , id, flip, const, (.), ($), Integer, Float, Double )
import safe qualified Prelude as P


-------------------------------------------------------------------------------
-- Rings
-------------------------------------------------------------------------------

-- | A < https://en.wikipedia.org/wiki/Ring_(mathematics) ring >.
--
-- A ring /R/ is a commutative group with a second monoidal operation '*' that distributes over '+'.
--
-- The basic properties of a ring follow immediately from the axioms:
-- 
-- @ r '*' 'zero' = 'zero' = 'zero' '*' r @
--
-- @ 'negate' 'one' '*' r = 'negate' r @
--
-- Furthermore, the binomial formula holds for any commuting pair of elements (that is, any /a/ and /b/ such that /a * b = b * a/).
--
-- If /zero = one/ in a ring /R/, then /R/ has only one element, and is called the zero ring.
-- Otherwise the additive identity, the additive inverse of each element, and the multiplicative identity are unique.
--
-- If the ring is < https://en.wikipedia.org/wiki/Ordered_ring ordered > (i.e. has an 'Ord' instance), then the following additional properties must hold:
--
-- @ a '<=' b ⇒ a '+' c '<=' b '+' c @
--
-- @ 'zero' '<=' a '&&' 'zero' '<=' b ⇒ 'zero' '<=' a '*' b @
--
class (Semiring a, RingLaw a) => Ring a where
 

  infixl 6 -

  -- | Subtract two elements.
  --
  -- @
  -- a '-' b = a + 'negate' b 
  -- @
  --
  (-) :: a -> a -> a
  a - b = a + negate b
  {-# INLINE (-) #-}
 
  -- | Absolute value of an element.
  --
  -- @ 'abs' x = x '*' 'signum' x @
  --
  abs :: Ord a => a -> a
  abs x = x * signum x
  {-# INLINE abs #-}

  -- | Extract the sign of an element.
  --
  -- 'signum' satisfies a trichotomy law:
  --
  -- @ 'signum' r = 'negate' r || 'zero' || r @
  -- 
  -- This follows from the fact that ordered rings are abelian, linearly 
  -- ordered groups with respect to addition.
  --
  -- See < https://en.wikipedia.org/wiki/Linearly_ordered_group >.
  --
  signum :: Ord a => a -> a
  signum x = bool (negate one) one $ zero P.<= x
  {-# INLINE signum #-}

-- | A monotone function from the integers to /a/.
--
-- This is a lawful replacement for the version in base.
--
--fromInteger :: ConnInteger a => Integer -> a
--fromInteger = connr connection . Just

-------------------------------------------------------------------------------
-- Fields
-------------------------------------------------------------------------------

-- | A < https://en.wikipedia.org/wiki/Field_(mathematics) field >.
--
class (Ring a, Semifield a, FieldLaw a) => Field a where

  -- | The negative infinity of the field.
  --
  -- @ 'ninf' = 'negate' 'one' '/' 'zero' @
  --
  ninf :: a
  ninf = negate one / zero
  {-# INLINE ninf #-}

-- | A lawful replacement for the version in base.
--
-- >>> fromRational @Float 1.3
-- 1.3
-- >>> fromRational @Float (1 :% 0)
-- Infinity
-- >>> fromRational @Float (0 :% 0)
-- NaN
--
fromRational :: Triple Rational a => Rational -> a
fromRational = round

-- | TODO: Document
--
round1 :: Ring a => Triple a b => (a -> a) -> b -> b
round1 = lift1 Round

round2 :: Ring a => Triple a b => (a -> a -> a) -> b -> b -> b
round2 = lift2 Round
{-# INLINE round2 #-}

round3 :: Ring a => Triple a b => (a -> a -> a -> a) -> b -> b -> b -> b
round3 = lift3 Round
{-# INLINE round3 #-}

---------------------------------------------------------------------
-- Rounding
---------------------------------------------------------------------

-- | The four primary IEEE rounding modes.
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
--
data RoundMode = 
    Round  -- ^ round to nearest with ties away from 0
  | Floor -- ^ round towards neg infinity
  | Ceiling -- ^ round towards pos infinity
  | Truncate -- ^ round towards 0
  deriving (Eq, Show)

-- | TODO: Document
--
-- > round = lift0 Round
-- > floor = lift0 Floor
-- > ceiling = lift0 Ceiling
-- > truncate = lift0 Truncate
--
lift0 :: (Ring a, Triple a b) => RoundMode -> a -> b
lift0 Round = roundOn triple
lift0 Floor = floorOn triple
lift0 Ceiling = ceilingOn triple
lift0 Truncate = truncateOn triple

-- | TODO: Document
--
-- > lift1 :: TripRational a => RoundMode -> (Rational -> Rational) -> a -> a
--
lift1 :: Ring a => Triple a b => RoundMode -> (a -> a) -> b -> b
lift1 rm f x = lift0 rm $ f (g x) where Trip _ g _ = triple
{-# INLINE lift1 #-}

-- | TODO: Document
--
-- >>> f x y = (x + y) - x 
-- >>> maxOdd32 = 1.6777215e7
-- >>> maxOdd64 = 9.007199254740991e15
-- >>> f maxOdd32 2.0 :: Float
-- 1.0
-- >>> lift2 @Rational @Float Round f maxOdd32 2.0
-- 2.0
-- >>> f maxOdd64 2.0 :: Double
-- 1.0
-- >>> lift2 @Rational @Double Round f maxOdd64 2.0
-- 2.0
--
lift2 :: Ring a => Triple a b => RoundMode -> (a -> a -> a) -> b -> b -> b
lift2 rm f x y = lift0 rm $ f (g x) (g y) where Trip _ g _ = triple
{-# INLINE lift2 #-}

-- | TODO: Document
--
lift3 :: Ring a => Triple a b => RoundMode -> (a -> a -> a -> a) -> b -> b -> b -> b
lift3 rm f x y z = lift0 rm $ f (g x) (g y) (g z) where Trip _ g _ = triple
{-# INLINE lift3 #-}

-- | Round-to-nearest. Ties are rounded away from zero.
--
-- 'round' can be used to build lawful replacements for 'Prelude.round':
--
-- >>> round32 = mapNan (bounded id) . round @Float
-- >>> P.round @Float @Int8 $ 0/0
-- 0
-- >>> round32 @Int8 $ 0/0
-- Nan
-- >>> P.round @Float @Int8 $ 1/0
-- 0
-- >>> round32 @Int8 $ 1/0
-- Def 127
-- >>> P.round @Float @Int8 129
-- -127
-- >>> round32 @Int8 129
-- Def 127
-- >>> P.round @Float @Int8 $ -129
-- 127
-- >>> round32 @Int8 $ -129
-- Def (-128)
-- >>> P.round @Float @Int8 $ -130
-- 126
-- >>> round32 @Int8 $ -130
-- Def (-128)
-- 
round :: (Ring a, Triple a b) => a -> b
round = roundOn triple

-- | Truncate towards zero.
--
-- >>> truncate32 = mapNan (bounded id) . truncate @Float
-- >>> truncate32 @Int16 5.4
-- Def 5
-- >>> truncate32 @Int16 (-5.4)
-- Def (-5)
--
truncate :: (Ring a, Triple a b) => a -> b
truncate = truncateOn triple

-- | Return the nearest value to x.
--
-- If x lies halfway between two values, then return the value with the
-- larger absolute value (i.e. round away from zero).
--
-- @ roundOn C.id == id @
-- 
roundOn :: (Prd a, Ring a) => Trip a b -> a -> b
roundOn t x | above t x = ceilingOn t x -- upper half interval
            | below t x = floorOn t x -- lower half interval
            | otherwise = bool (ceilingOn t x) (floorOn t x) $ x <= zero

-- @ truncateOn C.id == id @
truncateOn :: (Ring a, Prd a) => Trip a b -> a -> b
truncateOn t x = bool (ceilingOn t x) (floorOn t x) $ x >= zero

-- | Determine which half of the interval between two representations of /a/ a particular value lies.
-- 
half :: (Ring a, Prd a) => Trip a b -> a -> Maybe Ordering
half t x = pcompare (x - unitl t x) (counitr t x - x) 

-- | Determine whether /x/ lies exactly halfway between two representations.
-- 
-- @ 'tied' t x '==' (x '-' 'unitl' t x) '=~' ('counitr' t x '-' x) @
--
tied :: (Ring a, Prd a) => Trip a b -> a -> Bool
tied t = maybe False (== EQ) . half t

-- | Determine whether /x/ lies below the halfway point between two representations.
-- 
-- @ 'below' t x '==' (x '-' 'unitl' t x) '<' ('counitr' t x '-' x) @
--
below :: (Ring a, Prd a) => Trip a b -> a -> Bool
below t = maybe False (== LT) . half t

-- | Determine whether /x/ lies above the halfway point between two representations.
-- 
-- @ 'above' t x '==' (x '-' 'unitl' t x) '>' ('counitr' t x '-' x) @
--
above :: (Ring a, Prd a) => Trip a b -> a -> Bool
above t = maybe False (== GT) . half t

{-
deriving via (Ap ((->)a) b) instance Ring b => Ring (a -> b)
deriving via (Ap Dual a) instance Ring a => Ring (Dual a)
-- the component-wise multiplication semiring. use the semimodule instances and .#. for matrix mult.
deriving via (Ap (f**g) a) instance (Applicative f, Applicative g, Ring a) => Ring ((f**g) a) 
deriving via (Ap (f++g) a) instance (Applicative f, Applicative g, Ring a) => Ring ((f++g) a) 

instance Ring a => Ring (Op a b) where
  Op f - Op g = Op $ \b -> f b - g b
  {-# INLINE (-) #-}

instance (Ring a, Ring b) => Ring (a, b) where
  (x1,y1) - (x2,y2) = (x1-x2, y1-y2)

instance (Ring a, Ring b, Ring c) => Ring (a, b, c) where
  (x1,y1,z1) - (x2,y2,z2) = (x1-x2, y1-y2, z1-z2)

-}

instance Ring ()
instance Field ()

instance Ring Int
instance Ring Int8
instance Ring Int16
instance Ring Int32
instance Ring Int64
instance Ring Integer

instance Ring Uni
instance Ring Deci
instance Ring Centi
instance Ring Milli
instance Ring Micro
instance Ring Nano
instance Ring Pico
instance Field Uni
instance Field Deci
instance Field Centi
instance Field Milli
instance Field Micro
instance Field Nano
instance Field Pico

instance Ring Float
instance Ring Double
instance Field Float
instance Field Double

instance Ring a => Ring (Ratio a)
instance Ring a => Field (Ratio a)

instance Ring a => Ring (Complex a)
instance Field a => Field (Complex a)
