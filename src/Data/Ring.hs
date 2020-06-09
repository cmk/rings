{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}
{-# Language DeriveFunctor       #-}
{-# Language DeriveGeneric       #-}
{-# Language DerivingVia         #-}
{-# Language StandaloneDeriving  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Ring (
  -- * Constraint kinds
    type (-)
  , PresemiringLaw
  , SemiringLaw
  , SemifieldLaw
  , RingLaw
  , FieldLaw
  -- * Presemirings 
  , Presemiring(..)
  , (+), (*)
  -- * Semirings 
  , Semiring(..)
  , zero, one
  , fromNatural
  , type NaturalSemiring
  , type Natural
    -- * Rings
  , Ring(..)
  , negate
  , fromInteger
  , type IntegerRing
  , type Integer
  -- * Semifields
  , Semifield(..)
  , recip
  , fromPositive
  , type PositiveSemifield
  , type Positive
    -- * Fields
  , Field(..)
  , fromRational
  , type RationalField
  , type Rational
    -- * Rounding
  , round
  , floor
  , ceiling
  , truncate
  , midpoint
  , half
  , tied
  , below
  , above
) where

import safe Control.Applicative
import safe Data.Bool
--import safe Data.Complex
import safe Data.Connection
import safe Data.Connection.Type
import safe Data.Foldable as Foldable (foldl',foldr')
import safe Data.Functor.Identity
import safe Data.Int
import safe Data.Maybe
import safe Data.Order
import safe Data.Semiring
import safe Data.Semigroup.Additive
import safe GHC.Real (Rational)
import safe Prelude
 ( Eq(..), Ord, Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..)
 , id, flip, const, (.), ($), Integer, Float, Double, Ordering(..) )

-------------------------------------------------------------------------------
-- Rings
-------------------------------------------------------------------------------

type IntegerRing a = (Ring a, Connection Integer a)

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
-- @ a '<~' b ⇒ a '+' c '<~' b '+' c @
--
-- @ 'zero' '<~' a '&&' 'zero' '<~' b ⇒ 'zero' '<~' a '*' b @
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
    abs :: Preorder a => a -> a
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
    signum :: Preorder a => a -> a
    signum x = bool (negate one) one $ zero <~ x
    {-# INLINE signum #-}

-------------------------------------------------------------------------------
-- Fields
-------------------------------------------------------------------------------

type RationalField a = (Field a, Triple Rational a)

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

---------------------------------------------------------------------
-- Rounding
---------------------------------------------------------------------

-- | Return the nearest value to x.
--
-- > round @a @a = id
-- 
-- If x lies halfway between two values, then return the value with the
-- larger absolute value (i.e. round away from zero).
--
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
round :: forall a b. (Preorder a, Ring a, Triple a b) => a -> b
round x =
  case half (triple @a @b) x of
    Just GT -> ceiling x -- upper half interval
    Just LT -> floor x   -- lower half interval
    _       -> bool (ceiling x) (floor x) $ x <~ zero

-- | Truncate towards zero.
--
-- > truncate @a @a = id
--
-- >>> truncate32 = mapNan (bounded id) . truncate @Float
-- >>> truncate32 @Int16 5.4
-- Def 5
-- >>> truncate32 @Int16 (-5.4)
-- Def (-5)
--
truncate :: (Preorder a, Ring a, Triple a b) => a -> b
truncate x = bool (ceiling x) (floor x) $ x >~ zero

-- | Return the midpoint of the interval containing x.
--
-- >>> midpoint f64f32 P.pi
-- 1.1920928955078125e-7
-- >>> midpoint f64f32 nan
-- NaN
--
midpoint :: (Preorder a, Field a) => Trip a b -> a -> a
midpoint t x = (unitl t x - counitr t x) / (one + one)

-- | Determine which half of the interval between two representations of /a/ a particular value lies.
-- 
half :: (Preorder a, Ring a) => Trip a b -> a -> Maybe Ordering
half t x = pcompare (x - unitl t x) (counitr t x - x) 

-- | Determine whether /x/ lies exactly halfway between two representations.
-- 
-- @ 'tied' t x '~~' (x '-' 'unitl' t x) '=~' ('counitr' t x '-' x) @
--
tied :: (Preorder a, Ring a) => Trip a b -> a -> Bool
tied t = maybe False (~~ EQ) . half t

-- | Determine whether /x/ lies below the halfway point between two representations.
-- 
-- @ 'below' t x '~~' (x '-' 'unitl' t x) '<' ('counitr' t x '-' x) @
--
below :: (Preorder a, Ring a) => Trip a b -> a -> Bool
below t = maybe False (~~ LT) . half t

-- | Determine whether /x/ lies above the halfway point between two representations.
-- 
-- @ 'above' t x '~~' (x '-' 'unitl' t x) '>' ('counitr' t x '-' x) @
--
above :: (Preorder a, Ring a) => Trip a b -> a -> Bool
above t = maybe False (~~ GT) . half t

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

{-
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
-}

instance Ring Float
instance Field Float

instance Ring Double
instance Field Double

instance Ring Rational
instance Field Rational

instance Ring a => Ring (Identity a) 
instance Field a => Field (Identity a) 
--instance Ring a => Ring (Complex a)
--instance Field a => Field (Complex a)
