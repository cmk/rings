{-# LANGUAGE Safe                       #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}

{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE PatternSynonyms         #-}
{-# LANGUAGE PolyKinds         #-}


{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Data.Semiring (
  -- * Types
    type (-)
  -- * Semiring laws
  , PresemiringLaw
  , SemiringLaw
  , SemifieldLaw
  , RingLaw
  , FieldLaw
  -- * Additive groups 
  , (+)
  , zero
  , negate
  , sum
  , sum1
  , sumWith
  , sumWith1
  -- * Multiplicative groups 
  , (*)
  , one
  , recip
  , product
  , product1
  , productWith
  , productWith1
  -- * Semirings 
  , Presemiring(..)
  , Semiring(..)
  , Church
  , church
  , runChurch
  , fromNatural
  , type Natural
  -- * Semifields
  , Semifield(..)
  , fromPositive
  , type Positive
  -- * Newtypes
  , Additive(..)
  , Multiplicative(..)
  , F1(..)
  , F2(..)
  , mreplicate
) where

import safe Control.Category (Category, (>>>))
import safe Control.Applicative
--import safe Control.Applicative.Lift
import safe Data.Bool
import safe Data.Complex
import safe Data.Connection
import safe Data.Either
import safe Data.Tuple
import safe Data.Fixed
import safe Data.Foldable as Foldable (Foldable, foldl',foldMap)
import safe Data.Functor.Apply
import safe Data.Functor.Alt
import safe Data.Functor.Compose
import safe Data.Functor.Classes
import safe Data.Functor.Contravariant
import safe Data.Functor.Identity
import safe Data.Functor.Rep
import safe Data.Int
import safe Data.List.NonEmpty
import safe Data.Maybe
import safe Data.Monoid hiding (Alt)
import safe Data.Ord (Down(..), Ordering(..))
import safe Data.Profunctor
import safe Data.Profunctor.Yoneda
import safe Data.Semigroup
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Semigroup.Traversable (Traversable1)
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic, Generic1)
import safe GHC.Real (Ratio(..), Rational)
import safe Numeric.Natural
import safe Prelude
 ( Eq(..), Ord, IO, Show(..), Applicative(..), Functor(..), Traversable, Monoid(..), Semigroup(..)
 , id, flip, const, (.), ($), Integer, Float, Double, fst, snd, uncurry, quot, even)
import safe Data.IntMap (IntMap)
import safe Data.IntSet (IntSet)
import safe Data.Map (Map)
import safe Data.Set (Set)
import safe Data.Semilattice
import safe Data.Sequence (Seq)
import safe qualified Data.Foldable as Foldable
import safe qualified Data.Functor.Product as F
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set
import safe qualified Data.Monoid as M
import safe qualified Prelude as P
import safe qualified Control.Category as C
import safe Data.Kind
import safe Data.Group


-------------------------------------------------------------------------------
-- Semiring laws
-------------------------------------------------------------------------------

type PresemiringLaw a = ((Additive-Semigroup) a, (Multiplicative-Semigroup) a)

type SemiringLaw a = ((Additive-Monoid) a, (Multiplicative-Monoid) a)

type SemifieldLaw a = ((Additive-Monoid) a, (Multiplicative-Group) a)

type RingLaw a = ((Additive-Group) a, (Multiplicative-Monoid) a)

type FieldLaw a = ((Additive-Group) a, (Multiplicative-Group) a)

---------------------------------------------------------------------
-- Additive groups
---------------------------------------------------------------------

-- | A commutative 'Semigroup' under '+'.
newtype Additive a = Add { getAdd :: a }
  deriving stock (Eq, Generic, Ord, Show)
  deriving (Functor, Applicative) via Identity

infixl 6 +

-- | Additive semigroup operation on a semiring.
--
-- >>> Dual [2] + Dual [3] :: Dual [Int]
-- Dual {getDual = [3,2]}
--
(+) :: (Additive-Semigroup) a => a -> a -> a
x + y = getAdd $ Add x <> Add y
{-# INLINE (+) #-}

-- | Additive unit of a semiring.
--
zero :: (Additive-Monoid) a => a
zero = getAdd mempty
{-# INLINE zero #-}

-- | Reverse the sign of an element.
--
negate :: (Additive-Group) a => a -> a
negate = getAdd . invert . Add
{-# INLINE negate #-}

-- | Evaluate a semiring sum.
-- 
-- >>> sum [1..5 :: Int]
-- 15
--
sum :: (Additive-Monoid) a => Foldable f => f a -> a
sum = sumWith id

-- | Evaluate a non-empty presemiring sum.
--
sum1 :: (Additive-Semigroup) a => Foldable1 f => f a -> a
sum1 = sumWith1 id

-- | Evaluate a semiring sum using a given semiring.
-- 
sumWith :: (Additive-Monoid) a => Foldable f => (b -> a) -> f b -> a
sumWith f = getAdd . foldMap (Add . f)
{-# INLINE sumWith #-}

-- | Evaluate a non-empty presemiring sum using a given presemiring.
-- 
-- >>> reduceWith1 Max $ (1 :| [2..5 :: Int]) :| [1 :| [2..5 :: Int]]
-- | Fold over a non-empty collection using the additive operation of an arbitrary semiring.
--
-- >>> sumWith1 First $ (1 :| [2..5 :: Int]) * (1 :| [2..5 :: Int])
-- First {getFirst = 1}
-- >>> sumWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
-- >>> sumWith1 Just $ 1 :| [2..5 :: Int]
-- Just 15
--
sumWith1 :: (Additive-Semigroup) a => Foldable1 t => (b -> a) -> t b -> a
sumWith1 f = getAdd . foldMap1 (Add . f)
{-# INLINE sumWith1 #-}

---------------------------------------------------------------------
-- Multiplicative groups
---------------------------------------------------------------------

-- | A 'Semigroup' under '*'.
newtype Multiplicative a = Mul { getMul :: a }
  deriving stock (Eq, Generic, Ord, Show)
  deriving (Functor, Applicative) via Identity

infixl 7 *

-- | Multiplicative semigroup operation on a semiring.
--
-- >>> Dual [2] * Dual [3] :: Dual [Int]
-- Dual {getDual = [5]}
--
(*) :: (Multiplicative-Semigroup) a => a -> a -> a
x * y = let Mul z = Mul x <> Mul y in z
{-# INLINE (*) #-}

-- | Multiplicative unit of a semiring.
--
one :: (Multiplicative-Monoid) a => a
one = getMul mempty
{-# INLINE one #-}

-- | Reciprocal of a multiplicative group element.
--
-- @ 
-- 'recip' x = 'one' '/' x
-- @
--
-- >>> recip (3 :+ 4) :: Complex Rational
-- 3 % 25 :+ (-4) % 25
-- >>> recip (3 :+ 4) :: Complex Double
-- 0.12 :+ (-0.16)
-- >>> recip (3 :+ 4) :: Complex Pico
-- 0.120000000000 :+ -0.160000000000
-- 
recip :: (Multiplicative-Group) a => a -> a
recip = getMul . invert . Mul
{-# INLINE recip #-}

-- | Evaluate a semiring product.
--
-- >>> product [1..5 :: Int]
-- 120
--
product :: (Multiplicative-Monoid) a => Foldable f => f a -> a
product = productWith id

-- | Evaluate a non-empty presemiring product.
--
product1 :: (Multiplicative-Semigroup) a => Foldable1 f => f a -> a
product1 = productWith1 id

-- | Evaluate a semiring product using a given semiring.
--
-- @
-- 'product' f = 'Data.foldr'' (('*') . f) 'one'
-- @
--
-- >>> productWith Just [1..5 :: Int]
-- Just 120
--
productWith :: (Multiplicative-Monoid) a => Foldable f => (b -> a) -> f b -> a
productWith f = getMul . foldMap (Mul . f)
{-# INLINE productWith #-}

-- | Evaluate a non-empty presemiring product using a given presemiring.
-- 
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> productWith1 Just $ 1 :| [2..5 :: Int]
-- Just 120
-- >>> productWith1 First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
-- >>> productWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
productWith1 :: (Multiplicative-Semigroup) a => Foldable1 t => (b -> a) -> t b -> a
productWith1 f = getMul . foldMap1 (Mul . f)
{-# INLINE productWith1 #-}

-------------------------------------------------------------------------------
-- Presemirings
-------------------------------------------------------------------------------

-- | Right pre-semirings. and (non-unital and unital) right semirings.
-- 
-- A right pre-semiring (sometimes referred to as a bisemigroup) is a type /R/ endowed 
-- with two associative binary (i.e. semigroup) operations: '+' and '*', along with a 
-- right-distributivity property connecting them:
--
-- /Distributivity/
--
-- @
-- (a '+' b) '*' c = (a '*' c) '+' (b '*' c)
-- @
--
-- Note that multiplication needn't be commutative.
--
class PresemiringLaw a => Presemiring a where

  -- | Reduce a free presemiring expression.
  -- 
  reduce1 :: (Foldable1 f, Functor f) => f (f a) -> a
  reduce1 = sum1 . fmap product1
  {-# INLINE reduce1 #-}

  -- | Cross-multiply two non-empty collections.
  --
  -- >>> cross1 (Right 2 :| [Left False]) (Right 2 :| [Right 3]) :: Either Bool Int
  -- Right 10
  --
  cross1 :: (Foldable1 f, Apply f) => f a -> f a -> a
  cross1 a b = sum1 $ liftF2 (*) a b
  {-# INLINE cross1 #-}

-------------------------------------------------------------------------------
-- Semirings
-------------------------------------------------------------------------------


-- | Right semirings.
-- 
-- A right semiring is a pre-semiring with two distinct neutral elements, 'zero' 
-- and 'one', such that 'zero' is right-neutral wrt addition, 'one' is right-neutral wrt
-- multiplication, and 'zero' is right-annihilative wrt multiplication. 
--
-- /Neutrality/
--
-- @
-- 'zero' '+' a = a
-- 'one' '*' a = a
-- @
--
-- /Absorbtion/
--
-- @
-- 'zero' '*' a = 'zero'
-- @
--
class (Presemiring a, SemiringLaw a) => Semiring a where

  -- | Reduce a free semiring expression.
  -- 
  -- @ (a11 * .. * a1m) + (a21 * .. * a2n) + ... @
  --
  -- >>> reduce [[1, 2], [3, 4 :: Int]] -- 1 * 2 + 3 * 4
  -- 14
  -- >>> reduce $ sequence [[1, 2], [3, 4 :: Int]] -- (1 + 2) * (3 + 4)
  -- 21
  -- >>> reduce . (fmap . fmap) Max $ [[1..4 :: Int], [0..2 :: Int]]
  -- Max {getMax = 24}
  --
  reduce :: (Foldable f, Functor f) => f (f a) -> a
  reduce = sum . fmap product
  {-# INLINE reduce #-}

  -- | Cross-multiply two collections.
  --
  -- >>> cross [1,2,3 :: Int] [1,2,3]
  -- 36
  -- >>> cross [1,2,3 :: Int] []
  -- 0
  --
  cross :: (Foldable f, Applicative f) => f a -> f a -> a
  cross a b = sum $ liftA2 (*) a b
  {-# INLINE cross #-}

  infixr 8 ^

  -- | Evaluate a natural-numbered power of a semiring element.
  --
  -- @ 'one' = a '^' 'zero' @
  --
  -- >>> 8 ^ zero :: Int
  -- 1
  --
  (^) :: a -> Natural -> a
  x ^ n = getMul $ mreplicate (P.fromIntegral n) (Mul x)

  sign :: (Eq a, Lattice a) => a -> Maybe Ordering
  sign x = pcompare x zero

--sign :: (Eq a, (Additive-Monoid) a, (Join-Monoid) a) => a -> Maybe Ordering
--sign x = pcompareJoin x zero

-- | A free semiring.
--
-- The final (i.e. Church / Boehm-Berarducci) encoding of an arbitrary semiring is:
--
-- > forall a. (a -> a) -> a -> a
--
type Church a = Endo (Endo a)

church :: Semiring a => a -> Church a
church a = Endo $ \(Endo f) -> Endo (\y -> a * f zero + y)

-- | Evaluate a free semiring expression.
--
-- >>> runChurch $ (one + one) * (one + (cayley 3.4)) :: Double
-- 8.8
--
runChurch :: Semiring a => Church a -> a
runChurch (Endo f) = appEndo (f $ Endo (one +)) zero

{-
-- | The Min-plus dioid.
type MinPlus a = Min a

-- | The Max-plus dioid.
type MaxPlus a = Min (Down a)

-- | The Min-times dioid.
type MinTimes a = Max (Down a)

-- | The Max-times dioid.
type MaxTimes a = Max a
-}

-------------------------------------------------------------------------------
-- Semifields
-------------------------------------------------------------------------------

-- | A semifield, near-field, or division ring.
--
-- Instances needn't have commutative multiplication or additive inverses,
-- however addition must be commutative, and addition and multiplication must 
-- be associative and distribute as usual.
--
-- See also the wikipedia definitions of:
--
-- * < https://en.wikipedia.org/wiki/SemifieldLaw semifield >
-- * < https://en.wikipedia.org/wiki/Near-field_(mathematics) near-field >
-- * < https://en.wikipedia.org/wiki/Division_ring division ring >
-- 
class (Semiring a, SemifieldLaw a) => Semifield a where

  -- | The /NaN/ value of the semifield.
  --
  -- @ 'nan' = 'zero' '/' 'zero' @
  --
  nan :: a
  nan = zero / zero
  {-# INLINE nan #-}

  -- | The positive infinity of the semifield.
  --
  -- @ 'pinf' = 'one' '/' 'zero' @
  --
  pinf :: a
  pinf = one / zero
  {-# INLINE pinf #-}

  infixl 7 /

  -- | Right division by a multiplicative group element.
  --
  -- @ 
  -- x '/' y = x '*' 'recip' y
  -- @
  --
  (/) :: a -> a -> a
  x / y = x * recip y
  {-# INLINE (/) #-}

  infixr 8 ^^

  -- | Integral power of a multiplicative group element.
  --
  -- @ 'one' '==' a '^^' 0 @
  --
  -- >>> 8 ^^ 0 :: Double
  -- 1.0
  -- >>> 8 ^^ 0 :: Pico
  -- 1.000000000000
  --
  (^^) :: a -> Integer -> a
  a ^^ n = getMul $ pow (Mul a) n

-- | A monotone map from 'Ratio Natural' to /a/.
--
fromPositive :: Triple Positive a => Positive -> a
fromPositive = floor

type Positive = Ratio Natural



---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

-- | A generalization of 'Data.List.replicate' to an arbitrary 'Monoid'. 
--
-- Adapted from <http://augustss.blogspot.com/2008/07/lost-and-found-if-i-write-108-in.html>.
--
mreplicate :: Monoid a => Natural -> a -> a
mreplicate n a
    | n == 0 = mempty
    | otherwise = f a n
    where
        f x y 
            | even y = f (x <> x) (y `quot` 2)
            | y == 1 = x
            | otherwise = g (x <> x) ((y P.- 1) `quot` 2) x
        g x y z 
            | even y = g (x <> x) (y `quot` 2) z
            | y == 1 = x <> z
            | otherwise = g (x <> x) ((y P.- 1) `quot` 2) (x <> z)
{-# INLINE mreplicate #-}

deriving via (F1 Additive ()) instance Semigroup (Additive ())
deriving via (F1 Additive ()) instance Monoid (Additive ())
deriving via (F1 Additive ()) instance Group (Additive ())
deriving via (F1 Multiplicative ()) instance Semigroup (Multiplicative ())
deriving via (F1 Multiplicative ()) instance Monoid (Multiplicative ())
deriving via (F1 Multiplicative ()) instance Group (Multiplicative ())
instance Presemiring ()
instance Semiring ()
instance Semifield ()

deriving via (F1 Additive Any) instance Semigroup (Additive Bool)
deriving via (F1 Additive Any) instance Monoid (Additive Bool)
deriving via (F1 Multiplicative All) instance Semigroup (Multiplicative Bool)
deriving via (F1 Multiplicative All) instance Monoid (Multiplicative Bool)
instance Presemiring Bool
instance Semiring Bool

instance Semigroup (Additive Ordering) where
  (<>) = liftA2 (\/)

instance Monoid (Additive Ordering) where
  mempty = pure LT

instance Semigroup (Multiplicative Ordering) where
  (<>) = liftA2 (/\)

instance Monoid (Multiplicative Ordering) where
  mempty = pure GT



deriving via (F1 Additive (Sum Word8)) instance Semigroup (Additive Word8)
deriving via (F1 Additive (Sum Word8)) instance Monoid (Additive Word8)
deriving via (F1 Multiplicative (Product Word8)) instance Semigroup (Multiplicative Word8)
deriving via (F1 Multiplicative (Product Word8)) instance Monoid (Multiplicative Word8)
instance Presemiring Word8
instance Semiring Word8

deriving via (F1 Additive (Sum Word16)) instance Semigroup (Additive Word16)
deriving via (F1 Additive (Sum Word16)) instance Monoid (Additive Word16)
deriving via (F1 Multiplicative (Product Word16)) instance Semigroup (Multiplicative Word16)
deriving via (F1 Multiplicative (Product Word16)) instance Monoid (Multiplicative Word16)
instance Presemiring Word16
instance Semiring Word16

deriving via (F1 Additive (Sum Word32)) instance Semigroup (Additive Word32)
deriving via (F1 Additive (Sum Word32)) instance Monoid (Additive Word32)
deriving via (F1 Multiplicative (Product Word32)) instance Semigroup (Multiplicative Word32)
deriving via (F1 Multiplicative (Product Word32)) instance Monoid (Multiplicative Word32)
instance Presemiring Word32
instance Semiring Word32

deriving via (F1 Additive (Sum Word64)) instance Semigroup (Additive Word64)
deriving via (F1 Additive (Sum Word64)) instance Monoid (Additive Word64)
deriving via (F1 Multiplicative (Product Word64)) instance Semigroup (Multiplicative Word64)
deriving via (F1 Multiplicative (Product Word64)) instance Monoid (Multiplicative Word64)
instance Presemiring Word64
instance Semiring Word64

deriving via (F1 Additive (Sum Word)) instance Semigroup (Additive Word)
deriving via (F1 Additive (Sum Word)) instance Monoid (Additive Word)
deriving via (F1 Multiplicative (Product Word)) instance Semigroup (Multiplicative Word)
deriving via (F1 Multiplicative (Product Word)) instance Monoid (Multiplicative Word)
instance Presemiring Word
instance Semiring Word

deriving via (F1 Additive (Sum Natural)) instance Semigroup (Additive Natural)
deriving via (F1 Additive (Sum Natural)) instance Monoid (Additive Natural)
deriving via (F1 Multiplicative (Product Natural)) instance Semigroup (Multiplicative Natural)
deriving via (F1 Multiplicative (Product Natural)) instance Monoid (Multiplicative Natural)
instance Presemiring Natural
instance Semiring Natural

deriving via (F1 Additive (Sum Int8)) instance Semigroup (Additive Int8)
deriving via (F1 Additive (Sum Int8)) instance Monoid (Additive Int8)
deriving via (F1 Additive (Sum Int8)) instance Group (Additive Int8)
deriving via (F1 Multiplicative (Product Int8)) instance Semigroup (Multiplicative Int8)
deriving via (F1 Multiplicative (Product Int8)) instance Monoid (Multiplicative Int8)
instance Presemiring Int8
instance Semiring Int8

deriving via (F1 Additive (Sum Int16)) instance Semigroup (Additive Int16)
deriving via (F1 Additive (Sum Int16)) instance Monoid (Additive Int16)
deriving via (F1 Additive (Sum Int16)) instance Group (Additive Int16)
deriving via (F1 Multiplicative (Product Int16)) instance Semigroup (Multiplicative Int16)
deriving via (F1 Multiplicative (Product Int16)) instance Monoid (Multiplicative Int16)
instance Presemiring Int16
instance Semiring Int16

deriving via (F1 Additive (Sum Int32)) instance Semigroup (Additive Int32)
deriving via (F1 Additive (Sum Int32)) instance Monoid (Additive Int32)
deriving via (F1 Additive (Sum Int32)) instance Group (Additive Int32)
deriving via (F1 Multiplicative (Product Int32)) instance Semigroup (Multiplicative Int32)
deriving via (F1 Multiplicative (Product Int32)) instance Monoid (Multiplicative Int32)
instance Presemiring Int32
instance Semiring Int32

deriving via (F1 Additive (Sum Int64)) instance Semigroup (Additive Int64)
deriving via (F1 Additive (Sum Int64)) instance Monoid (Additive Int64)
deriving via (F1 Additive (Sum Int64)) instance Group (Additive Int64)
deriving via (F1 Multiplicative (Product Int64)) instance Semigroup (Multiplicative Int64)
deriving via (F1 Multiplicative (Product Int64)) instance Monoid (Multiplicative Int64)
instance Presemiring Int64
instance Semiring Int64

deriving via (F1 Additive (Sum Int)) instance Semigroup (Additive Int)
deriving via (F1 Additive (Sum Int)) instance Monoid (Additive Int)
deriving via (F1 Additive (Sum Int)) instance Group (Additive Int)
deriving via (F1 Multiplicative (Product Int)) instance Semigroup (Multiplicative Int)
deriving via (F1 Multiplicative (Product Int)) instance Monoid (Multiplicative Int)
instance Presemiring Int
instance Semiring Int

deriving via (F1 Additive (Sum Integer)) instance Semigroup (Additive Integer)
deriving via (F1 Additive (Sum Integer)) instance Monoid (Additive Integer)
deriving via (F1 Additive (Sum Integer)) instance Group (Additive Integer)
deriving via (F1 Multiplicative (Product Integer)) instance Semigroup (Multiplicative Integer)
deriving via (F1 Multiplicative (Product Integer)) instance Monoid (Multiplicative Integer)
instance Presemiring Integer
instance Semiring Integer

deriving via (F1 Additive (Sum Uni)) instance Semigroup (Additive Uni)
deriving via (F1 Additive (Sum Uni)) instance Monoid (Additive Uni)
deriving via (F1 Additive (Sum Uni)) instance Group (Additive Uni)
deriving via (F1 Multiplicative (Product Uni)) instance Semigroup (Multiplicative Uni)
deriving via (F1 Multiplicative (Product Uni)) instance Monoid (Multiplicative Uni)
deriving via (F1 Multiplicative (Product Uni)) instance Group (Multiplicative Uni)
instance Presemiring Uni
instance Semiring Uni
instance Semifield Uni

deriving via (F1 Additive (Sum Deci)) instance Semigroup (Additive Deci)
deriving via (F1 Additive (Sum Deci)) instance Monoid (Additive Deci)
deriving via (F1 Additive (Sum Deci)) instance Group (Additive Deci)
deriving via (F1 Multiplicative (Product Deci)) instance Semigroup (Multiplicative Deci)
deriving via (F1 Multiplicative (Product Deci)) instance Monoid (Multiplicative Deci)
deriving via (F1 Multiplicative (Product Deci)) instance Group (Multiplicative Deci)
instance Presemiring Deci
instance Semiring Deci
instance Semifield Deci

deriving via (F1 Additive (Sum Centi)) instance Semigroup (Additive Centi)
deriving via (F1 Additive (Sum Centi)) instance Monoid (Additive Centi)
deriving via (F1 Additive (Sum Centi)) instance Group (Additive Centi)
deriving via (F1 Multiplicative (Product Centi)) instance Semigroup (Multiplicative Centi)
deriving via (F1 Multiplicative (Product Centi)) instance Monoid (Multiplicative Centi)
deriving via (F1 Multiplicative (Product Centi)) instance Group (Multiplicative Centi)
instance Presemiring Centi
instance Semiring Centi
instance Semifield Centi

deriving via (F1 Additive (Sum Milli)) instance Semigroup (Additive Milli)
deriving via (F1 Additive (Sum Milli)) instance Monoid (Additive Milli)
deriving via (F1 Additive (Sum Milli)) instance Group (Additive Milli)
deriving via (F1 Multiplicative (Product Milli)) instance Semigroup (Multiplicative Milli)
deriving via (F1 Multiplicative (Product Milli)) instance Monoid (Multiplicative Milli)
deriving via (F1 Multiplicative (Product Milli)) instance Group (Multiplicative Milli)
instance Presemiring Milli
instance Semiring Milli
instance Semifield Milli

deriving via (F1 Additive (Sum Micro)) instance Semigroup (Additive Micro)
deriving via (F1 Additive (Sum Micro)) instance Monoid (Additive Micro)
deriving via (F1 Additive (Sum Micro)) instance Group (Additive Micro)
deriving via (F1 Multiplicative (Product Micro)) instance Semigroup (Multiplicative Micro)
deriving via (F1 Multiplicative (Product Micro)) instance Monoid (Multiplicative Micro)
deriving via (F1 Multiplicative (Product Micro)) instance Group (Multiplicative Micro)
instance Presemiring Micro
instance Semiring Micro
instance Semifield Micro

deriving via (F1 Additive (Sum Nano)) instance Semigroup (Additive Nano)
deriving via (F1 Additive (Sum Nano)) instance Monoid (Additive Nano)
deriving via (F1 Additive (Sum Nano)) instance Group (Additive Nano)
deriving via (F1 Multiplicative (Product Nano)) instance Semigroup (Multiplicative Nano)
deriving via (F1 Multiplicative (Product Nano)) instance Monoid (Multiplicative Nano)
deriving via (F1 Multiplicative (Product Nano)) instance Group (Multiplicative Nano)
instance Presemiring Nano
instance Semiring Nano
instance Semifield Nano

deriving via (F1 Additive (Sum Pico)) instance Semigroup (Additive Pico)
deriving via (F1 Additive (Sum Pico)) instance Monoid (Additive Pico)
deriving via (F1 Additive (Sum Pico)) instance Group (Additive Pico)
deriving via (F1 Multiplicative (Product Pico)) instance Semigroup (Multiplicative Pico)
deriving via (F1 Multiplicative (Product Pico)) instance Monoid (Multiplicative Pico)
deriving via (F1 Multiplicative (Product Pico)) instance Group (Multiplicative Pico)
instance Presemiring Pico
instance Semiring Pico
instance Semifield Pico

deriving via (F1 Additive (Sum Float)) instance Semigroup (Additive Float)
deriving via (F1 Additive (Sum Float)) instance Monoid (Additive Float)
deriving via (F1 Additive (Sum Float)) instance Group (Additive Float)
deriving via (F1 Multiplicative (Product Float)) instance Semigroup (Multiplicative Float)
deriving via (F1 Multiplicative (Product Float)) instance Monoid (Multiplicative Float)
deriving via (F1 Multiplicative (Product Float)) instance Group (Multiplicative Float)
instance Presemiring Float
instance Semiring Float
instance Semifield Float

deriving via (F1 Additive (Sum Double)) instance Semigroup (Additive Double)
deriving via (F1 Additive (Sum Double)) instance Monoid (Additive Double)
deriving via (F1 Additive (Sum Double)) instance Group (Additive Double)
deriving via (F1 Multiplicative (Product Double)) instance Semigroup (Multiplicative Double)
deriving via (F1 Multiplicative (Product Double)) instance Monoid (Multiplicative Double)
deriving via (F1 Multiplicative (Product Double)) instance Group (Multiplicative Double)
instance Presemiring Double
instance Semiring Double
instance Semifield Double

instance PresemiringLaw a => Semigroup (Additive (Ratio a)) where
  (<>) = liftA2 addRatio

instance SemiringLaw a => Monoid (Additive (Ratio a)) where
  mempty = Add $ zero :% one

instance RingLaw a => Group (Additive (Ratio a)) where
  invert = fmap $ subRatio zero

instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (Ratio a)) where
  (<>) = liftA2 mulRatio

instance Monoid (Multiplicative a) => Monoid (Multiplicative (Ratio a)) where
  mempty = Mul $ one :% one

instance Monoid (Multiplicative a) => Group (Multiplicative (Ratio a)) where
  invert = fmap $ divRatio one

instance Presemiring a => Presemiring (Ratio a)
instance Semiring a => Semiring (Ratio a)
instance Semiring a => Semifield (Ratio a)

addRatio :: (Semigroup (Additive a), Semigroup (Multiplicative a)) => Ratio a -> Ratio a -> Ratio a
addRatio (a :% b) (c :% d) = (a * d + c * b) :% (b * d)

subRatio :: (Group (Additive a), Semigroup (Multiplicative a)) => Ratio a -> Ratio a -> Ratio a
subRatio (a :% b) (c :% d) = (a * d + negate (c * b)) :% (b * d)

mulRatio :: Semigroup (Multiplicative a) => Ratio a -> Ratio a -> Ratio a
mulRatio (a :% b) (c :% d) = (a * c) :% (b * d)

divRatio :: Semigroup (Multiplicative a) => Ratio a -> Ratio a -> Ratio a
divRatio (a :% b) (c :% d) = (a * d) :% (b * c)

instance Semigroup (Additive a) => Semigroup (Additive (Complex a)) where
  (<>) = liftA2 addComplex

instance Monoid (Additive a) => Monoid (Additive (Complex a)) where
  mempty = Add $ zero :+ zero

instance Group (Additive a) => Group (Additive (Complex a)) where
  invert = fmap $ subComplex zero

instance RingLaw a => Semigroup (Multiplicative (Complex a)) where
  (<>) = liftA2 mulComplex

instance RingLaw a => Monoid (Multiplicative (Complex a)) where
  mempty = Mul $ one :+ zero

instance FieldLaw a => Group (Multiplicative (Complex a)) where
  invert = fmap $ divComplex one

instance RingLaw a => Presemiring (Complex a)
instance RingLaw a => Semiring (Complex a)
instance FieldLaw a => Semifield (Complex a)

addComplex :: Semigroup (Additive a) => Complex a -> Complex a -> Complex a
addComplex (a :+ b) (c :+ d) = (a + c) :+ (b + d)

subComplex :: Group (Additive a) => Complex a -> Complex a -> Complex a
subComplex (a :+ b) (c :+ d) = (a + negate c) :+ (b + negate d)

mulComplex :: (Group (Additive a), Semigroup (Multiplicative a)) => Complex a -> Complex a -> Complex a
mulComplex (a :+ b) (c :+ d) = (a * c + negate (b * d)) :+ (b * c + a * d)

divComplex :: (Group (Multiplicative a), Group (Additive a)) => Complex a -> Complex a -> Complex a
divComplex (a :+ b) (c :+ d) = (recip (c * c + d * d) *) <$> (a * c + b * d) :+ (b * c + negate (a * d))


-- For any ring we may define a dual ring which has the same underlying set and the same addition operation, but the opposite multiplication: 
-- Any left R-module M can then be seen to be a right module over Dual, and any right module over R can be considered a left module over Dual.
deriving via (F1 Additive (Dual (Additive a))) instance Semigroup (Additive a) => Semigroup (Additive (Dual a))
deriving via (F1 Additive (Dual (Additive a))) instance Monoid (Additive a) => Monoid (Additive (Dual a))
deriving via (F1 Multiplicative (Dual (Multiplicative a))) instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (Dual a))
deriving via (F1 Multiplicative (Dual (Multiplicative a))) instance Monoid (Multiplicative a) => Monoid (Multiplicative (Dual a))
instance Presemiring a => Presemiring (Dual a)
instance Semiring a => Semiring (Dual a)

deriving via (F2 Additive Down (Additive a)) instance Semigroup (Additive a) => Semigroup (Additive (Down a))
deriving via (F2 Additive Down (Additive a)) instance Monoid (Additive a) => Monoid (Additive (Down a))
deriving via (F2 Multiplicative Down (Multiplicative a)) instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (Down a))
deriving via (F2 Multiplicative Down (Multiplicative a)) instance Monoid (Multiplicative a) => Monoid (Multiplicative (Down a))
instance Presemiring a => Presemiring (Down a)
instance Semiring a => Semiring (Down a)

-- Min-Plus (Max-Plus) semiring
{-
λ> Min 3 + Min 4
Min {getMin = 3}
λ> Min 3 * Min 4
Min {getMin = 7}
λ> Min (Down 3) + Min (Down 4)
Min {getMin = Down 4}
λ> Min (Down 3) * Min (Down 4)
Min {getMin = Down 7}
-}
deriving via (F1 Additive (Min a)) instance P.Ord a => Semigroup (Additive (Min a))
deriving via (F1 Additive (Min a)) instance (P.Ord a, P.Bounded a) => Monoid (Additive (Min a))
deriving via (F2 Multiplicative Min (Additive a)) instance Semigroup (Additive a) => Semigroup (Multiplicative (Min a))
deriving via (F2 Multiplicative Min (Additive a)) instance Monoid (Additive a) => Monoid (Multiplicative (Min a))
instance (Ord a, Semigroup (Additive a)) => Presemiring (Min a)
instance (Ord a, Monoid (Additive a), P.Bounded a) => Semiring (Min a)

-- Max-Times (Min-Times) semiring
{-
λ> Max 3 + Max 4
Max {getMax = 4}
λ> Max 3 * Max 4
Max {getMax = 12}
λ> Max (Down 3) + Max (Down 4)
Max {getMax = Down 4}
λ> Max (Down 3) * Max (Down 4)
Max {getMax = Down 12}
-}
deriving via (F1 Additive (Max a)) instance P.Ord a => Semigroup (Additive (Max a))
deriving via (F1 Additive (Max a)) instance (P.Ord a, P.Bounded a) => Monoid (Additive (Max a))
deriving via (F2 Multiplicative Max (Multiplicative a)) instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (Max a))
deriving via (F2 Multiplicative Max (Multiplicative a)) instance Monoid (Multiplicative a) => Monoid (Multiplicative (Max a))
instance (Ord a, Semigroup (Multiplicative a)) => Presemiring (Max a)
instance (Ord a, Monoid (Multiplicative a), P.Bounded a) => Semiring (Max a)


--deriving via (F1 Additive ((f++g) (Additive a))) instance Semigroup (Additive a) => Semigroup (Additive ((f++g) a))
--deriving via (F1 Additive (Ap (f++g) (Additive a))) instance (Applicative f, Applicative g, Semigroup (Additive a)) => Semigroup (Additive ((f++g) a)) 

-- the component-wise multiplication semiring. use the semimodule instances and .#. for matrix mult.
--deriving via (F2 Additive (f**g) (Additive a)) instance (Applicative f, Applicative g, Semigroup (Additive a)) => Semigroup (Additive ((f**g) a)) 

deriving via (F1 Additive (a -> a)) instance Semigroup a => Semigroup (Additive (Endo a))
deriving via (F1 Additive (a -> a)) instance Monoid a => Monoid (Additive (Endo a))
deriving via (F1 Multiplicative (Endo a)) instance Semigroup a => Semigroup (Multiplicative (Endo a))
deriving via (F1 Multiplicative (Endo a)) instance Monoid a => Monoid (Multiplicative (Endo a))
instance Semigroup a => Presemiring (Endo a)
instance Monoid a => Semiring (Endo a)

deriving via (F1 Additive (r -> Additive a)) instance Semigroup (Additive a) => Semigroup (Additive (r -> a))
deriving via (F1 Additive (r -> Additive a)) instance Monoid (Additive a) => Monoid (Additive (r -> a))
deriving via (F1 Multiplicative (r -> Multiplicative a)) instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (r -> a))
deriving via (F1 Multiplicative (r -> Multiplicative a)) instance Monoid (Multiplicative a) => Monoid (Multiplicative (r -> a))
instance Presemiring a => Presemiring (r -> a)
instance Semiring a => Semiring (r -> a)

deriving via (b -> Additive a) instance Semigroup (Additive a) => Semigroup (Additive (Op a b))
deriving via (b -> Additive a) instance Monoid (Additive a) => Monoid (Additive (Op a b))
deriving via (b -> Multiplicative a) instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (Op a b))
deriving via (b -> Multiplicative a) instance Monoid (Multiplicative a) => Monoid (Multiplicative (Op a b))
instance Presemiring a => Presemiring (Op a b)
instance Semiring a => Semiring (Op a b)

deriving via (Op (Additive Bool) a) instance Semigroup (Additive (Predicate a))
deriving via (Op (Additive Bool) a) instance Monoid (Additive (Predicate a))
deriving via (Op (Multiplicative Bool) a) instance Semigroup (Multiplicative (Predicate a))
deriving via (Op (Multiplicative Bool) a) instance Monoid (Multiplicative (Predicate a))
instance Presemiring a => Presemiring (Predicate a)
instance Semiring a => Semiring (Predicate a)

deriving via (F1 Additive (Maybe (Additive a))) instance Semigroup (Additive a) => Semigroup (Additive (Maybe a))
deriving via (F1 Additive (Maybe (Additive a))) instance Monoid (Additive a) => Monoid (Additive (Maybe a))
deriving via (F2 Multiplicative Maybe (Multiplicative a)) instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (Maybe a))
deriving via (F2 Multiplicative Maybe (Multiplicative a)) instance Monoid (Multiplicative a) => Monoid (Multiplicative (Maybe a))
instance Presemiring a => Presemiring (Maybe a)
instance Semiring a => Semiring (Maybe a)

instance (Semigroup (Additive e), Semigroup (Additive a)) => Semigroup (Additive (Either e a)) where
  (<>) = liftA2 addEither

instance (Monoid (Additive e), Semigroup (Additive a)) => Monoid (Additive (Either e a)) where
  mempty = pure $ Left zero

instance (Semigroup (Multiplicative e), Semigroup (Multiplicative a)) => Semigroup (Multiplicative (Either e a)) where
  (<>) = liftA2 mulEither

instance (Semigroup (Multiplicative e), Monoid (Multiplicative a)) => Monoid (Multiplicative (Either e a)) where
  mempty = pure $ Right one

instance (Presemiring e, Presemiring a) => Presemiring (Either e a)
instance (Semiring e, Semiring a) => Semiring (Either e a)

addEither (Left _) (Right y) = Right y
addEither (Left x) (Left y) = Left $ x + y
addEither (Right x) (Left _) = Right x
addEither (Right x) (Right y) = Right $ x + y

mulEither (Left x) (Right _) = Left x
mulEither (Left x) (Left y) = Left $ x * y
mulEither (Right _) (Left y) = Left y
mulEither (Right x) (Right y) = Right $ x * y

instance Semigroup (Additive a) => Semigroup (Additive [a]) where
  (<>) = liftA2 addList

instance Semigroup (Additive a) => Monoid (Additive [a]) where
  mempty = pure []

instance SemiringLaw a => Semigroup (Multiplicative [a]) where
  (<>) = liftA2 mulList

instance SemiringLaw a => Monoid (Multiplicative [a]) where
  mempty = pure [one]

instance Semiring a => Presemiring [a]
instance Semiring a => Semiring [a]

addList :: (Additive-Semigroup) a => [a] -> [a] -> [a]
addList [] bs = bs
addList as [] = as
addList (a : as) (b : bs) = a + b : addList as bs

-- corresponds to discrete convolution / polynomial multiplication
-- >>> [1,2,3] * [1,0,0]
-- [1,2,3,0,0]
mulList :: SemiringLaw a => [a] -> [a] -> [a]
mulList [] _ = []
mulList (a : as) bs = fmap (a*) bs `addList` (zero : mulList as bs)

type Poly1 a = Map Natural a
type Poly2 a = Map (Natural, Natural) a

-- TODO props: reduce zero == const coeff, reduce one == sum of all coeffs
--reducePoly :: SemiringLaw a => a -> Map Int a -> a
--reducePoly x y = flip Map.foldMapWithKey y $ \k a -> (sumWith (P.replicate k) x) * a

instance (Ord k, Semigroup (Additive a)) => Semigroup (Additive (Map k a)) where
  (<>) = liftA2 $ Map.unionWith (+)

instance (Ord k, Semigroup (Additive a)) => Monoid (Additive (Map k a)) where
  --mempty = pure $ Map.singleton mempty zero
  mempty = pure $ Map.empty

mulMap :: (Ord k, Semigroup k, PresemiringLaw a) => Map k a -> Map k a -> Map k a
mulMap xs ys = foldl' (+) Map.empty [Map.singleton (u <> v) (xs Map.! u * ys Map.! v) | u <- Map.keys xs, v <- Map.keys ys]

instance (Ord k, Semigroup k, PresemiringLaw a) => Semigroup (Multiplicative (Map k a)) where
  --(<>) = liftA2 $ Map.unionWith (+)
  --Mul xs <> Mul ys = Mul $ Map.fromListWith (+) 
  --   [ (k <> l, v * u) | (k, v) <- Map.toList xs, (l, u) <- Map.toList ys ]

  -- TODO: improve fold
  (<>) = liftA2 mulMap

instance (Ord k, Monoid k, SemiringLaw a) => Monoid (Multiplicative (Map k a)) where
  --mempty = pure $ Map.singleton mempty zero
  --mempty = pure $ Map.empty
  mempty = Mul $ Map.singleton mempty one


instance (Semigroup (Additive a), Semigroup (Additive b)) => Semigroup (Additive (a, b)) where
  (<>) = liftA2 $ \(x1,x2) (y1,y2) -> (x1+y1,x2+y2)

instance (Monoid (Additive a), Monoid (Additive b)) => Monoid (Additive (a, b)) where
  mempty = pure (zero, zero)

instance (Semigroup (Multiplicative a), Semigroup (Multiplicative b)) => Semigroup (Multiplicative (a, b)) where
  (<>) = liftA2 $ \(x1,x2) (y1,y2) -> (x1*y1,x2*y2)

instance (Monoid (Multiplicative a), Monoid (Multiplicative b)) => Monoid (Multiplicative (a, b)) where
  mempty = pure (one, one)

instance (Presemiring a, Presemiring b) => Presemiring (a, b)
instance (Semiring a, Semiring b) => Semiring (a, b)

instance (Semigroup (Additive a), Semigroup (Additive b), Semigroup (Additive c)) => Semigroup (Additive (a, b, c)) where
  (<>) = liftA2 $ \(x1,x2,x3) (y1,y2,y3) -> (x1+y1,x2+y2,x3+y3)

instance (Monoid (Additive a), Monoid (Additive b), Monoid (Additive c)) => Monoid (Additive (a, b, c)) where
  mempty = pure (zero, zero, zero)

instance (Semigroup (Multiplicative a), Semigroup (Multiplicative b), Semigroup (Multiplicative c)) => Semigroup (Multiplicative (a, b, c)) where
  (<>) = liftA2 $ \(x1,x2,x3) (y1,y2,y3) -> (x1*y1,x2*y2,x3*y3)

instance (Monoid (Multiplicative a), Monoid (Multiplicative b), Monoid (Multiplicative c)) => Monoid (Multiplicative (a, b, c)) where
  mempty = pure (one, one, one)

instance (Presemiring a, Presemiring b, Presemiring c) => Presemiring (a, b, c)
instance (Semiring a, Semiring b, Semiring c) => Semiring (a, b, c)


{-
--deriving via (A1 Maybe a) instance PresemiringLaw a => PresemiringLaw (Maybe a) 

deriving via (Ap (f**g) a) instance (Applicative f, Applicative g, PresemiringLaw a) => PresemiringLaw ((f**g) a) 
deriving via (Ap (f**g) a) instance (Applicative f, Applicative g, SemiringLaw a) => SemiringLaw ((f**g) a) 

deriving via (Ap (f++g) a) instance (Applicative f, Applicative g, PresemiringLaw a) => PresemiringLaw ((f++g) a) 
-- the component-wise multiplication semiring. use the semimodule instances and .#. for matrix mult.
deriving via (Ap (f++g) a) instance (Applicative f, Applicative g, SemiringLaw a) => SemiringLaw ((f++g) a) 


deriving via (Ap ((->)a) b) instance PresemiringLaw b => PresemiringLaw (a -> b)

--deriving via (A1 [] a) instance PresemiringLaw a => PresemiringLaw [a] 
deriving via (A1 Seq a) instance PresemiringLaw a => PresemiringLaw (Seq a) 

deriving via (A1 (Either e) a) instance PresemiringLaw a => PresemiringLaw (Either e a)

deriving via (A1 NonEmpty a) instance PresemiringLaw a => PresemiringLaw (NonEmpty a) 
--deriving via (A1 (Map k) a) instance (Ord k, PresemiringLaw a) => PresemiringLaw (Map k a) 
deriving via (A1 IntMap a) instance PresemiringLaw a => PresemiringLaw (IntMap a) 
--deriving via (A1 (Lift f) a) instance (Alt f, Semigroup a) => PresemiringLaw (Lift f a) 



instance Ord a => PresemiringLaw (Set a) where
  (+) = Set.union
  (*) = Set.intersection



instance PresemiringLaw (Equivalence a) where
  Equivalence f + Equivalence g = Equivalence $ \x y -> f x y + g x y
  {-# INLINE (+) #-}
  Equivalence f * Equivalence g = Equivalence $ \x y -> f x y * g x y
  {-# INLINE (*) #-}

instance SemiringLaw (Equivalence a) where
  zero = Equivalence $ \_ _ -> zero
  one = Equivalence $ \_ _ -> one



instance (Alt f, Apply f, PresemiringLaw a) => PresemiringLaw (A1 f a) where
  A1 x * A1 y = A1 $ liftF2 (*) x y
  A1 x + A1 y = A1 $ x <!> y

instance (Applicative f, PresemiringLaw a) => PresemiringLaw (Ap f a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)

-------------------------------------------------------------------------------
-- SemifieldLaws
-------------------------------------------------------------------------------

infixl 7 /

-- | A semifield, near-field, or division ring.
--
-- Instances needn't have commutative multiplication or additive inverses,
-- however addition must be commutative, and addition and multiplication must 
-- be associative as usual.
--
-- See also the wikipedia definitions of:
--
-- * < https://en.wikipedia.org/wiki/SemifieldLaw semifield >
-- * < https://en.wikipedia.org/wiki/Near-field_(mathematics) near-field >
-- * < https://en.wikipedia.org/wiki/Division_ring division ring >
-- 
class SemiringLaw a => SemifieldLaw a where

  -- | Reciprocal of a multiplicative group element.
  --
  -- @ 
  -- x '/' y = x '*' 'recip' y
  -- @
  --
  -- >>> recip (3 :+ 4) :: Complex Rational
  -- 3 % 25 :+ (-4) % 25
  -- >>> recip (3 :+ 4) :: Complex Double
  -- 0.12 :+ (-0.16)
  -- >>> recip (3 :+ 4) :: Complex Pico
  -- 0.120000000000 :+ -0.160000000000
  -- 
  recip :: a -> a 
  recip x = one / x
  {-# INLINE recip #-}

  -- | Right division by a multiplicative group element.
  --
  (/) :: a -> a -> a
  (/) x y = x * recip y
  {-# INLINE (/) #-}

  infixr 8 ^^

  -- | Integral power of a multiplicative group element.
  --
  -- @ 'one' '==' a '^^' 0 @
  --
  -- >>> 8 ^^ 0 :: Double
  -- 1.0
  -- >>> 8 ^^ 0 :: Pico
  -- 1.000000000000
  --
  (^^) :: a -> Integer -> a
  a ^^ n 
    | n == 0 = one
    | n > 0 = a ^ P.fromIntegral n
    | otherwise = recip a ^ P.fromIntegral (P.negate n)

  -- | A /NaN/ value of the semifield.
  --
  -- @ 'anan' = 'zero' '/' 'zero' @
  --
  anan :: a
  anan = zero / zero
  {-# INLINE anan #-}

  -- | The positive infinity of the semifield.
  --
  -- @ 'pinf' = 'one' '/' 'zero' @
  --
  pinf :: a
  pinf = one / zero
  {-# INLINE pinf #-}




type Arr b = [[b]]

ident :: Arr Double
ident = [[1]]

--boxBlur :: Int -> Arr Double
--boxBlur n = (fmap.fmap) (/ fromIntegral (n*n)) ((replicate n . replicate n) 1)

sharpen :: Arr Double
sharpen = [[ 0,-1, 0]
          ,[-1, 5,-1]
          ,[ 0,-1, 0]]

edgy :: Arr Double
edgy = [[-1,-1,-1]
       ,[-1, 8,-1]
       ,[-1,-1,-1]]


-}
