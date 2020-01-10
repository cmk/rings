{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MonoLocalBinds             #-}

module Data.Semiring where

import safe Control.Applicative
import safe Control.Category ((>>>))
import safe Data.Bool
import safe Data.Ord
import safe Data.Complex
import safe Data.Maybe
import safe Data.Either
import safe Data.Fixed
import safe Data.Foldable as Foldable (Foldable, fold, foldr', foldl')
import safe Data.Group
import safe Data.Int
import safe Data.List.NonEmpty
import safe Data.Magma
import safe Data.Semigroup
import safe Data.Semigroup.Foldable as Foldable1

import safe Data.Semigroup.Additive as A
import safe Data.Semigroup.Multiplicative as M

import safe Data.Functor.Apply
import safe Data.Tuple
import safe Data.Word
import safe GHC.Real hiding (Fractional(..), (^^), (^))
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))

import safe Prelude ( Eq(..), Ord(..), Show, Ordering(..), Bounded(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), id, (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import GHC.Generics (Generic)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as Seq



type Nonnegative = Ratio Natural

--Tropical semirings
type MinPlus a = Min a
type MaxPlus a = Min (Down a)
type MinTimes a = Max (Down a)
type MaxTimes a = Max a

-- | Right pre-semirings and (non-unital and unital) right semirings.
-- 
-- A right pre-semiring (sometimes referred to as a bisemigroup) is a type /R/ endowed 
-- with two associative binary (i.e. semigroup) operations: (<>) and (*), along with a 
-- right-distributivity property connecting them:
--
-- @
-- (a '+' b) '*' c '==' (a '*' c) '+' (b '*' c)
-- @
--
-- A non-unital right semiring (sometimes referred to as a bimonoid) is a pre-semiring 
-- with a 'mempty' element that is neutral with respect to both addition and multiplication.
--
-- A unital right semiring is a pre-semiring with two distinct neutral elements, 'mempty' 
-- and 'one', such that 'mempty' is right-neutral wrt addition, 'one' is right-neutral wrt
--  multiplication, and 'mempty' is right-annihilative wrt multiplication. 
--
-- Note that 'one' needn't be distinct from 'mempty', moreover addition and multiplication
-- needn't be commutative or left-distributive.
--
-- See the properties module for a detailed specification of the laws.
--
type PresemiringLaw a = ((Additive-Semigroup) a, (Multiplicative-Semigroup) a)

type SemiringLaw a = ((Additive-Monoid) a, (Multiplicative-Monoid) a)

type RingLaw a = ((Additive-Group) a, (Multiplicative-Monoid) a)



--type MaxTimes a = ((Max-Monoid) a, (Multiplicative-Semigroup) a)

--type MinTimes a = ((Min-Monoid) a, (Multiplicative-Semigroup) a)

class PresemiringLaw a => Presemiring a

infixl 6 +
infixl 7 *

--class Presemiring a => Semiring a where
-- >>> Dual [2] + Dual [3] :: Dual [Int]
-- Dual {getDual = [3,2]}
(+) :: Presemiring a => a -> a -> a
(+) = A.add 

-- >>> Dual [2] * Dual [3] :: Dual [Int]
-- Dual {getDual = [5]}
(*) :: Presemiring a => a -> a -> a
(*) = M.mul

class (Presemiring a, SemiringLaw a) => Semiring a

-- | Cross-multiply two collections.
--
-- >>> cross [1,2,3 :: Int] [1,2,3]
-- 36
--
-- >>> cross [1,2,3 :: Int] []
-- 0
--
cross :: Foldable f => Applicative f => Presemiring a => (Additive-Monoid) a => f a -> f a -> a
cross a b = sum $ liftA2 (*) a b
{-# INLINE cross #-}

-- | Cross-multiply two non-empty collections.
--
-- >>> cross1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
--
cross1 :: Foldable1 f => Apply f => Presemiring a => f a -> f a -> a
cross1 a b = sum1 $ liftF2 (*) a b
{-# INLINE cross1 #-}



infixr 8 ^

-- @ 'one' == a '^' 0 @
--
-- >>> 8 ^ 0 :: Int
-- 1
--
(^) :: Semiring a => a -> Natural -> a
a ^ n = unMultiplicative $ mreplicate (P.fromIntegral n) (Multiplicative a)

-- | Evaluate a right-associated semiring expression.
-- 
-- @ (a11 * .. * a1m) + (a21 * .. * a2n) + ... @
--
-- >>> eval [[1, 2], [3, 4 :: Int]] -- 1 * 2 + 3 * 4
-- 14
-- >>> eval $ sequence [[1, 2], [3, 4 :: Int]] -- 1 + 2 * 3 + 4
-- 21
--
eval :: Semiring a => Functor f => Foldable f => Foldable g => f (g a) -> a
eval = sum . fmap product


-- >>> evalWith Max [[1..4 :: Int], [0..2 :: Int]]
-- Max {getMax = 24}
evalWith :: Semiring r => Functor f => Functor g => Foldable f => Foldable g => (a -> r) -> f (g a) -> r
evalWith f = sum . fmap product . (fmap . fmap) f

eval1 :: Presemiring a => Functor f => Foldable1 f => Foldable1 g => f (g a) -> a
eval1 = sum1 . fmap product1

-- >>>  evalWith1 (Max . Down) $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = Down 9}
-- >>>  evalWith1 Max $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = 15}
-- 
evalWith1 :: Presemiring r => Functor f => Functor g => Foldable1 f => Foldable1 g => (a -> r) -> f (g a) -> r
evalWith1 f = sum1 . fmap product1 . (fmap . fmap) f

-- >>> sum [1..5 :: Int]
-- 15
sum :: (Additive-Monoid) a => Presemiring a => Foldable f => f a -> a
sum = sumWith id

sum1 :: Presemiring a => Foldable1 f => f a -> a
sum1 = sumWith1 id

sumWith :: (Additive-Monoid) a => Presemiring a => Foldable t => (b -> a) -> t b -> a
sumWith f = foldr' ((+) . f) zero
{-# INLINE sumWith #-}

-- >>> evalWith1 Max $ (1 :| [2..5 :: Int]) :| [1 :| [2..5 :: Int]]
-- | Fold over a non-empty collection using the additive operation of an arbitrary semiring.
--
-- >>> sumWith1 First $ (1 :| [2..5 :: Int]) * (1 :| [2..5 :: Int])
-- First {getFirst = 1}
-- >>> sumWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
-- >>> sumWith1 Just $ 1 :| [2..5 :: Int]
-- Just 15
--
sumWith1 :: Foldable1 t => Presemiring a => (b -> a) -> t b -> a
sumWith1 f = unAdditive . foldMap1 (Additive . f)
{-# INLINE sumWith1 #-}

-- >>> product [1..5 :: Int]
-- 120
product :: (Multiplicative-Monoid) a => Presemiring a => Foldable f => f a -> a
product = productWith id

--
-- | The product of at a list of semiring elements (of length at least one)
product1 :: Presemiring a => Foldable1 f => f a -> a
product1 = productWith1 id

-- | Fold over a collection using the multiplicative operation of an arbitrary semiring.
-- 
-- @
-- 'product' f ≡ 'Data.foldr'' ((*) . f) 'one'
-- @
--
--
-- >>> productWith Just [1..5 :: Int]
-- Just 120
--
productWith :: (Multiplicative-Monoid) a => Presemiring a => Foldable t => (b -> a) -> t b -> a
productWith f = foldr' ((*) . f) one
{-# INLINE productWith #-}


-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
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
productWith1 :: Foldable1 t => Presemiring a => (b -> a) -> t b -> a
productWith1 f = unMultiplicative . foldMap1 (Multiplicative . f)
{-# INLINE productWith1 #-}


infixl 6 -

-- | Rings.
--
-- A ring /R/ is a commutative group with a second monoidal operation '*' that distributes over '+'.
--
-- The basic properties of a ring follow immediately from the axioms:
-- 
-- @ r '*' 'zero' '==' 'zero' '==' 'zero' '*' r @
--
-- @ 'negate' 'one' '*' r '==' 'negate' r @
--
-- Furthermore, the binomial formula holds for any commuting pair of elements (that is, any /a/ and /b/ such that /a * b = b * a/).
--
-- If /mempty = one/ in a ring /R/, then /R/ has only one element, and is called the zero ring.
-- Otherwise the additive identity, the additive inverse of each element, and the multiplicative identity are unique.
--
-- See < https://en.wikipedia.org/wiki/Ring_(mathematics) >.
--
-- If the ring is < https://en.wikipedia.org/wiki/Ordered_ring ordered > (i.e. has an 'Ord' instance), then the following additional properties must hold:
--
-- @ a '<=' b '==>' a '+' c '<=' b '+' c @
--
-- @ 'zero' '<=' a '&&' 'zero' '<=' b '==>' 'zero' '<=' a '*' b @
--
-- See the properties module for a detailed specification of the laws.
--
class (Semiring a, RingLaw a) => Ring a where

(-) :: Ring a => a -> a -> a
(-) = A.sub

negate :: (Additive-Group) a => a -> a
negate a = zero `sub` a
{-# INLINE negate #-}

two :: (Additive-Semigroup) a => (Multiplicative-Monoid) a => a
two = one `add` one
{-# INLINE two #-}

-- | Absolute value of an element.
--
-- @ abs r ≡ r  `mul`  signum r @
--
-- https://en.wikipedia.org/wiki/Linearly_ordered_group
abs :: (Additive-Group) a => Ord a => a -> a
abs x = bool (negate x) x $ zero <= x
{-# INLINE abs #-}

-- satisfies trichotomy law:
-- Exactly one of the following is true: a is positive, -a is positive, or a = 0.
-- This property follows from the fact that ordered rings are abelian, linearly ordered groups with respect to addition.
signum :: RingLaw a => Ord a => a -> a
signum x = bool (negate one) one $ zero <= x
{-# INLINE signum #-}




{-
-- | Default implementation of 'fromBoolean' given a multiplicative unit.
--
fromBooleanDef :: Unital a => a -> Bool -> a
fromBooleanDef _ False = mempty
fromBooleanDef o True = o
{-# INLINE fromBooleanDef #-}

-- | Multiplicative unit.
--
-- Note that 'one' needn't be distinct from 'mempty' for a semiring to be valid.
--
one :: Unital a => a
one = fromBoolean True
{-# INLINE one #-}


infixr 8 ^

(^) :: Unital a => a -> Natural -> a
(^) = flip sinnum'
{-# INLINE (^) #-}

-- | A generalization of 'Data.List.replicate' to an arbitrary 'Monoid'. 
--
-- Adapted from <http://augustss.blogspot.com/2008/07/lost-and-found-if-i-write-108-in.html>.
--
sinnum :: Monoid a => Natural -> a -> a
sinnum n a
    | n == 0 = mempty
    | otherwise = f a n
    where
        f x y 
            | even y = f (x <> x) (y `quot` 2)
            | y == 1 = x
            | otherwise = g (x <> x) ((y N.- 1) `quot` 2) x
        g x y z 
            | even y = g (x <> x) (y `quot` 2) z
            | y == 1 = x <> z
            | otherwise = g (x <> x) ((y N.- 1) `quot` 2) (x <> z)
{-# INLINE sinnum #-}

sinnum' :: Unital a => Natural -> a -> a
sinnum' n a = getProd $ sinnum n (Prod a)
{-# INLINE sinnum' #-}

powers :: Unital a => Natural -> a -> a
powers n a = foldr' (<>) one . flip unfoldr n $ \m -> 
  if m == 0 then Nothing else Just (a^m,m N.- 1)
{-# INLINE powers #-}

-------------------------------------------------------------------------------
-- Pre-semirings
-------------------------------------------------------------------------------

instance Semigroup a => Semiring (Either e a) where
  (*) = liftA2 (<>)
  {-# INLINE (*) #-}


instance Semiring Ordering where
  LT * LT = LT
  LT * GT = LT
  _  * EQ = EQ
  EQ * _  = EQ
  GT * x  = x

  fromBoolean = fromBooleanDef GT



  fromBoolean = const . fromBoolean

instance Unital a => Semiring (Op a b) where
  Op f * Op g = Op $ \x -> f x * g x
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Op (const one)

instance (Unital a, Unital b) => Semiring (a, b) where
  (a, b) * (c, d) = (a*c, b*d)
  {-# INLINE (*) #-}

  fromBoolean = liftA2 (,) fromBoolean fromBoolean

instance (Unital a, Unital b, Unital c) => Semiring (a, b, c) where
  (a, b, c) * (d, e, f) = (a*d, b*e, c*f)
  {-# INLINE (*) #-}

  fromBoolean = liftA3 (,,) fromBoolean fromBoolean fromBoolean




{-
---------------------------------------------------------------------
--  Instances (contravariant)
---------------------------------------------------------------------

-- Note that due to the underlying 'Monoid' instance this instance
-- has 'All' semiring semantics rather than 'Any'.
instance Semiring (Predicate a) where
  Predicate f * Predicate g = Predicate $ \x -> f x || g x
  {-# INLINE (*) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean False = Predicate $ const True
  fromBoolean True = Predicate $ const False


-- Note that due to the underlying 'Monoid' instance this instance
-- has 'All' semiring semantics rather than 'Any'.
instance Semiring (Equivalence a) where
  Equivalence f * Equivalence g = Equivalence $ \x y -> f x y || g x y
  {-# INLINE (*) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean False = Equivalence $ \_ _ -> True
  fromBoolean True = Equivalence $ \_ _ -> False
-}

---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------

instance Ord a => Semiring (Set.Set a) where
  (*) = Set.intersection

instance Monoid a => Semiring (Seq.Seq a) where
  (*) = liftA2 (<>)
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Seq.singleton mempty

instance (Ord k, Monoid k, Monoid a) => Semiring (Map.Map k a) where
  xs * ys = foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Map.singleton mempty mempty

instance Monoid a => Semiring (IntMap.IntMap a) where
  xs * ys = foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ IntMap.singleton 0 mempty

-}

---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

-- Semirings
instance Presemiring ()
instance Presemiring Bool
instance Presemiring Word
instance Presemiring Word8
instance Presemiring Word16
instance Presemiring Word32
instance Presemiring Word64
instance Presemiring Natural
instance Presemiring Nonnegative

instance Presemiring Int
instance Presemiring Int8
instance Presemiring Int16
instance Presemiring Int32
instance Presemiring Int64
instance Presemiring Integer
instance Presemiring Rational

instance Presemiring Uni
instance Presemiring Deci
instance Presemiring Centi
instance Presemiring Milli
instance Presemiring Micro
instance Presemiring Nano
instance Presemiring Pico

instance Presemiring Float
instance Presemiring Double
instance Presemiring CFloat
instance Presemiring CDouble

-- Selective Predioids


instance (Additive-Semigroup) a => Presemiring [a]
instance (Additive-Semigroup) a => Presemiring (NonEmpty a)
instance Presemiring a => Presemiring (Dual a)
instance Presemiring a => Presemiring (r -> a)
instance (Presemiring a, Presemiring b) => Presemiring (Either a b)
instance Presemiring a => Presemiring (Maybe a)
instance Presemiring a => Presemiring (IntMap.IntMap a)
instance Presemiring IntSet.IntSet
instance (Ord a, Presemiring a) => Presemiring (Set.Set a)
instance (Ord k, Presemiring a) => Presemiring (Map.Map k a)


instance Semiring ()
instance Semiring Bool
instance Semiring Word
instance Semiring Word8
instance Semiring Word16
instance Semiring Word32
instance Semiring Word64
instance Semiring Natural
instance Semiring Nonnegative

instance Semiring Int
instance Semiring Int8
instance Semiring Int16
instance Semiring Int32
instance Semiring Int64
instance Semiring Integer
instance Semiring Rational

instance Semiring Uni
instance Semiring Deci
instance Semiring Centi
instance Semiring Milli
instance Semiring Micro
instance Semiring Nano
instance Semiring Pico

instance Semiring Float
instance Semiring Double
instance Semiring CFloat
instance Semiring CDouble

instance Semiring a => Semiring (Dual a)
instance Semiring a => Semiring (r -> a)
instance (Additive-Monoid) a => Semiring [a]
instance Semiring a => Semiring (Maybe a)
instance Semiring a => Semiring (IntMap.IntMap a)
instance (Ord k, (Multiplicative-Monoid) k, Semiring a) => Semiring (Map.Map k a)

-- Rings
instance Ring ()
instance Ring Int
instance Ring Int8
instance Ring Int16
instance Ring Int32
instance Ring Int64
instance Ring Integer
instance Ring Rational

instance Ring Uni
instance Ring Deci
instance Ring Centi
instance Ring Milli
instance Ring Micro
instance Ring Nano
instance Ring Pico

instance Ring Float
instance Ring Double
