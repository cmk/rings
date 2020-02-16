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

module Data.Semiring (
  -- * Types
    type (-)
  -- * Presemirings
  , type PresemiringLaw, Presemiring
  , (+), (*)
  , sum1, sumWith1
  , product1, productWith1
  , xmult1
  , eval1, evalWith1
  -- * Semirings
  , type SemiringLaw, Semiring
  , zero, one, two
  , (^)
  , sum, sumWith
  , product, productWith
  , xmult   
  , eval, evalWith
  -- * Rings
  , type RingLaw, Ring
  , (-)
  , negate, abs, signum
  -- * Re-exports
  , mreplicate
  , Additive(..)
  , Multiplicative(..)
  , Magma(..)
  , Quasigroup
  , Loop
  , Group(..)
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Either
import safe Data.Fixed
import safe Data.Foldable as Foldable (Foldable, foldr')
import safe Data.Functor.Apply
import safe Data.Group
import safe Data.Int
import safe Data.List.NonEmpty
import safe Data.Maybe
import safe Data.Semigroup.Additive as A
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Semigroup.Multiplicative as M
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Real hiding (Fractional(..), (^^), (^))
import safe Numeric.Natural
import safe Prelude (Ord(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), id, (.), ($), Integer, Float, Double)
import safe qualified Prelude as P
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set

-------------------------------------------------------------------------------
-- Presemiring
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
-- Note that addition and multiplication needn't be commutative.
--
-- See the properties module for a detailed specification of the laws.
--
type PresemiringLaw a = ((Additive-Semigroup) a, (Multiplicative-Semigroup) a)

class PresemiringLaw a => Presemiring a

-- | Evaluate a non-empty presemiring sum.
--
sum1 :: Presemiring a => Foldable1 f => f a -> a
sum1 = sumWith1 id

-- | Evaluate a non-empty presemiring sum using a given presemiring.
-- 
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

-- | Evaluate a non-empty presemiring product.
--
product1 :: Presemiring a => Foldable1 f => f a -> a
product1 = productWith1 id

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
productWith1 :: Foldable1 t => Presemiring a => (b -> a) -> t b -> a
productWith1 f = unMultiplicative . foldMap1 (Multiplicative . f)
{-# INLINE productWith1 #-}

-- | Cross-multiply two non-empty collections.
--
-- >>> xmult1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
--
xmult1 :: Foldable1 f => Apply f => Presemiring a => f a -> f a -> a
xmult1 a b = sum1 $ liftF2 (*) a b
{-# INLINE xmult1 #-}

-- | Evaluate a presemiring expression.
-- 
eval1 :: Presemiring a => Functor f => Foldable1 f => Foldable1 g => f (g a) -> a
eval1 = sum1 . fmap product1

-- | Evaluate a presemiring expression using a given presemiring.
-- 
-- >>>  evalWith1 (Max . Down) $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = Down 9}
-- >>>  evalWith1 Max $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = 15}
-- 
evalWith1 :: Presemiring r => Functor f => Functor g => Foldable1 f => Foldable1 g => (a -> r) -> f (g a) -> r
evalWith1 f = sum1 . fmap product1 . (fmap . fmap) f

-------------------------------------------------------------------------------
-- Semiring
-------------------------------------------------------------------------------

type SemiringLaw a = ((Additive-Monoid) a, (Multiplicative-Monoid) a)

-- | Right semirings.
-- 
-- A right semiring is a pre-semiring with two distinct neutral elements, 'zero' 
-- and 'one', such that 'zero' is right-neutral wrt addition, 'one' is right-neutral wrt
-- multiplication, and 'zero' is right-annihilative wrt multiplication. 
--
-- /Neutrality/
--
-- @
-- 'zero' '+' r = r
-- 'one' '*' r = r
-- @
--
-- /Absorbtion/
--
-- @
-- 'zero' '*' a = 'zero'
-- @
--
class (Presemiring a, SemiringLaw a) => Semiring a

-- |
--
-- @
-- 'two' = 'one' '+' 'one'
-- @
--
two :: Semiring a => a
two = one + one
{-# INLINE two #-}

infixr 8 ^

-- | Evaluate a natural-numbered power of a semiring element.
--
-- @ 'one' = a '^' 0 @
--
-- >>> 8 ^ 0 :: Int
-- 1
--
(^) :: Semiring a => a -> Natural -> a
a ^ n = unMultiplicative $ mreplicate (P.fromIntegral n) (Multiplicative a)

-- | Evaluate a semiring sum.
-- 
-- >>> sum [1..5 :: Int]
-- 15
--
sum :: (Additive-Monoid) a => Presemiring a => Foldable f => f a -> a
sum = sumWith id

-- | Evaluate a semiring sum using a given semiring.
-- 
sumWith :: (Additive-Monoid) a => Presemiring a => Foldable t => (b -> a) -> t b -> a
sumWith f = foldr' ((+) . f) zero
{-# INLINE sumWith #-}

-- | Evaluate a semiring product.
--
-- >>> product [1..5 :: Int]
-- 120
--
product :: (Multiplicative-Monoid) a => Presemiring a => Foldable f => f a -> a
product = productWith id

-- | Evaluate a semiring product using a given semiring.
--
-- @
-- 'product' f = 'Data.foldr'' (('*') . f) 'one'
-- @
--
-- >>> productWith Just [1..5 :: Int]
-- Just 120
--
productWith :: (Multiplicative-Monoid) a => Presemiring a => Foldable t => (b -> a) -> t b -> a
productWith f = foldr' ((*) . f) one
{-# INLINE productWith #-}

-- | Cross-multiply two collections.
--
-- >>> xmult (V3 1 2 3) (V3 1 2 3)
-- 14
-- >>> xmult [1,2,3 :: Int] [1,2,3]
-- 36
-- >>> xmult [1,2,3 :: Int] []
-- 0
--
xmult :: Foldable f => Applicative f => Presemiring a => (Additive-Monoid) a => f a -> f a -> a
xmult a b = sum $ liftA2 (*) a b
{-# INLINE xmult #-}

-- | Evaluate a semiring expression.
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

-- | Evaluate a semiring expression using a given semiring.
-- 
-- >>> evalWith Max [[1..4 :: Int], [0..2 :: Int]]
-- Max {getMax = 24}
--
evalWith :: Semiring r => Functor f => Functor g => Foldable f => Foldable g => (a -> r) -> f (g a) -> r
evalWith f = sum . fmap product . (fmap . fmap) f

-------------------------------------------------------------------------------
-- Ring
-------------------------------------------------------------------------------

type RingLaw a = ((Additive-Group) a, (Multiplicative-Monoid) a)

-- | Rings.
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

-- satisfies trichotomy law:
-- Exactly one of the following is true: a is positive, -a is positive, or a = 0.
-- This property follows from the fact that ordered rings are abelian, linearly ordered groups with respect to addition.
signum :: Ring a => Ord a => a -> a
signum x = bool (negate one) one $ zero <= x
{-# INLINE signum #-}

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
instance Presemiring (Ratio Natural)

instance Presemiring Int
instance Presemiring Int8
instance Presemiring Int16
instance Presemiring Int32
instance Presemiring Int64
instance Presemiring Integer
instance Presemiring (Ratio Integer)

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


instance Ring a => Presemiring (Complex a)
instance Presemiring a => Presemiring (r -> a)
instance (Presemiring a, Presemiring b) => Presemiring (Either a b)
instance Presemiring a => Presemiring (Maybe a)
instance (Additive-Semigroup) a => Presemiring [a]
instance (Additive-Semigroup) a => Presemiring (NonEmpty a)


instance Semiring ()
instance Semiring Bool
instance Semiring Word
instance Semiring Word8
instance Semiring Word16
instance Semiring Word32
instance Semiring Word64
instance Semiring Natural
instance Semiring (Ratio Natural)

instance Semiring Int
instance Semiring Int8
instance Semiring Int16
instance Semiring Int32
instance Semiring Int64
instance Semiring Integer
instance Semiring (Ratio Integer)

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

instance Ring a => Semiring (Complex a)
instance Semiring a => Semiring (r -> a)
instance Semiring a => Semiring (Maybe a)
instance (Additive-Monoid) a => Semiring [a]

instance Presemiring IntSet.IntSet
instance Ord a => Presemiring (Set.Set a)
instance Presemiring a => Presemiring (IntMap.IntMap a)
instance (Ord k, Presemiring a) => Presemiring (Map.Map k a)
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
instance Ring (Ratio Integer)

instance Ring Uni
instance Ring Deci
instance Ring Centi
instance Ring Milli
instance Ring Micro
instance Ring Nano
instance Ring Pico

-- Unlawful instances
instance Ring Float
instance Ring Double
instance Ring CFloat
instance Ring CDouble

instance Ring a => Ring (Complex a)
