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
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Data.Semiring (
  -- * Types
    type (-)
  , type (**) 
  , type (++) 
  , type Free
  -- * Presemirings
  , type PresemiringLaw, Presemiring
  , (+), (*)
  -- * Presemiring folds
  , sum1, sumWith1
  , product1, productWith1
  , xmult1
  , eval1, evalWith1
  -- * Semirings
  , type SemiringLaw, Semiring
  , zero, one, two
  , (^)
  -- * Semiring folds
  , sum, sumWith
  , product, productWith
  , xmult   
  , eval, evalWith
  -- * Rings
  , type RingLaw, Ring
  , (-)
  , subtract, negate, abs, signum
  -- * Additive
  , Additive(..)
  -- * Multiplicative
  , Multiplicative(..)
  -- * Re-exports
  , mreplicate
  , Magma(..)
  , Quasigroup
  , Loop
  , Group(..)
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Distributive
import safe Data.Either
import safe Data.Fixed
import safe Data.Foldable as Foldable (Foldable, foldr')
import safe Data.Functor.Apply
import safe Data.Functor.Rep
import safe Data.Functor.Compose
import safe Data.Functor.Product
import safe Data.Functor.Contravariant
import safe Data.Group
import safe Data.Int
import safe Data.List.NonEmpty
import safe Data.Maybe
import safe Data.Semigroup hiding (Product)
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Ord (Down(..))
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..), (^^), (^))
import safe Numeric.Natural
import safe Prelude (Eq, Ord(..), Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), id, flip, const, (.), ($), Integer, Float, Double)
import safe qualified Prelude as P
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set

-- | Hyphenation operator.
type (g - f) a = f (g a)

infixr 2 **

-- | Tensor product.
--
type (f ** g) = Compose f g

infixr 1 ++

-- | Direct sum.
--
type (f ++ g) = Product f g

type Free = Representable

-------------------------------------------------------------------------------
-- Presemiring
-------------------------------------------------------------------------------

type PresemiringLaw a = ((Additive-Semigroup) a, (Multiplicative-Semigroup) a)

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
class PresemiringLaw a => Presemiring a


infixl 6 +

-- | Additive semigroup operation on a semiring.
--
-- >>> Dual [2] + Dual [3] :: Dual [Int]
-- Dual {getDual = [3,2]}
--
(+) :: (Additive-Semigroup) a => a -> a -> a
a + b = unAdditive (Additive a <> Additive b)
{-# INLINE (+) #-}


infixl 7 *

-- | Multiplicative semigroup operation on a semiring.
--
-- >>> Dual [2] * Dual [3] :: Dual [Int]
-- Dual {getDual = [5]}
--
(*) :: (Multiplicative-Semigroup) a => a -> a -> a
a * b = unMultiplicative (Multiplicative a <> Multiplicative b)
{-# INLINE (*) #-}

-------------------------------------------------------------------------------
-- Presemiring folds
-------------------------------------------------------------------------------

-- | Evaluate a non-empty presemiring sum.
--
sum1 :: (Additive-Semigroup) a => Foldable1 f => f a -> a
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
sumWith1 :: (Additive-Semigroup) a => Foldable1 t => (b -> a) -> t b -> a
sumWith1 f = unAdditive . foldMap1 (Additive . f)
{-# INLINE sumWith1 #-}

-- | Evaluate a non-empty presemiring product.
--
product1 :: (Multiplicative-Semigroup) a => Foldable1 f => f a -> a
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
productWith1 :: (Multiplicative-Semigroup) a => Foldable1 t => (b -> a) -> t b -> a
productWith1 f = unMultiplicative . foldMap1 (Multiplicative . f)
{-# INLINE productWith1 #-}

-- | Cross-multiply two non-empty collections.
--
-- >>> xmult1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
--
xmult1 :: Presemiring a => Foldable1 f => Apply f => f a -> f a -> a
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

-- | Additive unit of a semiring.
--
zero :: (Additive-Monoid) a => a
zero = unAdditive mempty
{-# INLINE zero #-}

-- | Multiplicative unit of a semiring.
--
one :: (Multiplicative-Monoid) a => a
one = unMultiplicative mempty
{-# INLINE one #-}

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

-------------------------------------------------------------------------------
-- Semiring folds
-------------------------------------------------------------------------------

-- | Evaluate a semiring sum.
-- 
-- >>> sum [1..5 :: Int]
-- 15
--
sum :: (Additive-Monoid) a => Foldable f => f a -> a
sum = sumWith id

-- | Evaluate a semiring sum using a given semiring.
-- 
sumWith :: (Additive-Monoid) a => Foldable f => (b -> a) -> f b -> a
sumWith f = foldr' ((+) . f) zero
{-# INLINE sumWith #-}

-- | Evaluate a semiring product.
--
-- >>> product [1..5 :: Int]
-- 120
--
product :: (Multiplicative-Monoid) a => Foldable f => f a -> a
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
productWith :: (Multiplicative-Monoid) a => Foldable f => (b -> a) -> f b -> a
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
xmult :: Semiring a => Foldable f => Applicative f => f a -> f a -> a
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
-- @ a '<=' b ⇒ a '+' c '<=' b '+' c @
--
-- @ 'zero' '<=' a '&&' 'zero' '<=' b ⇒ 'zero' '<=' a '*' b @
--
-- See the properties module for a detailed specification of the laws.
--
class (Semiring a, RingLaw a) => Ring a where

infixl 6 -

-- | Subtract two elements.
--
-- @
-- a '-' b = 'subtract' b a
-- @
--
(-) :: (Additive-Group) a => a -> a -> a
a - b = unAdditive (Additive a << Additive b)
{-# INLINE (-) #-}

-- | Reverse the sign of an element.
--
negate :: (Additive-Group) a => a -> a
negate a = zero - a
{-# INLINE negate #-}

-- | Subtract two elements.
--
subtract :: (Additive-Group) a => a -> a -> a
subtract a b = unAdditive (Additive b << Additive a)
{-# INLINE subtract #-}

-- | Absolute value of an element.
--
-- @ 'abs' r = r '*' ('signum' r) @
--
abs :: (Additive-Group) a => Ord a => a -> a
abs x = bool (negate x) x $ zero <= x
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
instance Presemiring a => Presemiring (e -> a)
--instance Presemiring a => Presemiring (Op a e)
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

--instance Ring a => Semiring (Complex a)
instance Semiring a => Semiring (e -> a)
--instance Semiring a => Semiring (Op a e)
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

instance Ring Float
instance Ring Double
instance Ring CFloat
instance Ring CDouble

--instance Ring a => Ring (Complex a)
instance Ring a => Ring (e -> a)
--instance Ring a => Ring (Op a e)



-------------------------------------------------------------------------------
-- Additive
-------------------------------------------------------------------------------

-- | A commutative 'Semigroup' under '+'.
newtype Additive a = Additive { unAdditive :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Additive where
  pure = Additive
  Additive f <*> Additive a = Additive (f a)

instance Distributive Additive where
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Representable Additive where
  type Rep Additive = ()
  tabulate f = Additive (f ())
  {-# INLINE tabulate #-}

  index (Additive x) () = x
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- Multiplicative
-------------------------------------------------------------------------------


-- | A (potentially non-commutative) 'Semigroup' under '*'.
newtype Multiplicative a = Multiplicative { unMultiplicative :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Multiplicative where
  pure = Multiplicative
  Multiplicative f <*> Multiplicative a = Multiplicative (f a)

instance Distributive Multiplicative where
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Representable Multiplicative where
  type Rep Multiplicative = ()
  tabulate f = Multiplicative (f ())
  {-# INLINE tabulate #-}

  index (Multiplicative x) () = x
  {-# INLINE index #-}


---------------------------------------------------------------------
-- Additive semigroup instances
---------------------------------------------------------------------

#define deriveAdditiveSemigroup(ty)             \
instance Semigroup (Additive ty) where {        \
   a <> b = (P.+) <$> a <*> b                   \
;  {-# INLINE (<>) #-}                          \
}

deriveAdditiveSemigroup(Int)
deriveAdditiveSemigroup(Int8)
deriveAdditiveSemigroup(Int16)
deriveAdditiveSemigroup(Int32)
deriveAdditiveSemigroup(Int64)
deriveAdditiveSemigroup(Integer)

deriveAdditiveSemigroup(Word)  --TODO clip these at maxBound to make dioids
deriveAdditiveSemigroup(Word8)
deriveAdditiveSemigroup(Word16)
deriveAdditiveSemigroup(Word32)
deriveAdditiveSemigroup(Word64)
deriveAdditiveSemigroup(Natural)

deriveAdditiveSemigroup(Uni)
deriveAdditiveSemigroup(Deci)
deriveAdditiveSemigroup(Centi)
deriveAdditiveSemigroup(Milli)
deriveAdditiveSemigroup(Micro)
deriveAdditiveSemigroup(Nano)
deriveAdditiveSemigroup(Pico)

deriveAdditiveSemigroup(Float)
deriveAdditiveSemigroup(CFloat)
deriveAdditiveSemigroup(Double)
deriveAdditiveSemigroup(CDouble)

#define deriveAdditiveMonoid(ty)                \
instance Monoid (Additive ty) where {           \
   mempty = pure 0                              \
;  {-# INLINE mempty #-}                        \
}

deriveAdditiveMonoid(Int)
deriveAdditiveMonoid(Int8)
deriveAdditiveMonoid(Int16)
deriveAdditiveMonoid(Int32)
deriveAdditiveMonoid(Int64)
deriveAdditiveMonoid(Integer)

deriveAdditiveMonoid(Word)
deriveAdditiveMonoid(Word8)
deriveAdditiveMonoid(Word16)
deriveAdditiveMonoid(Word32)
deriveAdditiveMonoid(Word64)
deriveAdditiveMonoid(Natural)

deriveAdditiveMonoid(Uni)
deriveAdditiveMonoid(Deci)
deriveAdditiveMonoid(Centi)
deriveAdditiveMonoid(Milli)
deriveAdditiveMonoid(Micro)
deriveAdditiveMonoid(Nano)
deriveAdditiveMonoid(Pico)

deriveAdditiveMonoid(Float)
deriveAdditiveMonoid(CFloat)
deriveAdditiveMonoid(Double)
deriveAdditiveMonoid(CDouble)

#define deriveAdditiveMagma(ty)                 \
instance Magma (Additive ty) where {            \
   a << b = (P.-) <$> a <*> b                   \
;  {-# INLINE (<<) #-}                          \
}

deriveAdditiveMagma(Int)
deriveAdditiveMagma(Int8)
deriveAdditiveMagma(Int16)
deriveAdditiveMagma(Int32)
deriveAdditiveMagma(Int64)
deriveAdditiveMagma(Integer)

deriveAdditiveMagma(Uni)
deriveAdditiveMagma(Deci)
deriveAdditiveMagma(Centi)
deriveAdditiveMagma(Milli)
deriveAdditiveMagma(Micro)
deriveAdditiveMagma(Nano)
deriveAdditiveMagma(Pico)

deriveAdditiveMagma(Float)
deriveAdditiveMagma(CFloat)
deriveAdditiveMagma(Double)
deriveAdditiveMagma(CDouble)

#define deriveAdditiveQuasigroup(ty)            \
instance Quasigroup (Additive ty) where {             \
}

deriveAdditiveQuasigroup(Int)
deriveAdditiveQuasigroup(Int8)
deriveAdditiveQuasigroup(Int16)
deriveAdditiveQuasigroup(Int32)
deriveAdditiveQuasigroup(Int64)
deriveAdditiveQuasigroup(Integer)

deriveAdditiveQuasigroup(Uni)
deriveAdditiveQuasigroup(Deci)
deriveAdditiveQuasigroup(Centi)
deriveAdditiveQuasigroup(Milli)
deriveAdditiveQuasigroup(Micro)
deriveAdditiveQuasigroup(Nano)
deriveAdditiveQuasigroup(Pico)

deriveAdditiveQuasigroup(Float)
deriveAdditiveQuasigroup(CFloat)
deriveAdditiveQuasigroup(Double)
deriveAdditiveQuasigroup(CDouble)

#define deriveAdditiveLoop(ty)                  \
instance Loop (Additive ty) where {             \
   lreplicate n (Additive a) = Additive $ P.fromIntegral n  *  (-a) \
;  {-# INLINE lreplicate #-}                    \
}

deriveAdditiveLoop(Int)
deriveAdditiveLoop(Int8)
deriveAdditiveLoop(Int16)
deriveAdditiveLoop(Int32)
deriveAdditiveLoop(Int64)
deriveAdditiveLoop(Integer)

deriveAdditiveLoop(Uni)
deriveAdditiveLoop(Deci)
deriveAdditiveLoop(Centi)
deriveAdditiveLoop(Milli)
deriveAdditiveLoop(Micro)
deriveAdditiveLoop(Nano)
deriveAdditiveLoop(Pico)

deriveAdditiveLoop(Float)
deriveAdditiveLoop(CFloat)
deriveAdditiveLoop(Double)
deriveAdditiveLoop(CDouble)

#define deriveAdditiveGroup(ty)                 \
instance Group (Additive ty) where {            \
   greplicate n (Additive a) = Additive $ P.fromInteger n  *  a \
;  {-# INLINE greplicate #-}                    \
}

deriveAdditiveGroup(Int)
deriveAdditiveGroup(Int8)
deriveAdditiveGroup(Int16)
deriveAdditiveGroup(Int32)
deriveAdditiveGroup(Int64)
deriveAdditiveGroup(Integer)

deriveAdditiveGroup(Uni)
deriveAdditiveGroup(Deci)
deriveAdditiveGroup(Centi)
deriveAdditiveGroup(Milli)
deriveAdditiveGroup(Micro)
deriveAdditiveGroup(Nano)
deriveAdditiveGroup(Pico)

deriveAdditiveGroup(Float)
deriveAdditiveGroup(CFloat)
deriveAdditiveGroup(Double)
deriveAdditiveGroup(CDouble)


instance ((Additive-Semigroup) a, Free f, Free g) => Semigroup (Additive ((f++g) a)) where
   (<>) = liftA2 $ mzipWithRep (+)
   {-# INLINE (<>) #-}

instance ((Additive-Monoid) a, Free f, Free g) => Monoid (Additive ((f++g) a)) where
   mempty = pure $ pureRep zero 
   {-# INLINE mempty #-}

instance ((Additive-Group) a, Free f, Free g) => Magma (Additive ((f++g) a)) where
   (<<) = liftA2 $ mzipWithRep (-)
   {-# INLINE (<<) #-}

instance ((Additive-Group) a, Free f, Free g) => Quasigroup (Additive ((f++g) a))
instance ((Additive-Group) a, Free f, Free g) => Loop (Additive ((f++g) a))
instance ((Additive-Group) a, Free f, Free g) => Group (Additive ((f++g) a))

instance ((Additive-Semigroup) a, Free f, Free g) => Semigroup (Additive ((f**g) a)) where
   (<>) = liftA2 $ mzipWithRep (+)
   {-# INLINE (<>) #-}

instance ((Additive-Monoid) a, Free f, Free g) => Monoid (Additive ((f**g) a)) where
   mempty = pure $ pureRep zero 
   {-# INLINE mempty #-}

instance ((Additive-Group) a, Free f, Free g) => Magma (Additive ((f**g) a)) where
   (<<) = liftA2 $ mzipWithRep (-)
   {-# INLINE (<<) #-}

instance ((Additive-Group) a, Free f, Free g) => Quasigroup (Additive ((f**g) a))
instance ((Additive-Group) a, Free f, Free g) => Loop (Additive ((f**g) a))
instance ((Additive-Group) a, Free f, Free g) => Group (Additive ((f**g) a))

instance (Additive-Semigroup) a => Semigroup (Additive (Complex a)) where
  Additive (a :+ b) <> Additive (c :+ d) = Additive $ (a + b) :+ (c + d)
  {-# INLINE (<>) #-}

instance (Additive-Monoid) a => Monoid (Additive (Complex a)) where
  mempty = Additive $ zero :+ zero

instance (Additive-Group) a => Magma (Additive (Complex a)) where
  Additive (a :+ b) << Additive (c :+ d) = Additive $ (subtract c a) :+ (subtract d b)
  {-# INLINE (<<) #-}

instance (Additive-Group) a => Quasigroup (Additive (Complex a))

instance (Additive-Group) a => Loop (Additive (Complex a)) where
  lreplicate n = mreplicate n . inv

instance (Additive-Group) a => Group (Additive (Complex a))

-- type Rng a = ((Additive-Group) a, (Multiplicative-Semigroup) a)
instance ((Additive-Group) a, (Multiplicative-Semigroup) a) => Semigroup (Multiplicative (Complex a)) where
  Multiplicative (a :+ b) <> Multiplicative (c :+ d) = Multiplicative $ (subtract (b * d) (a * c)) :+ (a * d + b * c)
  {-# INLINE (<>) #-}

{-
-- type Ring a = ((Additive-Group) a, (Multiplicative-Monoid) a)
instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Monoid (Multiplicative (Complex a)) where
  mempty = Multiplicative $ one :+ zero

instance ((Additive-Group) a, (Multiplicative-Group) a) => Magma (Multiplicative (Complex a)) where
  Multiplicative (a :+ b) << Multiplicative (c :+ d) = Multiplicative $ ((a * c + b * d) / (c * c + d * d)) :+ ((subtract (a * d) (b * c)) / (c * c + d * d))
  {-# INLINE (<<) #-}

instance ((Additive-Group) a, (Multiplicative-Group) a) => Quasigroup (Multiplicative (Complex a))

instance ((Additive-Group) a, (Multiplicative-Group) a) => Loop (Multiplicative (Complex a)) where
  lreplicate n = mreplicate n . inv

instance ((Additive-Group) a, (Multiplicative-Group) a) => Group (Multiplicative (Complex a))
-}

instance ((Additive-Semigroup) a, (Multiplicative-Semigroup) a) => Semigroup (Additive (Ratio a)) where
  Additive (a :% b) <> Additive (c :% d) = Additive $ (a * d + c * b) :% (b  *  d)
  {-# INLINE (<>) #-}

instance ((Additive-Monoid) a, (Multiplicative-Monoid) a) => Monoid (Additive (Ratio a)) where
  mempty = Additive $ zero :% one

instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Magma (Additive (Ratio a)) where
  Additive (a :% b) << Additive (c :% d) = Additive $ (subtract (c * b) (a * d)) :% (b  *  d)
  {-# INLINE (<<) #-}

instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Quasigroup (Additive (Ratio a))

instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Loop (Additive (Ratio a)) where
  lreplicate n = mreplicate n . inv

instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Group (Additive (Ratio a))

instance (Additive-Semigroup) b => Semigroup (Additive (a -> b)) where
  (<>) = liftA2 . liftA2 $ (+)
  {-# INLINE (<>) #-}

instance (Additive-Monoid) b => Monoid (Additive (a -> b)) where
  mempty = pure . pure $ zero

instance (Additive-Group) b => Magma (Additive (a -> b)) where
  (<<) = liftA2 . liftA2 $ flip subtract 

instance (Additive-Group) b => Quasigroup (Additive (a -> b)) where
instance (Additive-Group) b => Loop (Additive (a -> b)) where
instance (Additive-Group) b => Group (Additive (a -> b)) where

instance ((Additive-Semigroup) a) => Semigroup (Additive (Op a b)) where
  Additive (Op f) <> Additive (Op g) = Additive . Op $ \b -> f b + g b
  {-# INLINE (<>) #-}

instance ((Additive-Monoid) a) => Monoid (Additive (Op a b)) where
  mempty = Additive . Op $ const zero

instance ((Additive-Group) a) => Magma (Additive (Op a b)) where
  Additive (Op f) << Additive (Op g) = Additive . Op $ \b -> f b - g b
  {-# INLINE (<<) #-}

instance ((Additive-Group) a) => Quasigroup (Additive (Op a b))
instance ((Additive-Group) a) => Loop (Additive (Op a b)) where
instance ((Additive-Group) a) => Group (Additive (Op a b))

instance Semigroup (Additive [a]) where
  (<>) = liftA2 (<>)

instance Monoid (Additive [a]) where
  mempty = pure mempty

-- >>> [1, 2] * [3, 4]
-- [4,5,5,6]
instance (Additive-Semigroup) a => Semigroup (Multiplicative [a]) where 
  (<>) = liftA2 . liftA2 $ (+) 
  {-# INLINE (<>) #-}

instance (Additive-Monoid) a => Monoid (Multiplicative [a]) where 
  mempty = pure [zero]

-- >>> (1 :| [2 :: Int]) * (3 :| [4 :: Int])
-- 4 :| [5,5,6]
instance Semigroup (Additive (NonEmpty a)) where
  (<>) = liftA2 (<>)

instance (Additive-Semigroup) a => Semigroup (Multiplicative (NonEmpty a)) where
  (<>) = liftA2 (+) 
  {-# INLINE (<>) #-}



-- MinPlus Predioid
-- >>> Min 1  *  Min 2 :: Min Int
-- Min {getMin = 3}
instance (Additive-Semigroup) a => Semigroup (Multiplicative (Min a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 (+) a b

-- MinPlus Dioid
instance (Additive-Monoid) a => Monoid (Multiplicative (Min a)) where
  mempty = Multiplicative $ pure zero

instance (Additive-Semigroup) a => Semigroup (Additive (Down a)) where
  (<>) = liftA2 . liftA2 $ (+) 

instance (Additive-Monoid) a => Monoid (Additive (Down a)) where
  --Additive (Down a) <> Additive (Down b)
  mempty = pure . pure $ zero



instance Semigroup (Additive ()) where
  _ <> _ = pure ()
  {-# INLINE (<>) #-}

instance Monoid (Additive ()) where
  mempty = pure ()
  {-# INLINE mempty #-}

instance Magma (Additive ()) where
  _ << _ = pure ()

instance Quasigroup (Additive ()) 

instance Loop (Additive ()) 

instance Group (Additive ()) 

instance Semigroup (Additive Bool) where
  a <> b = (P.||) <$> a <*> b
  {-# INLINE (<>) #-}

instance Monoid (Additive Bool) where
  mempty = pure False
  {-# INLINE mempty #-}

--instance ((Additive-Semigroup) a, Minimal a) => Monoid (Additive a) where
--  mempty = Additive minimal

-- instance (Meet-Monoid) (Down a) => Monoid (Meet (Down a)) where mempty = Down <$> mempty

instance ((Additive-Semigroup) a, (Additive-Semigroup) b) => Semigroup (Additive (a, b)) where
  (<>) = liftA2 $ \(x1,y1) (x2,y2) -> (x1+x2, y1+y2)

instance ((Additive-Monoid) a, (Additive-Monoid) b) => Monoid (Additive (a, b)) where
  mempty = pure (zero, zero)

instance ((Additive-Semigroup) a, (Additive-Semigroup) b, (Additive-Semigroup) c) => Semigroup (Additive (a, b, c)) where
  (<>) = liftA2 $ \(x1,y1,z1) (x2,y2,z2) -> (x1+x2, y1+y2, z1+z2)

instance ((Additive-Monoid) a, (Additive-Monoid) b, (Additive-Monoid) c) => Monoid (Additive (a, b, c)) where
  mempty = pure (zero, zero, zero)

instance (Additive-Semigroup) a => Semigroup (Additive (Maybe a)) where
  Additive (Just x) <> Additive (Just y) = Additive . Just $ x + y
  Additive (x@Just{}) <> _           = Additive x
  Additive Nothing  <> y             = y

instance (Additive-Semigroup) a => Monoid (Additive (Maybe a)) where
  mempty = Additive Nothing

instance ((Additive-Semigroup) a, (Additive-Semigroup) b) => Semigroup (Additive (Either a b)) where
  Additive (Right x) <> Additive (Right y) = Additive . Right $ x + y

  Additive(x@Right{}) <> _     = Additive x
  Additive (Left x)  <> Additive (Left y)  = Additive . Left $ x + y
  Additive (Left _)  <> y     = y

instance Ord a => Semigroup (Additive (Set.Set a)) where
  (<>) = liftA2 Set.union 

instance (Ord k, (Additive-Semigroup) a) => Semigroup (Additive (Map.Map k a)) where
  (<>) = liftA2 (Map.unionWith (+))

instance (Additive-Semigroup) a => Semigroup (Additive (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.unionWith (+))

instance Semigroup (Additive IntSet.IntSet) where
  (<>) = liftA2 IntSet.union 

instance Monoid (Additive IntSet.IntSet) where
  mempty = Additive IntSet.empty

instance (Additive-Semigroup) a => Monoid (Additive (IntMap.IntMap a)) where
  mempty = Additive IntMap.empty

instance Ord a => Monoid (Additive (Set.Set a)) where
  mempty = Additive Set.empty

instance (Ord k, (Additive-Semigroup) a) => Monoid (Additive (Map.Map k a)) where
  mempty = Additive Map.empty




---------------------------------------------------------------------
-- Multiplicative Semigroup Instances
---------------------------------------------------------------------

#define deriveMultiplicativeSemigroup(ty)       \
instance Semigroup (Multiplicative ty) where {  \
   a <> b = (P.*) <$> a <*> b                   \
;  {-# INLINE (<>) #-}                          \
}

deriveMultiplicativeSemigroup(Int)
deriveMultiplicativeSemigroup(Int8)
deriveMultiplicativeSemigroup(Int16)
deriveMultiplicativeSemigroup(Int32)
deriveMultiplicativeSemigroup(Int64)
deriveMultiplicativeSemigroup(Integer)

deriveMultiplicativeSemigroup(Word)
deriveMultiplicativeSemigroup(Word8)
deriveMultiplicativeSemigroup(Word16)
deriveMultiplicativeSemigroup(Word32)
deriveMultiplicativeSemigroup(Word64)
deriveMultiplicativeSemigroup(Natural)

deriveMultiplicativeSemigroup(Uni)
deriveMultiplicativeSemigroup(Deci)
deriveMultiplicativeSemigroup(Centi)
deriveMultiplicativeSemigroup(Milli)
deriveMultiplicativeSemigroup(Micro)
deriveMultiplicativeSemigroup(Nano)
deriveMultiplicativeSemigroup(Pico)

deriveMultiplicativeSemigroup(Float)
deriveMultiplicativeSemigroup(CFloat)
deriveMultiplicativeSemigroup(Double)
deriveMultiplicativeSemigroup(CDouble)

#define deriveMultiplicativeMonoid(ty)          \
instance Monoid (Multiplicative ty) where {     \
   mempty = pure 1                              \
;  {-# INLINE mempty #-}                        \
}

deriveMultiplicativeMonoid(Int)
deriveMultiplicativeMonoid(Int8)
deriveMultiplicativeMonoid(Int16)
deriveMultiplicativeMonoid(Int32)
deriveMultiplicativeMonoid(Int64)
deriveMultiplicativeMonoid(Integer)

deriveMultiplicativeMonoid(Word)
deriveMultiplicativeMonoid(Word8)
deriveMultiplicativeMonoid(Word16)
deriveMultiplicativeMonoid(Word32)
deriveMultiplicativeMonoid(Word64)
deriveMultiplicativeMonoid(Natural)

deriveMultiplicativeMonoid(Uni)
deriveMultiplicativeMonoid(Deci)
deriveMultiplicativeMonoid(Centi)
deriveMultiplicativeMonoid(Milli)
deriveMultiplicativeMonoid(Micro)
deriveMultiplicativeMonoid(Nano)
deriveMultiplicativeMonoid(Pico)

deriveMultiplicativeMonoid(Float)
deriveMultiplicativeMonoid(CFloat)
deriveMultiplicativeMonoid(Double)
deriveMultiplicativeMonoid(CDouble)

#define deriveMultiplicativeMagma(ty)                 \
instance Magma (Multiplicative ty) where {            \
   a << b = (P./) <$> a <*> b                         \
;  {-# INLINE (<<) #-}                                \
}

deriveMultiplicativeMagma(Uni)
deriveMultiplicativeMagma(Deci)
deriveMultiplicativeMagma(Centi)
deriveMultiplicativeMagma(Milli)
deriveMultiplicativeMagma(Micro)
deriveMultiplicativeMagma(Nano)
deriveMultiplicativeMagma(Pico)

deriveMultiplicativeMagma(Float)
deriveMultiplicativeMagma(CFloat)
deriveMultiplicativeMagma(Double)
deriveMultiplicativeMagma(CDouble)

#define deriveMultiplicativeQuasigroup(ty)            \
instance Quasigroup (Multiplicative ty) where {       \
}

deriveMultiplicativeQuasigroup(Uni)
deriveMultiplicativeQuasigroup(Deci)
deriveMultiplicativeQuasigroup(Centi)
deriveMultiplicativeQuasigroup(Milli)
deriveMultiplicativeQuasigroup(Micro)
deriveMultiplicativeQuasigroup(Nano)
deriveMultiplicativeQuasigroup(Pico)

deriveMultiplicativeQuasigroup(Float)
deriveMultiplicativeQuasigroup(CFloat)
deriveMultiplicativeQuasigroup(Double)
deriveMultiplicativeQuasigroup(CDouble)

#define deriveMultiplicativeLoop(ty)                  \
instance Loop (Multiplicative ty) where {             \
   lreplicate n = mreplicate n . inv                  \
}

deriveMultiplicativeLoop(Uni)
deriveMultiplicativeLoop(Deci)
deriveMultiplicativeLoop(Centi)
deriveMultiplicativeLoop(Milli)
deriveMultiplicativeLoop(Micro)
deriveMultiplicativeLoop(Nano)
deriveMultiplicativeLoop(Pico)

deriveMultiplicativeLoop(Float)
deriveMultiplicativeLoop(CFloat)
deriveMultiplicativeLoop(Double)
deriveMultiplicativeLoop(CDouble)

#define deriveMultiplicativeGroup(ty)           \
instance Group (Multiplicative ty) where {      \
   greplicate n (Multiplicative a) = Multiplicative $ a P.^^ P.fromInteger n \
;  {-# INLINE greplicate #-}                    \
}

deriveMultiplicativeGroup(Uni)
deriveMultiplicativeGroup(Deci)
deriveMultiplicativeGroup(Centi)
deriveMultiplicativeGroup(Milli)
deriveMultiplicativeGroup(Micro)
deriveMultiplicativeGroup(Nano)
deriveMultiplicativeGroup(Pico)

deriveMultiplicativeGroup(Float)
deriveMultiplicativeGroup(CFloat)
deriveMultiplicativeGroup(Double)
deriveMultiplicativeGroup(CDouble)



instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Ratio a)) where
  Multiplicative (a :% b) <> Multiplicative (c :% d) = Multiplicative $ (a * c) :% (b * d)
  {-# INLINE (<>) #-}

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Ratio a)) where
  mempty = Multiplicative $ unMultiplicative mempty :% unMultiplicative mempty

instance (Multiplicative-Monoid) a => Magma (Multiplicative (Ratio a)) where
  Multiplicative (a :% b) << Multiplicative (c :% d) = Multiplicative $ (a * d) :% (b * c)
  {-# INLINE (<<) #-}

instance (Multiplicative-Monoid) a => Quasigroup (Multiplicative (Ratio a))

instance (Multiplicative-Monoid) a => Loop (Multiplicative (Ratio a)) where
  lreplicate n = mreplicate n . inv

instance (Multiplicative-Monoid) a => Group (Multiplicative (Ratio a))


---------------------------------------------------------------------
-- Misc
---------------------------------------------------------------------

--instance ((Multiplicative-Semigroup) a, Maximal a) => Monoid (Multiplicative a) where
--  mempty = Multiplicative maximal

instance Semigroup (Multiplicative ()) where
  _ <> _ = pure ()
  {-# INLINE (<>) #-}

instance Monoid (Multiplicative ()) where
  mempty = pure ()
  {-# INLINE mempty #-}

instance  Magma (Multiplicative ()) where
  _ << _ = pure ()
  {-# INLINE (<<) #-}

instance Quasigroup (Multiplicative ())

instance Loop (Multiplicative ())

instance Group (Multiplicative ())

instance Semigroup (Multiplicative Bool) where
  a <> b = (P.&&) <$> a <*> b
  {-# INLINE (<>) #-}

instance Monoid (Multiplicative Bool) where
  mempty = pure True
  {-# INLINE mempty #-}

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Dual a)) where
  (<>) = liftA2 . liftA2 $ flip (*)

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Dual a)) where
  mempty = pure . pure $ one

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Down a)) where
  --Additive (Down a) <> Additive (Down b)
  (<>) = liftA2 . liftA2 $ (*) 

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Down a)) where
  mempty = pure . pure $ one

-- MaxTimes Predioid

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Max a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 (*) a b

-- MaxTimes Dioid
instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Max a)) where
  mempty = Multiplicative $ pure one

instance ((Multiplicative-Semigroup) a, (Multiplicative-Semigroup) b) => Semigroup (Multiplicative (a, b)) where
  Multiplicative (x1, y1) <> Multiplicative (x2, y2) = Multiplicative (x1 * x2, y1 * y2)

instance (Multiplicative-Semigroup) b => Semigroup (Multiplicative (a -> b)) where
  (<>) = liftA2 . liftA2 $ (*)
  {-# INLINE (<>) #-}

instance (Multiplicative-Monoid) b => Monoid (Multiplicative (a -> b)) where
  mempty = pure . pure $ one

{-
instance ((Multiplicative-Semigroup) a) => Semigroup (Multiplicative (Op a b)) where
  Multiplicative (Op f) <> Multiplicative (Op g) = Multiplicative . Op $ \b -> f b * g b
  {-# INLINE (<>) #-}

instance ((Multiplicative-Monoid) a) => Monoid (Multiplicative (Op a b)) where
  mempty = Multiplicative . Op $ const one
-}

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Maybe a)) where
  Multiplicative Nothing  <> _             = Multiplicative Nothing
  Multiplicative (Just{}) <> Multiplicative Nothing   = Multiplicative Nothing
  Multiplicative (Just x) <> Multiplicative (Just y) = Multiplicative . Just $ x * y
  -- Mul a <> Mul b = Mul $ liftA2 (*) a b

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Maybe a)) where
  mempty = Multiplicative $ pure one

instance ((Multiplicative-Semigroup) a, (Multiplicative-Semigroup) b) => Semigroup (Multiplicative (Either a b)) where
  Multiplicative (Right x) <> Multiplicative (Right y) = Multiplicative . Right $ x * y
  Multiplicative (Right{}) <> y     = y
  Multiplicative (Left x) <> Multiplicative (Left y)  = Multiplicative . Left $ x * y
  Multiplicative (x@Left{}) <> _     = Multiplicative x

instance Ord a => Semigroup (Multiplicative (Set.Set a)) where
  (<>) = liftA2 Set.intersection 

instance (Ord k, (Multiplicative-Semigroup) a) => Semigroup (Multiplicative (Map.Map k a)) where
  (<>) = liftA2 (Map.intersectionWith (*))

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.intersectionWith (*))

instance Semigroup (Multiplicative IntSet.IntSet) where
  (<>) = liftA2 IntSet.intersection 

instance (Ord k, (Multiplicative-Monoid) k, (Multiplicative-Monoid) a) => Monoid (Multiplicative (Map.Map k a)) where
  mempty = Multiplicative $ Map.singleton one one

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (IntMap.IntMap a)) where
  mempty = Multiplicative $ IntMap.singleton 0 one
