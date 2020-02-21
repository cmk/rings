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
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Data.Semigroup.Additive where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Maybe
import safe Data.Either
import safe Data.Distributive
import safe Data.Functor.Rep
import safe Data.Fixed
import safe Data.Group hiding ((\\))
import safe Data.Int
import safe Data.List.NonEmpty
import safe Data.Ord
import safe Data.Semigroup
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..), div, (^^), (^), (%))
import safe Numeric.Natural

import safe Prelude
 ( Eq(..), Ord(..), Show, Applicative(..), Functor(..), Monoid(..), Semigroup(..)
 , (.), ($), (<$>), flip, Integer, Float, Double)
import safe qualified Prelude as P

import safe qualified Data.Map as Map
import safe qualified Data.Set as Set
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet

infixr 1 -

-- | Hyphenation operator.
type (g - f) a = f (g a)

-------------------------------------------------------------------------------
-- Additive
-------------------------------------------------------------------------------

-- | A commutative 'Semigroup' under '+'.
newtype Additive a = Additive { unAdditive :: a } deriving (Eq, Generic, Ord, Show, Functor)

-- | The additive unit of a semiring.
--
zero :: (Additive-Monoid) a => a
zero = unAdditive mempty
{-# INLINE zero #-}

infixl 6 +

-- >>> Dual [2] + Dual [3] :: Dual [Int]
-- Dual {getDual = [3,2]}
(+) :: (Additive-Semigroup) a => a -> a -> a
a + b = unAdditive (Additive a <> Additive b)
{-# INLINE (+) #-}

-- | Subtract two elements.
--
subtract :: (Additive-Group) a => a -> a -> a
subtract a b = unAdditive (Additive b << Additive a)
{-# INLINE subtract #-}

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

-- | The multiplicative unit of a semiring.
--
one :: (Multiplicative-Monoid) a => a
one = unMultiplicative mempty
{-# INLINE one #-}

infixl 7 *, \\, /

-- | Multiply two elements.
--
-- >>> Dual [2] * Dual [3] :: Dual [Int]
-- Dual {getDual = [5]}
--
(*) :: (Multiplicative-Semigroup) a => a -> a -> a
a * b = unMultiplicative (Multiplicative a <> Multiplicative b)
{-# INLINE (*) #-}

-- | Reciprocal of a multiplicative group element.
--
-- @ 
-- x '/' y = x '*' 'recip' y
-- x '\\' y = 'recip' x '*' y
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
recip a = one / a
{-# INLINE recip #-}

-- | Right division by a multiplicative group element.
--
(/) :: (Multiplicative-Group) a => a -> a -> a
a / b = unMultiplicative (Multiplicative a << Multiplicative b)
{-# INLINE (/) #-}

-- | Left division by a multiplicative group element.
--
-- When '*' is commutative we must have:
--
-- @ x '\\' y = y '/' x @
--
(\\) :: (Multiplicative-Group) a => a -> a -> a
(\\) x y = recip x * y

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
