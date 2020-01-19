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

module Data.Semigroup.Multiplicative where

import safe Data.Ord
import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Maybe
import safe Data.Either
import safe Data.Fixed
import safe Data.Foldable as Foldable (Foldable, foldr', foldl')
import safe Data.Group
import safe Data.Int
import safe Data.List
import safe Data.List.NonEmpty
import safe Data.Magma
import safe Data.Semigroup
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Tuple
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..), div, (^^), (^))
import safe Numeric.Natural
--import safe Prelude ( Eq, Ord, Show, Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import safe Prelude ( Eq(..), Ord, Show, Ordering(..), Bounded(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as Seq


import safe Data.Distributive
import safe Data.Functor.Rep

infixr 1 -

-- | Hyphenation operator.
type (g - f) a = f (g a)  


mul :: (Multiplicative-Semigroup) a => a -> a -> a
a `mul` b = unMultiplicative (Multiplicative a <> Multiplicative b)
{-# INLINE mul #-}

one :: (Multiplicative-Monoid) a => a
one = unMultiplicative mempty
{-# INLINE one #-}

-- infixl 7 /

div :: (Multiplicative-Group) a => a -> a -> a
a `div` b = unMultiplicative (Multiplicative a << Multiplicative b)
{-# INLINE div #-}

-- | Take the reciprocal of a multiplicative group element.
--
-- >>> recip (3 :+ 4) :: Complex Rational
-- 3 % 25 :+ (-4) % 25
-- >>> recip (3 :+ 4) :: Complex Double
-- 0.12 :+ (-0.16)
-- >>> recip (3 :+ 4) :: Complex Pico
-- 0.120000000000 :+ -0.160000000000
-- 
recip :: (Multiplicative-Group) a => a -> a 
recip a = one `div` a
{-# INLINE recip #-}

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
-- Num-based instances
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

---------------------------------------------------------------------
-- Ratio
---------------------------------------------------------------------

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Ratio a)) where
  Multiplicative (a :% b) <> Multiplicative (c :% d) = Multiplicative $ (a `mul` c) :% (b `mul` d)
  {-# INLINE (<>) #-}

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Ratio a)) where
  mempty = Multiplicative $ unMultiplicative mempty :% unMultiplicative mempty

instance (Multiplicative-Monoid) a => Magma (Multiplicative (Ratio a)) where
  Multiplicative (a :% b) << Multiplicative (c :% d) = Multiplicative $ (a `mul` d) :% (b `mul` c)
  {-# INLINE (<<) #-}

instance (Multiplicative-Monoid) a => Quasigroup (Multiplicative (Ratio a))

instance (Multiplicative-Monoid) a => Loop (Multiplicative (Ratio a)) where
  lreplicate n = mreplicate n . inv

instance (Multiplicative-Monoid) a => Group (Multiplicative (Ratio a))

---------------------------------------------------------------------
-- Semigroup Instances
---------------------------------------------------------------------

--instance ((Multiplicative-Semigroup) a, Maximal a) => Monoid (Multiplicative a) where
--  mempty = Multiplicative maximal

instance Semigroup (Multiplicative ()) where
  _ <> _ = pure ()
  {-# INLINE (<>) #-}

instance Monoid (Multiplicative ()) where
  mempty = pure ()
  {-# INLINE mempty #-}

instance Semigroup (Multiplicative Bool) where
  a <> b = (P.&&) <$> a <*> b
  {-# INLINE (<>) #-}

instance Monoid (Multiplicative Bool) where
  mempty = pure True
  {-# INLINE mempty #-}

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Dual a)) where
  (<>) = liftA2 . liftA2 $ flip mul

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Dual a)) where
  mempty = pure . pure $ one

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Down a)) where
  --Additive (Down a) <> Additive (Down b)
  (<>) = liftA2 . liftA2 $ mul 

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Down a)) where
  mempty = pure . pure $ one

-- MaxTimes Predioid

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Max a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 mul a b

-- MaxTimes Dioid
instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Max a)) where
  mempty = Multiplicative $ pure one


instance ((Multiplicative-Semigroup) a, (Multiplicative-Semigroup) b) => Semigroup (Multiplicative (a, b)) where
  Multiplicative (x1, y1) <> Multiplicative (x2, y2) = Multiplicative (x1 `mul` x2, y1 `mul` y2)

instance (Multiplicative-Semigroup) b => Semigroup (Multiplicative (a -> b)) where
  (<>) = liftA2 . liftA2 $ mul
  {-# INLINE (<>) #-}

instance (Multiplicative-Monoid) b => Monoid (Multiplicative (a -> b)) where
  mempty = pure . pure $ one

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Maybe a)) where
  Multiplicative Nothing  <> _             = Multiplicative Nothing
  Multiplicative (x@Just{}) <> Multiplicative Nothing   = Multiplicative Nothing
  Multiplicative (Just x) <> Multiplicative (Just y) = Multiplicative . Just $ x `mul` y


  -- Mul a <> Mul b = Mul $ liftA2 mul a b

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Maybe a)) where
  mempty = Multiplicative $ pure one

instance ((Multiplicative-Semigroup) a, (Multiplicative-Semigroup) b) => Semigroup (Multiplicative (Either a b)) where
  Multiplicative (Right x) <> Multiplicative (Right y) = Multiplicative . Right $ x `mul` y
  Multiplicative(x@Right{}) <> y     = y
  Multiplicative (Left x) <> Multiplicative (Left y)  = Multiplicative . Left $ x `mul` y
  Multiplicative (x@Left{}) <> _     = Multiplicative x

instance Ord a => Semigroup (Multiplicative (Set.Set a)) where
  a <> b = Set.intersection <$> a <*> b

instance (Ord k, (Multiplicative-Semigroup) a) => Semigroup (Multiplicative (Map.Map k a)) where
  a <> b = Map.intersectionWith mul <$> a <*> b

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (IntMap.IntMap a)) where
  a <> b = IntMap.intersectionWith mul <$> a <*> b

instance Semigroup (Multiplicative IntSet.IntSet) where
  a <> b = IntSet.intersection <$> a <*> b

instance (Ord k, (Multiplicative-Monoid) k, (Multiplicative-Monoid) a) => Monoid (Multiplicative (Map.Map k a)) where
  mempty = Multiplicative $ Map.singleton one one

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (IntMap.IntMap a)) where
  mempty = Multiplicative $ IntMap.singleton 0 one

{-


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
