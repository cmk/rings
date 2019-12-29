{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}

module Data.Semiring.V2 where

import Data.Dioid
import Data.Distributive
import Data.Foldable as Foldable (fold, foldl')
import Data.Functor.Rep
import Data.Group
import Data.Prd
import Data.Ring
import Data.Semigroup.Foldable as Foldable1
import Data.Semiring

import Prelude hiding (sum, negate)

data V2 a = V2 !a !a deriving (Eq,Ord,Show)

instance Prd a => Prd (V2 a) where
  V2 a b <~ V2 d e = a <~ d && b <~ e

-- | Entry-wise vector or matrix addition.
--
-- >>> V2 (V3 1 2 3) (V3 4 5 6) <> V2 (V3 7 8 9) (V3 1 2 3)
-- V2 (V3 8 10 12) (V3 5 7 9)
--
instance Semigroup a => Semigroup (V2 a) where
  (<>) = mzipWithRep (<>)

instance Monoid a => Monoid (V2 a) where
  mempty = pureRep mempty

-- | Entry-wise vector or matrix multiplication.
--
-- >>> V2 (V3 1 2 3) (V3 4 5 6) >< V2 (V3 7 8 9) (V3 1 2 3)
-- V2 (V3 7 16 27) (V3 4 10 18)
--
instance Unital a => Semiring (V2 a) where
  (><) = mzipWithRep (><)
  fromBoolean = pureRep . fromBoolean

instance (Monoid a, Dioid a) => Dioid (V2 a) where
  fromNatural = pureRep . fromNatural

-- | Entry-wise vector or matrix subtraction.
--
-- >>> V2 (V3 1 2 3) (V3 4 5 6) << V2 (V3 7 8 9) (V3 1 2 3)
-- V2 (V3 (-6) (-6) (-6)) (V3 3 3 3)
--
instance Group a => Group (V2 a) where
  (<<) = mzipWithRep (<<)

instance Functor V2 where
  fmap f (V2 a b) = V2 (f a) (f b)
  {-# INLINE fmap #-}
  a <$ _ = V2 a a
  {-# INLINE (<$) #-}

instance Foldable V2 where
  foldMap f (V2 a b) = f a <> f b
  {-# INLINE foldMap #-}
  null _ = False
  length _ = 2

instance Foldable1 V2 where
  foldMap1 f (V2 a b) = f a <> f b
  {-# INLINE foldMap1 #-}

instance Distributive V2 where
  distribute f = V2 (fmap (\(V2 x _) -> x) f) (fmap (\(V2 _ y) -> y) f)
  {-# INLINE distribute #-}

data I2 = I21 | I22 deriving (Eq, Ord, Show)

instance Representable V2 where
  type Rep V2 = I2
  tabulate f = V2 (f I21) (f I22)
  {-# INLINE tabulate #-}

  index (V2 x _) I21 = x
  index (V2 _ y) I22 = y
  {-# INLINE index #-}

instance Prd I2 where
  (<~) = (<=)
  (>~) = (>=)
  pcompare = pcompareOrd

instance Minimal I2 where
  minimal = I21

instance Maximal I2 where
  maximal = I22
