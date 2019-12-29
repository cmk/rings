{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}

module Data.Semiring.V4 where

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

data V4 a = V4 !a !a !a !a deriving (Eq,Ord,Show)

instance Prd a => Prd (V4 a) where
  V4 a b c d <~ V4 e f g h = a <~ e && b <~ f && c <~ g && d <~ h

instance Semigroup a => Semigroup (V4 a) where
  (<>) = mzipWithRep (<>)

instance Monoid a => Monoid (V4 a) where
  mempty = pureRep mempty

instance Unital a => Semiring (V4 a) where
  (><) = mzipWithRep (><)
  fromBoolean = pureRep . fromBoolean

instance (Monoid a, Dioid a) => Dioid (V4 a) where
  fromNatural = pureRep . fromNatural

instance Group a => Group (V4 a) where
  (<<) = mzipWithRep (<<)

instance Functor V4 where
  fmap f (V4 a b c d) = V4 (f a) (f b) (f c) (f d)
  {-# INLINE fmap #-}
  a <$ _ = V4 a a a a
  {-# INLINE (<$) #-}

instance Foldable V4 where
  foldMap f (V4 a b c d) = f a <> f b <> f c <> f d
  {-# INLINE foldMap #-}
  null _ = False
  length _ = 4

instance Foldable1 V4 where
  foldMap1 f (V4 a b c d) = f a <> f b <> f c <> f d
  {-# INLINE foldMap1 #-}

instance Distributive V4 where
  distribute f = V4 (fmap (\(V4 x _ _ _) -> x) f) (fmap (\(V4 _ y _ _) -> y) f) (fmap (\(V4 _ _ z _) -> z) f) (fmap (\(V4 _ _ _ w) -> w) f)
  {-# INLINE distribute #-}

instance Representable V4 where
  type Rep V4 = I4
  tabulate f = V4 (f I41) (f I42) (f I43) (f I44)
  {-# INLINE tabulate #-}

  index (V4 x _ _ _) I41 = x
  index (V4 _ y _ _) I42 = y
  index (V4 _ _ z _) I43 = z
  index (V4 _ _ _ w) I44 = w
  {-# INLINE index #-}

data I4 = I41 | I42 | I43 | I44 deriving (Eq, Ord, Show)

instance Prd I4 where
  (<~) = (<=)
  (>~) = (>=)
  pcompare = pcompareOrd

instance Minimal I4 where
  minimal = I41

instance Maximal I4 where
  maximal = I44
