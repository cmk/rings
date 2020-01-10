{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE Safe #-}

module Data.Module.V3  (
    V3(..)
  , triple
  , I3(..)
) where

import safe Data.Dioid
import safe Data.Distributive
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Functor.Rep
import safe Data.Group
import safe Data.Module
import safe Data.Prd
import safe Data.Ring
import safe Data.Semigroup.Foldable as Foldable1

import safe Prelude hiding (negate)

data V3 a = V3 !a !a !a deriving (Eq,Ord,Show)

-- | Scalar triple product.
--
triple :: Ring a => V3 a -> V3 a -> V3 a -> a
triple a b c = a <.> b <@> c
{-# INLINE triple #-}

instance Prd a => Prd (V3 a) where
  V3 a b c <~ V3 d e f = a <~ d && b <~ e && c <~ f

instance Semigroup a => Semigroup (V3 a) where
  (<>) = mzipWithRep (<>)

instance Monoid a => Monoid (V3 a) where
  mempty = pureRep mempty

instance Unital a => Semiring (V3 a) where
  (><) = mzipWithRep (><)
  fromBoolean = pureRep . fromBoolean

instance (Monoid a, Dioid a) => Dioid (V3 a) where
  fromNatural = pureRep . fromNatural

instance Group a => Group (V3 a) where
  (<<) = mzipWithRep (<<)

instance Semiring a => Semimodule a (V3 a) where
  a .# f = (a ><) <$> f

instance Functor V3 where
  fmap f (V3 a b c) = V3 (f a) (f b) (f c)
  {-# INLINE fmap #-}
  a <$ _ = V3 a a a
  {-# INLINE (<$) #-}

instance Foldable V3 where
  foldMap f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap #-}
  null _ = False
  length _ = 3

instance Foldable1 V3 where
  foldMap1 f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap1 #-}

instance Distributive V3 where
  distribute f = V3 (fmap (\(V3 x _ _) -> x) f) (fmap (\(V3 _ y _) -> y) f) (fmap (\(V3 _ _ z) -> z) f)
  {-# INLINE distribute #-}

instance Representable V3 where
  type Rep V3 = I3
  tabulate f = V3 (f I31) (f I32) (f I33)
  {-# INLINE tabulate #-}

  index (V3 x _ _) I31 = x
  index (V3 _ y _) I32 = y
  index (V3 _ _ z) I33 = z
  {-# INLINE index #-}
