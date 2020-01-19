{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Semimodule.V3 where

import safe Data.Algebra
import safe Data.Distributive
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Functor.Rep
import safe Data.Magma
import safe Data.Group
import safe Data.Semimodule
--import safe Data.Prd hiding (zero)
import safe Data.Semiring
import safe Data.Semigroup.Foldable as Foldable1


import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe qualified Prelude as P


-- | Scalar triple product.
--
triple :: Ring a => V3 a -> V3 a -> V3 a -> a
triple a b c = a .*. b >< c
{-# INLINE triple #-}

data V3 a = V3 !a !a !a deriving (Eq,Ord,Show)

instance (Additive-Semigroup) a => Semigroup (V3 a) where
  (<>) = mzipWithRep add

instance (Additive-Monoid) a => Monoid (V3 a) where
  mempty = pureRep zero

instance (Additive-Group) a => Magma (V3 a) where
  (<<) = mzipWithRep sub

instance (Additive-Group) a => Quasigroup (V3 a)

instance (Additive-Group) a => Loop (V3 a)

instance (Additive-Group) a => Group (V3 a)

instance Semiring a => Semimodule a (V3 a) where 
  a *. f = (a *) <$> f

instance Functor V3 where
  fmap f (V3 a b c) = V3 (f a) (f b) (f c)
  {-# INLINE fmap #-}
  a <$ _ = V3 a a a
  {-# INLINE (<$) #-}

instance Foldable V3 where
  foldMap f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap #-}
  null _ = False
  --length _ = 3

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


-------------------------------------------------------------------------------
-- I3
-------------------------------------------------------------------------------

data I3 = I31 | I32 | I33 deriving (Eq, Ord, Show)

instance Ring r => Algebra r I3 where
  multiplyWith f = f' where
    i31 = f I32 I33 - f I33 I32
    i32 = f I33 I31 - f I31 I33
    i33 = f I31 I32 - f I32 I31 
    f' I31 = i31
    f' I32 = i32
    f' I33 = i33

type QuaternionBasis = Maybe I3

instance Ring r => Algebra r QuaternionBasis where
  multiplyWith f = maybe fe f' where
    e = Nothing
    i = Just I31
    j = Just I32
    k = Just I33
    fe = f e e - (f i i + f j j + f k k)
    fi = f e i + f i e + (f j k - f k j)
    fj = f e j + f j e + (f k i - f i k)
    fk = f e k + f k e + (f i j - f j i)
    f' I31 = fi
    f' I32 = fj
    f' I33 = fk

instance Ring r => Unital r QuaternionBasis where
  unitWith x Nothing = x 
  unitWith _ _ = zero

instance Ring r => Composition r QuaternionBasis where
  conjugateWith f = maybe fe f' where
    fe = f Nothing
    f' I31 = negate . f $ Just I31
    f' I32 = negate . f $ Just I32
    f' I33 = negate . f $ Just I33
