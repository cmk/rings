module Data.Complex.Instance where

import Data.Complex
import Data.Semiring
import Data.Group
import Data.Ring

import Prelude hiding (negate, fromInteger)

instance Semigroup a => Semigroup (Complex a) where
  (x :+ y) <> (x' :+ y') = (x <> x') :+ (y <> y')
  {-# INLINE (<>) #-}

instance Monoid a => Monoid (Complex a) where
  mempty = mempty :+ mempty

instance Group a => Group (Complex a) where
  negate (x :+ y) = negate x :+ negate y
  {-# INLINE negate #-}

instance (Group a, Semiring a) => Semiring (Complex a) where
  (x :+ y) >< (x' :+ y') = (x >< x' << y >< y') :+ (x >< y' <> y >< x')
  {-# INLINE (><) #-}

  fromBoolean False = mempty
  fromBoolean True = fromBoolean True :+ mempty
  {-# INLINE fromBoolean #-}

instance Ring a => Ring (Complex a) where
  fromInteger x = fromInteger x :+ mempty
  {-# INLINE fromInteger #-}
