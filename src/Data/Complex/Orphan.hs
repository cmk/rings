-- | Orphan instances from base.
module Data.Complex.Orphan where

import Data.Complex
import Prelude

instance Semigroup a => Semigroup (Complex a) where
  (x :+ y) <> (x' :+ y') = (x <> x') :+ (y <> y')
  {-# INLINE (<>) #-}

instance Monoid a => Monoid (Complex a) where
  mempty = mempty :+ mempty
