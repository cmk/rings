-- | Orphan instances from base.
module Data.Semigroup.Orphan where

import Control.Applicative
import Data.Complex
import Data.Functor.Alt
import Data.Functor.Plus
import Numeric.Natural (Natural)


instance Semigroup Word where (<>) = (+)

instance Monoid Word where mempty = 0

instance Semigroup Int where (<>) = (+)

instance Monoid Int where mempty = 0

instance Semigroup Bool where (<>) = (||)

instance Monoid Bool where mempty = False

instance Semigroup Float where (<>) = (+)

instance Monoid Float where mempty = 0

instance Semigroup a => Semigroup (Complex a) where
  (x :+ y) <> (x' :+ y') = (x <> x') :+ (y <> y')

instance Monoid a => Monoid (Complex a) where
  mempty = mempty :+ mempty

instance Semigroup Natural where (<>) = (+)

instance Monoid Natural where mempty = 0


