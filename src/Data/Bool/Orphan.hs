-- | Orphan instances from base.
module Data.Bool.Orphan where

import Data.Prd
import Data.Dioid
import Data.Semiring
import Prelude

instance Semigroup Bool where
  (<>) = (||)
  {-# INLINE (<>) #-}

instance Monoid Bool where mempty = False

instance Semiring Bool where
  (><) = (&&)
  {-# INLINE (><) #-}

  fromBoolean = id
  {-# INLINE fromBoolean #-}

instance Kleene Bool where
  star = const True -- == (|| True)
  plus = id -- == (&& True)
  {-# INLINE star #-}
  {-# INLINE plus #-}

instance Dioid Bool where
