{-# LANGUAGE CPP #-}
module Data.Double.Instance where

import Data.Semiring
import Foreign.C.Types (CDouble(..))
import Prelude (Monoid(..), Semigroup(..), Double)
import qualified Prelude as N (Num(..))

#define deriveSemigroup(ty)        \
instance Semigroup (ty) where {    \
   (<>) = (N.+)                    \
;  {-# INLINE (<>) #-}             \
}

#define deriveMonoid(ty)           \
instance Monoid (ty) where {       \
   mempty = 0                      \
}
#define deriveSemiring(ty)         \
instance Semiring (ty) where {     \
   (><) = (N.*)                    \
;  fromBoolean = fromBooleanDef 1  \
;  {-# INLINE (><) #-}             \
;  {-# INLINE fromBoolean #-}      \
}

deriveSemigroup(Double)
deriveSemigroup(CDouble)
deriveMonoid(Double)
deriveMonoid(CDouble)
deriveSemiring(Double)
deriveSemiring(CDouble)
