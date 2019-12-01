{-# LANGUAGE CPP #-}
module Data.Float.Instance where

import Data.Semiring
import Foreign.C.Types (CFloat(..))
import Prelude (Monoid(..), Semigroup(..), Float)
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

deriveSemigroup(Float)
deriveSemigroup(CFloat)
deriveMonoid(Float)
deriveMonoid(CFloat)
deriveSemiring(Float)
deriveSemiring(CFloat)
