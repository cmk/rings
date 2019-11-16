{-# LANGUAGE CPP #-}
module Data.Int.Instance where

import Data.Semiring
import Data.Group
import Data.Ring
import Data.Int
import Prelude (Monoid(..), Semigroup(..), Integer)
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

#define deriveGroup(ty)            \
instance Group (ty) where {        \
   (<<) = (N.-)                    \
;  negate = N.negate               \
;  {-# INLINE (<<) #-}             \
;  {-# INLINE negate #-}           \
}

#define deriveSemiring(ty)         \
instance Semiring (ty) where {     \
   (><) = (N.*)                    \
;  fromBoolean = fromBooleanDef 1  \
;  {-# INLINE (><) #-}             \
;  {-# INLINE fromBoolean #-}      \
}

#define deriveRing(ty)             \
instance Ring (ty) where {         \
   abs = N.abs                     \
;  signum = N.signum               \
;  {-# INLINE abs #-}              \
;  {-# INLINE signum #-}           \
}

deriveSemigroup(Int)
deriveSemigroup(Int8)
deriveSemigroup(Int16)
deriveSemigroup(Int32)
deriveSemigroup(Int64)
deriveSemigroup(Integer)

deriveMonoid(Int)
deriveMonoid(Int8)
deriveMonoid(Int16)
deriveMonoid(Int32)
deriveMonoid(Int64)
deriveMonoid(Integer)

deriveGroup(Int)
deriveGroup(Int8)
deriveGroup(Int16)
deriveGroup(Int32)
deriveGroup(Int64)
deriveGroup(Integer)

deriveSemiring(Int)
deriveSemiring(Int8)
deriveSemiring(Int16)
deriveSemiring(Int32)
deriveSemiring(Int64)
deriveSemiring(Integer)

deriveRing(Int)
deriveRing(Int8)
deriveRing(Int16)
deriveRing(Int32)
deriveRing(Int64)
deriveRing(Integer)
