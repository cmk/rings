{-# LANGUAGE CPP #-}
module Data.Fixed.Instance where

import Data.Fixed
import Data.Semiring
import Data.Group
import Data.Ring
import Prelude (Monoid(..), Semigroup(..))
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
   fromInteger = N.fromInteger     \
;  abs = N.abs                     \
;  signum = N.signum               \
;  {-# INLINE abs #-}              \
;  {-# INLINE signum #-}           \
}

deriveSemigroup(Uni)
deriveSemigroup(Deci)
deriveSemigroup(Centi)
deriveSemigroup(Milli)
deriveSemigroup(Micro)
deriveSemigroup(Nano)
deriveSemigroup(Pico)

deriveMonoid(Uni)
deriveMonoid(Deci)
deriveMonoid(Centi)
deriveMonoid(Milli)
deriveMonoid(Micro)
deriveMonoid(Nano)
deriveMonoid(Pico)

deriveGroup(Uni)
deriveGroup(Deci)
deriveGroup(Centi)
deriveGroup(Milli)
deriveGroup(Micro)
deriveGroup(Nano)
deriveGroup(Pico)

deriveSemiring(Uni)
deriveSemiring(Deci)
deriveSemiring(Centi)
deriveSemiring(Milli)
deriveSemiring(Micro)
deriveSemiring(Nano)
deriveSemiring(Pico)

deriveRing(Uni)
deriveRing(Deci)
deriveRing(Centi)
deriveRing(Milli)
deriveRing(Micro)
deriveRing(Nano)
deriveRing(Pico)
