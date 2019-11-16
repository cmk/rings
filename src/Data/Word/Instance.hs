{-# LANGUAGE CPP #-}
module Data.Word.Instance where

import Data.Dioid
import Data.Prd
import Data.Semiring
import Data.Word
import Numeric.Natural
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

#define deriveSemiring(ty)         \
instance Semiring (ty) where {     \
   (><) = (N.*)                    \
;  fromBoolean = fromBooleanDef 1  \
;  {-# INLINE (><) #-}             \
;  {-# INLINE fromBoolean #-}      \
}

#define deriveDioid(ty)             \
instance Dioid (ty) where {         \
}

deriveSemigroup(Word)
deriveSemigroup(Word8)
deriveSemigroup(Word16)
deriveSemigroup(Word32)
deriveSemigroup(Word64)
deriveSemigroup(Natural)

deriveMonoid(Word)
deriveMonoid(Word8)
deriveMonoid(Word16)
deriveMonoid(Word32)
deriveMonoid(Word64)
deriveMonoid(Natural)

deriveSemiring(Word)
deriveSemiring(Word8)
deriveSemiring(Word16)
deriveSemiring(Word32)
deriveSemiring(Word64)
deriveSemiring(Natural)

deriveDioid(Word)
deriveDioid(Word8)
deriveDioid(Word16)
deriveDioid(Word32)
deriveDioid(Word64)
deriveDioid(Natural)
