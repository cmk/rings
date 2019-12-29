{-# LANGUAGE CPP #-}
module Data.Word.Instance where

import Data.Connection
import Data.Connection.Word
import Data.Dioid
import Data.Prd
import Data.Semiring
import Data.Word
import Numeric.Natural
import Prelude (id, Monoid(..), Semigroup(..))
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

instance Dioid Word8 where
  fromNatural = connr w08nat

instance Dioid Word16 where
  fromNatural = connr w16nat

instance Dioid Word32 where
  fromNatural = connr w32nat

instance Dioid Word64 where
  fromNatural = connr w64nat

instance Dioid Natural where
  fromNatural = id
