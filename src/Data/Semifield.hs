{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}

module Data.Semifield where

import safe Data.Bool
import safe Data.Complex
import safe Data.Fixed
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Group
import safe Data.Int
import safe Data.Magma
--import safe Data.Semiring
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative 
import safe Data.Tuple
import safe Data.Word
import safe GHC.Real hiding (Fractional(..), (^^), (^))
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))

import Prelude ( Eq(..), Ord(..), Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, fromInteger, Float, Double)
import qualified Prelude as P

import GHC.Generics (Generic)


-- Sometimes called a division ring
type Semifield a = ((Additive-Monoid) a, (Multiplicative-Group) a)

type Field a = ((Additive-Group) a, (Multiplicative-Group) a)


--class Semiring a => Involutive a where adjoint :: a -> a

--type InvolutiveSemiring a = (Involutive a, Semiring a)

--type AdditiveIdempotentSemiring a = ((Additive-Idempotent) a, Semiring a)

infixr 8 ^^

-- @ 'one' == a '^^' 0 @
--
-- >>> 8 ^^ 0 :: Double
-- 1.0
-- >>> 8 ^^ 0 :: Pico
-- 1.000000000000
--
(^^) :: (Multiplicative-Group) a => a -> Integer -> a
a ^^ n = unMultiplicative $ greplicate n (Multiplicative a)



{-
infixl 7 //

-- | A semifield, near-field, division ring, or associative division algebra.
--
-- Instances needn't be commutative, nor need they possess 'Monoid' or 'Group' instances.
--
-- They need only be right-associative pre-semirings.
--
-- See also the wikipedia definitions of < https://en.wikipedia.org/wiki/Semifield semifield >, < https://en.wikipedia.org/wiki/Near-field_(mathematics) near-field >, < https://en.wikipedia.org/wiki/Division_ring division ring >, and < https://en.wikipedia.org/wiki/Division_algebra division algebra >.
-- 
class Semiring a => Semifield a where
  {-# MINIMAL (//) #-}

  (//) :: a -> a -> a
  default (//) :: Monoid a => a -> a -> a
  x // y = x >< recip y

  recip :: Monoid a => a -> a
  recip x = sunit // x
 
  -- | A semifield homomorphism from 'Rational' to /a/.
  fromRational :: Ring a => Rational -> a
  fromRational (x :% y) = fromInteger x // fromInteger y
 
  -- | A semifield homomorphism from 'Positive' to /a/.
  --
  -- The only legal instance providing both 'fromPositive' and 'fromRational' is '()'.
  -- This is due to the well-known theorem in semigroup theory that a non-trivial monoid 
  -- cannot be both canonically ordered (not just pre-ordered) and also have reciperses
  -- (i.e. be a group).
  --
  fromPositive :: Dioid a => Positive -> a
  fromPositive (x :% y) = fromNatural x // fromNatural y

instance Semifield () where
  () // () = ()
  fromRational _ = ()
  fromPositive _ = ()

instance Semifield Rational where
  x1 :% y1 // x2 :% y2 = (x1><y2) :% (y1><x2)

  recip (x :% y) = y :% x 

  fromRational = id

instance Semifield Positive where
  x1 :% y1 // x2 :% y2 = (x1><y2) :% (y1><x2)

  recip (x :% y) = y :% x 

  fromPositive = id

instance Field a => Semifield (Complex a) where
  (a :+ b) // (c :+ d) = ((a><c <> b><d) // (c><c <> d><d)) :+ ((b><c << a><d) // (c><c <> d><d))

#define deriveSemifield(ty)        \
instance Semifield (ty) where {    \
   fromRational = N.fromRational   \
;  (//) = (N./)                    \
;  recip = N.recip                   \
}

deriveSemifield(Uni)
deriveSemifield(Deci)
deriveSemifield(Centi)
deriveSemifield(Milli)
deriveSemifield(Micro)
deriveSemifield(Nano)
deriveSemifield(Pico)
-}
