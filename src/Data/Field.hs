{-# LANGUAGE CPP #-}
{-# Language ConstrainedClassMethods #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
module Data.Field where

import safe Data.Complex
import safe Data.Dioid
import safe Data.Fixed
import safe Data.Group
import safe Data.Ring
import safe Data.Ring
import safe Numeric.Natural

import safe GHC.Real hiding (Fractional(..))
import safe Prelude hiding (Num(..), Fractional(..))
import safe qualified Prelude as N


-- Convenience constraint representing a field.
-- Note this ignores the many classes between ring and field and may change at a later date.
--
type Field a = (Ring a, Semifield a)


{-
(i) a <> b = mempty ==> a == mempty && b == mempty
(ii) a >< b = mempty ==> a == mempty || b == mempty

every dioid satisfies (i).
Show that a dioid which is a group for the second law is a positive dioid. Positive
semirings (and consequently positive dioids) are often referred to as semi-fields

  --Just $ recip a = star <$> mon one a --default for Dioid instances if one-a exists?
-}



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
