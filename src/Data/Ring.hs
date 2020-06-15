{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}
{-# Language DeriveFunctor       #-}
{-# Language DeriveGeneric       #-}
{-# Language DerivingVia         #-}
{-# Language StandaloneDeriving  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Ring (
  -- * Constraint kinds
    type (-)
  -- ** Laws
  , RingLaw
  , FieldLaw
  -- ** Ordered rings
  , OrderedRing
  , IntegerRing
  , OrderedField
  , RationalField
  -- * Rings
  -- ** Rings
  , Ring(..)
  , negate
  -- ** Fields
  , Field(..)
  -- * Re-exports
  , type Integer
  , type Rational
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Connection
import safe Data.Connection.Type
import safe Data.Foldable as Foldable (foldl',foldr')
import safe Data.Functor.Identity
import safe Data.Int
import safe Data.Maybe
import safe Data.Lattice
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Semiring
import safe Data.Semigroup.Additive
import safe GHC.Real (Rational)
import safe Prelude
 ( Eq(..), Ord, Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..)
 , id, flip, const, (.), ($), Integer, Float, Double, Ordering(..) )


-------------------------------------------------------------------------------
-- Rings
-------------------------------------------------------------------------------

type OrderedRing a = (TotalOrder a, Ring a)

-- | An ordered ring equipped with a Galois connection from the Integers.
type IntegerRing a = (Connection a (Lifted Integer), OrderedRing a)

-- | A < https://en.wikipedia.org/wiki/Ring_(mathematics) ring >.
--
-- A ring /R/ is a commutative group with a second monoidal operation '*' that distributes over '+'.
--
-- The basic properties of a ring follow immediately from the axioms:
-- 
-- @ r '*' 'zero' = 'zero' = 'zero' '*' r @
--
-- @ 'negate' 'one' '*' r = 'negate' r @
--
-- Furthermore, the binomial formula holds for any commuting pair of elements (that is, any /a/ and /b/ such that /a * b = b * a/).
--
-- If /zero = one/ in a ring /R/, then /R/ has only one element, and is called the zero ring.
-- Otherwise the additive identity, the additive inverse of each element, and the multiplicative identity are unique.
--
-- If the ring is < https://en.wikipedia.org/wiki/Ordered_ring ordered > (i.e. has an 'Ord' instance), then the following additional properties must hold:
--
-- @ a '<~' b ⇒ a '+' c '<~' b '+' c @
--
-- @ 'zero' '<~' a '&&' 'zero' '<~' b ⇒ 'zero' '<~' a '*' b @
--
class (Semiring a, RingLaw a) => Ring a where

    infixl 6 -

    -- | Subtract two elements.
    --
    -- @
    -- a '-' b = a + 'negate' b 
    -- @
    --
    (-) :: a -> a -> a
    a - b = a + negate b
    {-# INLINE (-) #-}
   
    -- | Absolute value of an element.
    --
    -- @ 'abs' x = x '*' 'signum' x @
    --
    abs :: TotalOrder a => a -> a
    abs x = x * signum x
    {-# INLINE abs #-}

    -- | Extract the sign of an element.
    --
    -- 'signum' satisfies a trichotomy law:
    --
    -- @ 'signum' r = 'negate' 'one' || 'zero' || 'one' @
    -- 
    -- This follows from the fact that ordered rings are abelian, linearly 
    -- ordered groups with respect to addition.
    --
    -- See < https://en.wikipedia.org/wiki/Linearly_ordered_group >.
    --
    signum :: TotalOrder a => a -> a
    signum x = bool (negate one) one $ zero <~ x
    {-# INLINE signum #-}

-------------------------------------------------------------------------------
-- Fields
-------------------------------------------------------------------------------

-- | An < https://en.wikipedia.org/wiki/Ordered_field ordered field >.
type OrderedField a = (TotalOrder a, Field a)

-- | A field equipped with a triple adjunction from the rationals.
type RationalField a = (Triple Rational a, Field a)
--type RationalField a = (Triple Rational a, OrderedField a)

-- | A < https://en.wikipedia.org/wiki/Field_(mathematics) field >.
--
class (Ring a, Semifield a, FieldLaw a) => Field a where

    -- | The negative infinity of the field.
    --
    -- @ 'ninf' = 'negate' 'one' '/' 'zero' @
    --
    ninf :: a
    ninf = negate one / zero
    {-# INLINE ninf #-}


{-
deriving via (Ap ((->)a) b) instance Ring b => Ring (a -> b)
deriving via (Ap Dual a) instance Ring a => Ring (Dual a)
-- the component-wise multiplication semiring. use the semimodule instances and .#. for matrix mult.
deriving via (Ap (f**g) a) instance (Applicative f, Applicative g, Ring a) => Ring ((f**g) a) 
deriving via (Ap (f++g) a) instance (Applicative f, Applicative g, Ring a) => Ring ((f++g) a) 

instance Ring a => Ring (Op a b) where
  Op f - Op g = Op $ \b -> f b - g b
  {-# INLINE (-) #-}

instance (Ring a, Ring b) => Ring (a, b) where
  (x1,y1) - (x2,y2) = (x1-x2, y1-y2)

instance (Ring a, Ring b, Ring c) => Ring (a, b, c) where
  (x1,y1,z1) - (x2,y2,z2) = (x1-x2, y1-y2, z1-z2)

-}

instance Ring ()
instance Field ()

instance Ring Int
instance Ring Int8
instance Ring Int16
instance Ring Int32
instance Ring Int64
instance Ring Integer

{-
instance Ring Uni
instance Ring Deci
instance Ring Centi
instance Ring Milli
instance Ring Micro
instance Ring Nano
instance Ring Pico
instance Field Uni
instance Field Deci
instance Field Centi
instance Field Milli
instance Field Micro
instance Field Nano
instance Field Pico
-}

instance Ring Float
instance Field Float

instance Ring Double
instance Field Double

instance Ring Rational
instance Field Rational

instance Ring a => Ring (Identity a) 
instance Field a => Field (Identity a) 
instance Ring a => Ring (Complex a)
instance Field a => Field (Complex a)
