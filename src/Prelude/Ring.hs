{-# LANGUAGE RebindableSyntax #-}
module Prelude.Ring
  ( -- * Primitive types
    -- ** Bool
    Bool (..),
    bool,
    (&&),
    (||),
    not,
    otherwise,
    ifThenElse,
    -- ** Int
    Int8,
    Int16,
    Int32,
    Int64,
    Int,
    Integer,
    -- ** Word
    Word8,
    Word16,
    Word32,
    Word64,
    Word,
    Natural,
    -- ** Rational
    Ratio(..),
    type Rational,
    type Positive,
    -- ** Floating
    Float, Double,

    -- * Algebraic datatypes
    -- ** Maybe
    Maybe (..),
    fromMaybe,
    maybe,
    -- ** Either
    Either (..),
    either,
    -- ** Tuple
    fst,
    snd,
    curry,
    uncurry,

  -- * Orders
    Ordering(..),
  -- ** Preorders
    Preorder(..),
    pcomparing,
  -- ** Partial orders
    Eq (),
    PartialOrder,
    (==),(/=),
    (<=),(>=),
  -- ** Total orders
    Ord (),
    TotalOrder,
    min, max,
    compare,
    comparing,
  -- ** Connections
    left,
    right,
    Connection(..),
  -- ** Rounding
    Mode(..),
    embed,
    round,
    floor,
    ceiling,
    truncate,
    roundWith,
    roundWith1,
    roundWith2,
    roundWith3,
    Triple(..),
  -- ** TripFloat
    TripFloat,
    embed32,
    round32,
    floor32,
    ceiling32,
    truncate32,
  -- ** TripDouble
    TripDouble,
    embed64,
    round64,
    floor64,
    ceiling64,
    truncate64,

  -- * Rings
    type (-),
  -- ** Presemirings 
    (+), (*),
    sum1, sumWith1,
    product1, productWith1,
    Presemiring(..),
  -- ** Semirings 
    zero, one,
    sum, sumWith,
    product, productWith,
    Semiring(..),
    OrderedSemiring,
    NaturalSemiring,
  -- ** Rings
    negate,
    fromInteger,
    Ring(..),
    OrderedRing,
    IntegerRing,
  -- ** Semifields
    recip,
    Semifield(..),
    OrderedSemifield,
    PositiveSemifield,
  -- ** Fields
    fromRational, pi,
    Field(..),
    OrderedField,
    RationalField,

  -- * Semigroups
    Semigroup(..),
    Monoid(..),
    Group(..),
    Additive(..),
    Multiplicative(..),
  ) where

import Data.Connection
import Data.Connection.Round
import Data.Order
import Data.Order.Total
import Data.Semiring
import Data.Ring
import Data.Ring.Syntax

import Data.Bool ((&&), Bool (..), bool, not, otherwise, (||))
import Data.Either (Either (..), either)
import Data.Group (Group(..))
import Data.Int (Int, Int16, Int32, Int64, Int8)
import Data.Maybe (Maybe (..), fromMaybe, maybe)
import Data.Monoid (Monoid (..))
import Data.Semigroup (Semigroup (..))
import Data.Tuple (curry, fst, snd, uncurry)
import Data.Word (Word, Word16, Word32, Word64, Word8)
import GHC.Real (Ratio(..))
import Numeric.Natural (Natural)

import Prelude (Rational, Double, Float, Integer)

pi :: RationalField a => a
pi = 3.141592653589793238

-- Used in conjunction with RebindableSyntax.
ifThenElse :: Bool -> a -> a -> a
ifThenElse b x y = bool y x b
{-# INLINE ifThenElse #-}
