{-# LANGUAGE Safe                       #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Data.Semiring (
  -- * Constraint kinds
    type (-)
  -- ** Laws
  , PresemiringLaw
  , SemiringLaw
  , SemifieldLaw
  -- ** Ordered semirings
  , OrderedSemiring
  , NaturalSemiring
  , OrderedSemifield
  , PositiveSemifield
  -- * Semirings 
  -- ** Presemirings 
  , Presemiring(..)
  , (+), (*)
  , sum1, sumWith1
  , product1, productWith1
  -- ** Semirings 
  , Semiring(..)
  , zero, one
  , sum, sumWith
  , product, productWith
  -- ** Semifields
  , Semifield(..)
  , recip
  -- ** Endomorphism semirings
  , Endo2
  , appEndo2, endo2
  -- ** Distributive lattices
  , Dist(..)
  -- * Re-exports
  , type Natural
  , type Positive
  , Additive(..)
  , Multiplicative(..)
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Connection
import safe Data.Connection.Type
import safe Data.Either
import safe Data.Foldable as Foldable (Foldable)
import safe Data.Functor.Identity
import safe Data.Functor.Apply
import safe Data.Functor.Contravariant
import safe Data.Int
import safe Data.Maybe
import safe Data.Monoid hiding (Alt)
import safe Data.Order
import safe Data.Order.Total
import safe Data.Order.Interval
import safe Data.Lattice
import safe Data.Semigroup
import safe Data.Semigroup.Additive
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Word
import safe GHC.Generics
import safe GHC.Real (Ratio(..), Rational)
import safe Numeric.Natural
import safe Prelude
 ( Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..),
 (.), ($), Ordering(..), Integer, Float, Double)
import safe Data.Universe.Class (Finite(..))
--import safe qualified Data.Map as Map
--import safe qualified Data.Set as Set
import safe qualified Prelude as P


-------------------------------------------------------------------------------
-- Presemirings
-------------------------------------------------------------------------------

-- | Right pre-semirings. and (non-unital and unital) right semirings.
-- 
-- A right pre-semiring (sometimes referred to as a bisemigroup) is a type /R/ endowed 
-- with two associative binary (i.e. semigroup) operations: '+' and '*', along with a 
-- right-distributivity property connecting them:
--
-- /Distributivity/
--
-- @
-- (a '+' b) '*' c = (a '*' c) '+' (b '*' c)
-- @
--
-- Note that multiplication needn't be commutative.
--
class (PresemiringLaw a) => Presemiring a where

    -- | Reduce a free presemiring expression.
    -- 
    reduce1 :: (Foldable1 f, Functor f) => f (f a) -> a
    reduce1 = sum1 . fmap product1
    {-# INLINE reduce1 #-}

    -- | Cross-multiply two non-empty collections.
    --
    -- >>> cross1 (Right 2 :| [Left False]) (Right 2 :| [Right 3]) :: Either Bool Int
    -- Right 10
    --
    cross1 :: (Foldable1 f, Apply f) => f a -> f a -> a
    cross1 a b = sum1 $ liftF2 (*) a b
    {-# INLINE cross1 #-}

-------------------------------------------------------------------------------
-- Semirings
-------------------------------------------------------------------------------

-- | A semiring endowed with a preorder.
--
-- The preorder is said to be 'natural' when it is compatible with addition:
--
-- > x <~ y <=> x + c ~~ y
--
-- Semirings with this property are sometimes referred to as dioids.
--
type OrderedSemiring a = (Preorder a, Semiring a)

type NaturalSemiring a = (Connection a Natural, OrderedSemiring a)

-- | Right semirings.
-- 
-- A right semiring is a pre-semiring with two distinct neutral elements, 'zero' 
-- and 'one', such that 'zero' is right-neutral wrt addition, 'one' is right-neutral wrt
-- multiplication, and 'zero' is right-annihilative wrt multiplication. 
--
-- /Neutrality/
--
-- @
-- 'zero' '+' a = a
-- 'one' '*' a = a
-- @
--
-- /Absorbtion/
--
-- @
-- 'zero' '*' a = 'zero'
-- @
--
class (Presemiring a, SemiringLaw a) => Semiring a where

    -- | Reduce a free semiring expression.
    -- 
    -- @ (a11 * .. * a1m) + (a21 * .. * a2n) + ... @
    --
    -- >>> reduce [[1, 2], [3, 4 :: Int]] -- 1 * 2 + 3 * 4
    -- 14
    -- >>> reduce $ sequence [[1, 2], [3, 4 :: Int]] -- (1 + 2) * (3 + 4)
    -- 21
    -- >>> reduce . (fmap . fmap) Max $ [[1..4 :: Int], [0..2 :: Int]]
    -- Max {getMax = 24}
    --
    reduce :: (Foldable f, Functor f) => f (f a) -> a
    reduce = sum . fmap product
    {-# INLINE reduce #-}

    -- | Cross-multiply two collections.
    --
    -- >>> cross [1,2,3 :: Int] [1,2,3]
    -- 36
    -- >>> cross [1,2,3 :: Int] []
    -- 0
    --
    cross :: (Foldable f, Applicative f) => f a -> f a -> a
    cross a b = sum $ liftA2 (*) a b
    {-# INLINE cross #-}

    infixr 8 ^

    -- | Evaluate a natural-numbered power of a semiring element.
    --
    -- @ 'one' = a '^' 'zero' @
    --
    -- >>> 8 ^ zero :: Int
    -- 1
    --
    (^) :: a -> Word -> a
    x ^ n = getMul $ mreplicate (P.fromIntegral n) (Mul x)

-------------------------------------------------------------------------------
-- Semifields
-------------------------------------------------------------------------------

type OrderedSemifield a = (Preorder a, Semifield a)

type PositiveSemifield a = (Triple Positive a, Semifield a)

-- | A semifield, near-field, or division ring.
--
-- Instances needn't have commutative multiplication or additive inverses,
-- however addition must be commutative, and addition and multiplication must 
-- be associative and distribute as usual.
--
-- See also the wikipedia definitions of:
--
-- * < https://en.wikipedia.org/wiki/SemifieldLaw semifield >
-- * < https://en.wikipedia.org/wiki/Near-field_(mathematics) near-field >
-- * < https://en.wikipedia.org/wiki/Division_ring division ring >
-- 
class (Semiring a, SemifieldLaw a) => Semifield a where

    -- | The /NaN/ value of the semifield.
    --
    -- @ 'nan' = 'zero' '/' 'zero' @
    --
    nan :: a
    nan = zero / zero
    {-# INLINE nan #-}

    -- | The positive infinity of the semifield.
    --
    -- @ 'pinf' = 'one' '/' 'zero' @
    --
    pinf :: a
    pinf = one / zero
    {-# INLINE pinf #-}

    infixl 7 /

    -- | Right division by a multiplicative group element.
    --
    -- @ x '/' y = x '*' 'recip' y @
    --
    (/) :: a -> a -> a
    x / y = x * recip y
    {-# INLINE (/) #-}

    infixr 8 ^^

    -- | Integral power of a multiplicative group element.
    --
    -- @ 'one' = a '^^' 0 @
    --
    -- >>> 8 ^^ 0 :: Double
    -- 1.0
    --
    (^^) :: a -> Int -> a
    a ^^ n = getMul $ pow (Mul a) n

---------------------------------------------------------------------
-- Endo2
---------------------------------------------------------------------

-- | A free semiring.
--
-- The final (i.e. Boehm-Berarducci) encoding of an arbitrary semiring is:
--
-- > forall a. (a -> a) -> a -> a
--
type Endo2 a = Endo (Endo a)

endo2 :: Semiring a => a -> Endo2 a
endo2 a = Endo $ \(Endo f) -> Endo (\y -> a * f zero + y)

-- | Evaluate a free semiring expression.
--
-- >>> appEndo2 $ (one + one) * (one + (endo2 3.4)) :: Double
-- 8.8
--
appEndo2 :: Semiring a => Endo2 a -> a
appEndo2 (Endo f) = appEndo (f $ Endo (one +)) zero

---------------------------------------------------------------------
-- Dist
---------------------------------------------------------------------

-- | Distributive lattices.
--
-- Distributive lattices are lattices satisfying the semiring distributivity laws: 
--
-- @ 
-- x '/\' (y '\/' z) = x '/\' y '\/' x '/\' z
-- x '\/' (y '/\' z) = (x '\/' y) '/\' (x '\/' z)
-- @
--
newtype Dist a = Dist { getDist :: a }
  deriving stock (Eq, Generic, Ord, Show)
  deriving (Functor, Applicative) via Identity

deriving via (F1 Additive (Join a)) instance Lattice a => Semigroup (Additive (Dist a))
deriving via (F1 Multiplicative (Meet a)) instance Lattice a => Semigroup (Multiplicative (Dist a))
deriving via (F1 Additive (Join a)) instance Bounded a => Monoid (Additive (Dist a))
deriving via (F1 Multiplicative (Meet a)) instance Bounded a => Monoid (Multiplicative (Dist a))

instance Lattice a => Presemiring (Dist a)
instance Bounded a => Semiring (Dist a)

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Presemiring ()
instance Semiring ()
instance Semifield ()

instance Presemiring Bool
instance Semiring Bool

instance Presemiring Ordering
instance Semiring Ordering

instance Presemiring Word8
instance Semiring Word8

instance Presemiring Word16
instance Semiring Word16

instance Presemiring Word32
instance Semiring Word32

instance Presemiring Word64
instance Semiring Word64

instance Presemiring Word
instance Semiring Word

instance Presemiring Natural
instance Semiring Natural

instance Presemiring Int8
instance Semiring Int8

instance Presemiring Int16
instance Semiring Int16

instance Presemiring Int32
instance Semiring Int32

instance Presemiring Int64
instance Semiring Int64

instance Presemiring Int
instance Semiring Int

instance Presemiring Integer
instance Semiring Integer

{-
instance Presemiring Uni
instance Semiring Uni
instance Semifield Uni

instance Presemiring Deci
instance Semiring Deci
instance Semifield Deci

instance Presemiring Centi
instance Semiring Centi
instance Semifield Centi

instance Presemiring Milli
instance Semiring Milli
instance Semifield Milli

instance Presemiring Micro
instance Semiring Micro
instance Semifield Micro

instance Presemiring Nano
instance Semiring Nano
instance Semifield Nano

instance Presemiring Pico
instance Semiring Pico
instance Semifield Pico

-}

instance Presemiring Float
instance Semiring Float
instance Semifield Float

instance Presemiring Double
instance Semiring Double
instance Semifield Double

instance Presemiring Rational
instance Semiring Rational
instance Semifield Rational

instance Presemiring Positive
instance Semiring Positive
instance Semifield Positive

instance RingLaw a => Presemiring (Complex a)
instance RingLaw a => Semiring (Complex a)
instance FieldLaw a => Semifield (Complex a)

instance Presemiring a => Presemiring (Identity a) 
instance Semiring a => Semiring (Identity a) 
instance Semifield a => Semifield (Identity a) 

instance Presemiring a => Presemiring (Dual a)
instance Semiring a => Semiring (Dual a)

instance Presemiring a => Presemiring (Down a)
instance Semiring a => Semiring (Down a)

instance (TotalOrder a, Semigroup (Additive a)) => Presemiring (Min a)
instance (TotalOrder a, Monoid (Additive a), P.Bounded a) => Semiring (Min a)

instance (TotalOrder a, Semigroup (Multiplicative a)) => Presemiring (Max a)
instance (TotalOrder a, Monoid (Multiplicative a), P.Bounded a) => Semiring (Max a)

instance (Semigroup (Join a), Semigroup (Additive a)) => Presemiring (Join a)
instance (Semigroup (Meet a), Semigroup (Multiplicative a)) => Presemiring (Meet a)
instance (Monoid (Join a), Monoid (Additive a)) => Semiring (Join a)
instance (Monoid (Meet a), Monoid (Multiplicative a)) => Semiring (Meet a)

instance (Lattice a, Semigroup (Additive a)) => Presemiring (Interval a)
instance (Lattice a, Monoid (Additive a)) => Semiring (Interval a)

instance Semigroup a => Presemiring (Endo a)
instance Monoid a => Semiring (Endo a)

instance Presemiring b => Presemiring (a -> b)
instance Semiring b => Semiring (a -> b)

instance Presemiring b => Presemiring (Op b a)
instance Semiring b => Semiring (Op b a)

instance Presemiring (Predicate a)
instance Semiring (Predicate a)

instance Presemiring a => Presemiring (Maybe a)
instance Semiring a => Semiring (Maybe a)

instance (Presemiring e, Presemiring a) => Presemiring (Either e a)
instance (Semiring e, Semiring a) => Semiring (Either e a)

instance Semiring a => Presemiring [a]
instance Semiring a => Semiring [a]

--instance (TotalOrder k, Semigroup (Additive k), Presemiring a) => Presemiring (Map k a)
--instance (TotalOrder k, Monoid (Additive k), Semiring a) => Semiring (Map k a)

instance (Presemiring a, Presemiring b) => Presemiring (a, b)
instance (Semiring a, Semiring b) => Semiring (a, b)

instance (Presemiring a, Presemiring b, Presemiring c) => Presemiring (a, b, c)
instance (Semiring a, Semiring b, Semiring c) => Semiring (a, b, c)


{-
--type Poly1 a = Map Natural a
--type Poly2 a = Map (Natural, Natural) a


type Arr b = [[b]]

ident :: Arr Double
ident = [[1]]

--boxBlur :: Int -> Arr Double
--boxBlur n = (fmap.fmap) (/ fromIntegral (n*n)) ((replicate n . replicate n) 1)

sharpen :: Arr Double
sharpen = [[ 0,-1, 0]
          ,[-1, 5,-1]
          ,[ 0,-1, 0]]

edge :: Arr Double
edge = [[-1,-1,-1]
       ,[-1, 8,-1]
       ,[-1,-1,-1]]

-}



{-

--deriving via (A1 Maybe a) instance PresemiringLaw a => PresemiringLaw (Maybe a) 

deriving via (Ap (f**g) a) instance (Applicative f, Applicative g, PresemiringLaw a) => PresemiringLaw ((f**g) a) 
deriving via (Ap (f**g) a) instance (Applicative f, Applicative g, SemiringLaw a) => SemiringLaw ((f**g) a) 

deriving via (Ap (f++g) a) instance (Applicative f, Applicative g, PresemiringLaw a) => PresemiringLaw ((f++g) a) 
-- the component-wise multiplication semiring. use the semimodule instances and .#. for matrix mult.
deriving via (Ap (f++g) a) instance (Applicative f, Applicative g, SemiringLaw a) => SemiringLaw ((f++g) a) 


deriving via (Ap ((->)a) b) instance PresemiringLaw b => PresemiringLaw (a -> b)

--deriving via (A1 [] a) instance PresemiringLaw a => PresemiringLaw [a] 
deriving via (A1 Seq a) instance PresemiringLaw a => PresemiringLaw (Seq a) 

deriving via (A1 (Either e) a) instance PresemiringLaw a => PresemiringLaw (Either e a)

deriving via (A1 NonEmpty a) instance PresemiringLaw a => PresemiringLaw (NonEmpty a) 
--deriving via (A1 (Map k) a) instance (TotalOrder k, PresemiringLaw a) => PresemiringLaw (Map k a) 
deriving via (A1 IntMap a) instance PresemiringLaw a => PresemiringLaw (IntMap a) 
--deriving via (A1 (Lift f) a) instance (Alt f, Semigroup a) => PresemiringLaw (Lift f a) 

-}
