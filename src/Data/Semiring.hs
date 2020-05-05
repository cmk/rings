{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE StandaloneDeriving         #-}

{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Data.Semiring (
  -- * Types
    type (**), type (++)
  , Endo2
  , MinPlus, MaxPlus
  , MinTimes, MaxTimes
  -- * Presemirings
  , Presemiring(..), Predioid
  -- * Presemiring folds
  --, sum1, product1
  --, xmult1, eval1
  -- * Semirings
  , Semiring(..), Dioid
  , two, fromNatural
  , liftEndo, lowerEndo
  -- * Semiring folds
  , sum, product
  --, xmult, eval 
  -- * Semifields
  , Semifield(..)
  -- * Newtypes
  , Sum(..), Product(..)
  , F0(..), A1(..), F1(..)
) where

import safe Control.Category (Category, (>>>))
import safe Control.Applicative
--import safe Control.Applicative.Lift
import safe Data.Bool
import safe Data.Complex
import safe Data.Connection
import safe Data.Either
import safe Data.Tuple
import safe Data.Fixed
import safe Data.Foldable as Foldable (Foldable, foldl',foldr')
import safe Data.Functor.Apply
import safe Data.Functor.Alt
import safe Data.Functor.Compose
import safe Data.Functor.Contravariant
import safe Data.Functor.Identity
import safe Data.Functor.Rep
import safe Data.Int
import safe Data.List.NonEmpty
import safe Data.Maybe
import safe Data.Monoid hiding (Alt,Product(..),Sum(..))
import safe Data.Ord (Down(..), Ordering(..))
import safe Data.Prd
import safe Data.Profunctor
import safe Data.Profunctor.Yoneda
import safe Data.Semigroup hiding (Product(..), Sum(..))
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real (Ratio(..), Rational)
import safe Numeric.Natural
import safe Prelude
 ( Eq(..), Ord, IO, Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..)
 , id, flip, const, (.), ($), Integer, Float, Double, fst, snd, uncurry)
import safe Data.IntMap (IntMap)
import safe Data.IntSet (IntSet)
import safe Data.Map (Map)
import safe Data.Set (Set)
import safe Data.Sequence (Seq)
import safe qualified Data.Functor.Product as F
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set
import safe qualified Data.Monoid as M
import safe qualified Prelude as P
import safe qualified Control.Category as C

infixr 2 **

-- | Tensor product.
--
type (f ** g) = Compose f g

infixr 1 ++

-- | Direct sum.
--
type (f ++ g) = F.Product f g

-- | The Min-plus dioid.
type MinPlus a = Min a

-- | The Max-plus dioid.
type MaxPlus a = Min (Down a)

-- | The Min-times dioid.
type MinTimes a = Max (Down a)

-- | The Max-times dioid.
type MaxTimes a = Max a

-- | Endomorphism semiring.
--
-- The Boehm-Berarducci encoding of an arbitrary semiring is:
--
-- > forall a. (a -> a) -> a -> a
--
type Endo2 a = Endo (Endo a)

-------------------------------------------------------------------------------
-- Presemiring
-------------------------------------------------------------------------------

type Predioid a = (Prd a, Presemiring a)

-- | Right pre-semirings. and (non-unital and unital) right semirings.
-- 
-- Fun right pre-semiring (sometimes referred to as a bisemigroup) is a type /R/ endowed 
-- with two associative binary (i.e. semigroup) operations: '+' and '*', along with a 
-- right-distributivity property connecting them:
--
-- /Distributivity/
--
-- @
-- (a '+' b) '*' c = (a '*' c) '+' (b '*' c)
-- @
--
-- Note that addition and multiplication needn't be commutative.
--
-- See the properties module for a detailed specification of the laws.
--
class Presemiring a where

  infixl 6 +
  -- | Sum semigroup operation on a semiring.
  --
  -- >>> Dual [2] + Dual [3] :: Dual [Int]
  -- Dual {getDual = [3,2]}
  --
  (+) :: a -> a -> a

  infixl 7 *
  -- | Product semigroup operation on a semiring.
  --
  -- >>> Dual [2] * Dual [3] :: Dual [Int]
  -- Dual {getDual = [5]}
  --
  (*) :: a -> a -> a



-------------------------------------------------------------------------------
-- Semifields
-------------------------------------------------------------------------------

type Dioid a = (Prd a, Semiring a)

-- | Right semirings.
-- 
-- Fun right semiring is a pre-semiring with two distinct neutral elements, 'zero' 
-- and 'one', such that 'zero' is right-neutral wrt addition, 'one' is right-neutral wrt
-- multiplication, and 'zero' is right-annihilative wrt multiplication. 
--
-- /Neutrality/
--
-- @
-- 'zero' '+' r = r
-- 'one' '*' r = r
-- @
--
-- /Absorbtion/
--
-- @
-- 'zero' '*' a = 'zero'
-- @
--
class Presemiring a => Semiring a where

  -- | Sum unit of a semiring.
  --
  zero :: a

  -- | Product unit of a semiring.
  --
  one :: a

  --infixr 8 ^

  -- | Evaluate a natural-numbered power of a semiring element.
  --
  -- @ 'one' = a '^' 0 @
  --
  -- >>> 8 ^ 0 :: Int
  -- 1
  --
  (^) :: a -> Natural -> a
  --a ^ n = getProduct $ mreplicate n (Product a)
  a ^ n | n == zero = zero
        | otherwise = f a n
    where
        f x y 
            | P.even y = f (x * x) (y `P.quot` two)
            | y == one = x
            | otherwise = g (x * x) ((y P.- one) `P.quot` two) x
        g x y z 
            | P.even y = g (x * x) (y `P.quot` two) z
            | y == one = x * z
            | otherwise = g (x * x) ((y P.- one) `P.quot` two) (x * z)

--instance (Applicative f, Semigroup (f (g a)), Semigroup (g a)) => Presemiring (Tropical f g a) where
two :: Semiring a => a
two = one + one

-- | Evaluate a semiring sum using a given semiring.
-- 
sum :: Semiring a => Foldable f => f a -> a
sum = foldl' (+) zero
{-# INLINE sum #-}

-- | Evaluate a semiring product using a given semiring.
--
-- @
-- 'product' f = 'Data.foldl'' ('*') 'one'
-- @
--
-- >>> product [1..5 :: Int]
-- 120
--
product :: Semiring a => Foldable f => f a -> a
product = foldl' (*) one
{-# INLINE product #-}

liftEndo :: Semiring a => a -> Endo2 a
liftEndo a = Endo $ \(Endo f) -> Endo (\y -> a * f zero + y)

lowerEndo :: Semiring a => Endo2 a -> a
lowerEndo (Endo f) = appEndo (f $ Endo (one +)) zero

-------------------------------------------------------------------------------
-- Semifields
-------------------------------------------------------------------------------

infixl 7 \\, /

-- | A semifield, near-field, or division ring.
--
-- Instances needn't have commutative multiplication or additive inverses,
-- however addition must be commutative, and addition and multiplication must 
-- be associative as usual.
--
-- See also the wikipedia definitions of:
--
-- * < https://en.wikipedia.org/wiki/Semifield semifield >
-- * < https://en.wikipedia.org/wiki/Near-field_(mathematics) near-field >
-- * < https://en.wikipedia.org/wiki/Division_ring division ring >
-- 
class Semiring a => Semifield a where

  -- | Reciprocal of a multiplicative group element.
  --
  -- @ 
  -- x '/' y = x '*' 'recip' y
  -- x '\\' y = 'recip' x '*' y
  -- @
  --
  -- >>> recip (3 :+ 4) :: Complex Rational
  -- 3 % 25 :+ (-4) % 25
  -- >>> recip (3 :+ 4) :: Complex Double
  -- 0.12 :+ (-0.16)
  -- >>> recip (3 :+ 4) :: Complex Pico
  -- 0.120000000000 :+ -0.160000000000
  -- 
  recip :: a -> a 
  recip x = one / x
  {-# INLINE recip #-}

  -- | Right division by a multiplicative group element.
  --
  (/) :: a -> a -> a
  (/) x y = x * recip y
  {-# INLINE (/) #-}

  -- | Left division by a multiplicative group element.
  --
  -- When '*' is commutative we must have:
  --
  -- @ x '\\' y = y '/' x @
  --
  (\\) :: a -> a -> a
  (\\) x y = recip x * y

  --infixr 8 ^^

  -- | Integral power of a multiplicative group element.
  --
  -- @ 'one' '==' a '^^' 0 @
  --
  -- >>> 8 ^^ 0 :: Double
  -- 1.0
  -- >>> 8 ^^ 0 :: Pico
  -- 1.000000000000
  --
  --(^^) :: a -> Integer -> a
  --default (^^) :: Group (Product a) => a -> Integer -> a
  --a ^^ n = getProduct $ greplicate n (Product a)

  -- | A /NaN/ value of the semifield.
  --
  -- @ 'anan' = 'zero' '/' 'zero' @
  --
  anan :: a
  anan = zero / zero
  {-# INLINE anan #-}

  -- | The positive infinity of the semifield.
  --
  -- @ 'pinf' = 'one' '/' 'zero' @
  --
  pinf :: a
  pinf = one / zero
  {-# INLINE pinf #-}

type Positive = Ratio Natural

type TripPositive a = Triple Positive a

-- | TODO: Document
--
fromPositive :: TripPositive a => Positive -> a
fromPositive = floor

{-
greplicate :: Integer -> a -> a
greplicate n a     
    | n == 0 = mempty
    | n > 0 = mreplicate (fromInteger n) a
    | otherwise = mreplicate (fromInteger $ abs n) (inv a)
-}

---------------------------------------------------------------------
-- Newtypes
---------------------------------------------------------------------

newtype F0 a = F0 { getF0 :: a } deriving (Functor)
deriving via Identity instance Applicative F0

newtype A1 f a = A1 { getA1 :: f a } deriving (Functor)
deriving via (Ap f) instance (Applicative f) => Applicative (A1 f) 

newtype F1 f a = F1 { getF1 :: f a } deriving (Functor)
deriving via (Ap f) instance (Applicative f) => Applicative (F1 f) 

newtype Tropical f g a = Tropical { getTropical :: f (g a) } deriving (Functor)
deriving via (Compose f g) instance (Applicative f, Applicative g) => Applicative (Tropical f g) 

---------------------------------------------------------------------
--  Sum & Product
---------------------------------------------------------------------
-- | A commutative 'Semigroup' under '+'.
newtype Sum a = Sum { getSum :: a }
  deriving stock (Eq, Generic, Ord, Show)
  deriving (Functor, Applicative) via Identity

instance Presemiring a => Semigroup (Sum a) where
  (<>) = liftA2 (+)

instance Semiring a => Monoid (Sum a) where
  mempty = pure zero

-- | A (potentially non-commutative) 'Semigroup' under '*'.
newtype Product a = Product { getProduct :: a }
  deriving stock (Eq, Generic, Ord, Show)
  deriving (Functor, Applicative) via Identity

instance Presemiring a => Semigroup (Product a) where
  (<>) = liftA2 (*)

instance Semiring a => Monoid (Product a) where
  mempty = pure one


---------------------------------------------------------------------
--  Presemiring Instances
---------------------------------------------------------------------

instance P.Num a => Presemiring (F0 a) where
  (+) = liftA2 (P.+)
  (*) = liftA2 (P.*)

instance (Alt f, Apply f, Presemiring a) => Presemiring (A1 f a) where
  A1 x * A1 y = A1 $ liftF2 (*) x y
  A1 x + A1 y = A1 $ x <!> y

instance (Representable f, Presemiring a) => Presemiring (Co f a) where
  (+) = liftR2 (+)
  (*) = liftR2 (*)

instance (Applicative f, Presemiring a) => Presemiring (F1 f a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)

instance (Applicative f, Semigroup (f (g a)), Semigroup (g a)) => Presemiring (Tropical f g a) where
  Tropical x * Tropical y = Tropical $ x <> y
  Tropical x + Tropical y = Tropical $ liftA2 (<>) x y

deriving via (F1 (f**g) a) instance (Applicative f, Applicative g, Presemiring a) => Presemiring ((f**g) a) 
deriving via (F1 (f++g) a) instance (Applicative f, Applicative g, Presemiring a) => Presemiring ((f++g) a) 
-- the component-wise multiplication semiring. use the semimodule instances and .#. for matrix mult.
deriving via (F1 (f**g) a) instance (Applicative f, Applicative g, Semiring a) => Semiring ((f**g) a) 
deriving via (F1 (f++g) a) instance (Applicative f, Applicative g, Semiring a) => Semiring ((f++g) a) 

deriving via (F0 Int) instance Presemiring Int
deriving via (F0 Int8) instance Presemiring Int8
deriving via (F0 Int16) instance Presemiring Int16
deriving via (F0 Int32) instance Presemiring Int32
deriving via (F0 Int64) instance Presemiring Int64
deriving via (F0 Integer) instance Presemiring Integer

deriving via (F0 Word) instance Presemiring Word
deriving via (F0 Word8) instance Presemiring Word8
deriving via (F0 Word16) instance Presemiring Word16
deriving via (F0 Word32) instance Presemiring Word32
deriving via (F0 Word64) instance Presemiring Word64
deriving via (F0 Natural) instance Presemiring Natural

deriving via (F0 Uni) instance Presemiring Uni
deriving via (F0 Deci) instance Presemiring Deci
deriving via (F0 Centi) instance Presemiring Centi
deriving via (F0 Milli) instance Presemiring Milli
deriving via (F0 Micro) instance Presemiring Micro
deriving via (F0 Nano) instance Presemiring Nano
deriving via (F0 Pico) instance Presemiring Pico

deriving via (F0 Float) instance Presemiring Float
deriving via (F0 Double) instance Presemiring Double

deriving via (Co ((->)a) b) instance Presemiring b => Presemiring (a -> b)

-- For any ring we may define a dual ring which has the same underlying set and the same addition operation, but the opposite multiplication: 
-- Any left R-module M can then be seen to be a right module over Dual, and any right module over R can be considered a left module over Dual.
deriving via (Co Dual a) instance Presemiring a => Presemiring (Dual a)

deriving via (A1 IO a) instance Presemiring a => Presemiring (IO a) 
--deriving via (A1 Maybe a) instance Presemiring a => Presemiring (Maybe a) 
deriving via (A1 (Either e) a) instance Presemiring a => Presemiring (Either e a) 
deriving via (A1 [] a) instance Presemiring a => Presemiring [a] 
deriving via (A1 Seq a) instance Presemiring a => Presemiring (Seq a) 
deriving via (A1 NonEmpty a) instance Presemiring a => Presemiring (NonEmpty a) 
deriving via (A1 (Map k) a) instance (Ord k, Presemiring a) => Presemiring (Map k a) 
deriving via (A1 IntMap a) instance Presemiring a => Presemiring (IntMap a) 
--deriving via (A1 (Lift f) a) instance (Alt f, Semigroup a) => Presemiring (Lift f a) 

{-
λ> Min 3 + Min 4
Min {getMin = 3}
λ> Min 3 * Min 4
Min {getMin = 7}
λ> Min (Down 3) + Min (Down 4)
Min {getMin = Down 4}
λ> Min (Down 3) * Min (Down 4)
Min {getMin = Down 7}
-}
deriving via (Tropical Sum Min a) instance (Presemiring a, Ord a) => Presemiring (Min a)

{-
λ> Max 3 + Max 4
Max {getMax = 3}
λ> Max 3 * Max 4
Max {getMax = 12}
λ> Max (Down 3) + Max (Down 4)
Max {getMax = Down 4}
λ> Max (Down 3) * Max (Down 4)
Max {getMax = Down 12}
-}
deriving via (Tropical Product Max a) instance (Presemiring a, Ord a) => Presemiring (Max a)


instance Presemiring () where
  (+) _ _ = ()
  (*) _ _ = ()

instance Presemiring Bool where
  (+) = (||)
  (*) = (&&)

-- compare with Sign dioid
instance Presemiring Ordering where
  LT + x = x
  x + LT = x
  EQ + LT = EQ
  EQ + EQ = EQ
  EQ + GT = GT
  GT + _ = GT
  _ + GT = GT

  LT * _ = LT
  _ * LT = LT
  EQ * _ = EQ
  _ * EQ = EQ
  GT * GT = GT

instance Presemiring (Predicate a) where
  Predicate f + Predicate g = Predicate $ \b -> f b + g b
  {-# INLINE (+) #-}
  Predicate f * Predicate g = Predicate $ \b -> f b * g b
  {-# INLINE (*) #-}

instance Presemiring (Equivalence a) where
  Equivalence f + Equivalence g = Equivalence $ \x y -> f x y + g x y
  {-# INLINE (+) #-}
  Equivalence f * Equivalence g = Equivalence $ \x y -> f x y * g x y
  {-# INLINE (*) #-}

instance Presemiring a => Presemiring (Op a b) where
  Op f + Op g = Op $ \b -> f b + g b
  {-# INLINE (+) #-}
  Op f * Op g = Op $ \b -> f b * g b
  {-# INLINE (*) #-}

instance Presemiring (Endo2 a) where
  Endo f + Endo g = Endo $ f <> g
  {-# INLINE (+) #-}
  (*) = (<>) 
  {-# INLINE (*) #-}

instance Presemiring a => Presemiring (Maybe a) where
  Nothing + y = y
  x + Nothing = x
  Just x + Just y = Just (x + y)

  (*) = liftA2 (*)

instance Presemiring a => Presemiring (Ratio a) where
  (a :% b) + (c :% d) = (a * d + c * b) :% (b * d)
  (a :% b) * (c :% d) = (a * c) :% (b * d)

instance (Presemiring a, Presemiring b) => Presemiring (a, b) where
  (x1,y1) + (x2,y2) = (x1+x2, y1+y2)
  (x1,y1) * (x2,y2) = (x1*x2, y1*y2)

instance (Presemiring a, Presemiring b, Presemiring c) => Presemiring (a, b, c) where
  (x1,y1,z1) + (x2,y2,z2) = (x1+x2, y1+y2, z1+z2)
  (x1,y1,z1) * (x2,y2,z2) = (x1*x2, y1*y2, z1*z2)


---------------------------------------------------------------------
--  Semiring Instances
---------------------------------------------------------------------

instance P.Num a => Semiring (F0 a) where
  zero = F0 0
  one = F0 1

instance (Alt f, Apply f, Alternative f, Semiring a) => Semiring (A1 f a) where
  zero = A1 empty
  one = A1 . pure $ one

instance (Representable f, Semiring a) => Semiring (Co f a) where
  zero = pureRep zero
  one = pureRep one

instance (Applicative f, Semiring a) => Semiring (F1 f a) where
  zero = pure zero
  one = pure one

instance (Applicative f, Monoid (f (g a)), Monoid (g a)) => Semiring (Tropical f g a) where
  zero = Tropical mempty
  one = Tropical $ pure mempty

deriving via (F0 Int) instance Semiring Int
deriving via (F0 Int8) instance Semiring Int8
deriving via (F0 Int16) instance Semiring Int16
deriving via (F0 Int32) instance Semiring Int32
deriving via (F0 Int64) instance Semiring Int64
deriving via (F0 Integer) instance Semiring Integer

deriving via (F0 Word) instance Semiring Word
deriving via (F0 Word8) instance Semiring Word8
deriving via (F0 Word16) instance Semiring Word16
deriving via (F0 Word32) instance Semiring Word32
deriving via (F0 Word64) instance Semiring Word64
deriving via (F0 Natural) instance Semiring Natural

deriving via (F0 Uni) instance Semiring Uni
deriving via (F0 Deci) instance Semiring Deci
deriving via (F0 Centi) instance Semiring Centi
deriving via (F0 Milli) instance Semiring Milli
deriving via (F0 Micro) instance Semiring Micro
deriving via (F0 Nano) instance Semiring Nano
deriving via (F0 Pico) instance Semiring Pico
deriving via (F0 Float) instance Semiring Float
deriving via (F0 Double) instance Semiring Double

--deriving via (A1 Maybe a) instance Semiring a => Semiring (Maybe a) 
deriving via (A1 [] a) instance Semiring a => Semiring [a] 
deriving via (Co ((->)a) b) instance Semiring b => Semiring (a -> b)
deriving via (Co Dual a) instance Semiring a => Semiring (Dual a)

deriving via (Tropical Sum Min a) instance (Semiring a, Ord a, P.Bounded a) => Semiring (Min a)
deriving via (Tropical Product Max a) instance (Semiring a, Ord a, P.Bounded a) => Semiring (Max a)

instance Semiring () where
  zero = ()
  one = ()

instance Semiring Bool where
  zero = False
  one = True

instance Semiring Ordering where
  zero = LT
  one = GT

instance Semiring a => Semiring (Ratio a) where
  zero = zero :% one
  one = one :% one

instance Semiring a => Semiring (Op a b) where
  zero = Op $ const zero
  one = Op $ const one

instance Semiring (Predicate a) where
  zero = Predicate $ const zero
  one = Predicate $ const one

instance Semiring (Equivalence a) where
  zero = Equivalence $ \_ _ -> zero
  one = Equivalence $ \_ _ -> one

instance Semiring (Endo2 a) where
  zero = Endo $ const mempty
  one = mempty

instance Semiring a => Semiring (Maybe a) where
  zero = Nothing
  one = Just one

instance (Semiring a, Semiring b) => Semiring (a, b) where
  zero = (zero, zero)
  one = (one, one)

instance (Semiring a, Semiring b, Semiring c) => Semiring (a, b, c) where
  zero = (zero, zero, zero)
  one = (one, one, one)

---------------------------------------------------------------------
--  Semifield Instances
---------------------------------------------------------------------
instance P.Fractional a => Semifield (F0 a) where
  (/) = liftA2 (P./)

deriving via (F0 Uni) instance Semifield Uni
deriving via (F0 Deci) instance Semifield Deci
deriving via (F0 Centi) instance Semifield Centi
deriving via (F0 Milli) instance Semifield Milli
deriving via (F0 Micro) instance Semifield Micro
deriving via (F0 Nano) instance Semifield Nano
deriving via (F0 Pico) instance Semifield Pico

deriving via (F0 Float) instance Semifield Float
deriving via (F0 Double) instance Semifield Double

instance Semifield () where
  (/) _ _ = ()

instance Semiring a => Semifield (Ratio a) where
  (a :% b) / (c :% d) = (a * d) :% (b * c)
  {-# INLINE (/) #-}
