{-# LANGUAGE CPP                        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}


{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE QuantifiedConstraints                #-}
{-# LANGUAGE StandaloneDeriving                #-}

{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Data.Semiring where
{- (
  -- * Types
    type (-)
  , type (**) 
  , type (++) 
  , module Data.Semiring


  -- * Presemirings
  , type PresemiringLaw, Presemiring
  , (+), (*)
  -- * Presemiring folds
  , sum1, sumWith1
  , product1, productWith1
  , xmult1
  , eval1, evalWith1
  -- * Semirings
  , type SemiringLaw, Semiring
  , zero, one, two
  , (^)
  -- * Semiring folds
  , sum, sumWith
  , product, productWith
  , xmult   
  , eval, evalWith
  -- * Rings
  , type RingLaw, Ring
  , (-)
  , subtract, negate, abs, signum
  -- * Sum
  , Sum(..)
  -- * Product
  , Product(..)
  -- * Re-exports
  , mreplicate
  , Magma(..)
  , Quasigroup
  , Loop
  , Group(..)
) where
-}

import Control.Applicative
import Data.Bool
import Data.Complex
import Data.Either
import Data.Fixed
import Data.Foldable as Foldable (Foldable, foldl',foldl1)
import Data.Functor.Apply
import Data.Functor.Rep
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Contravariant
import Data.Group
import Data.Int
import Data.List.NonEmpty
import Data.Maybe
import Data.Monoid
import Data.Semigroup
import Data.Semigroup.Foldable as Foldable1
import Data.Prd
import Data.Ord (Down(..))
import Data.Word
import Foreign.C.Types (CFloat(..),CDouble(..))
import GHC.Generics (Generic)
--import GHC.TypeNats (KnownNat(..))
import GHC.Real hiding (Fractional(..), (^^), (^))
import Numeric.Natural
import Prelude (Eq, Ord, Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), id, flip, const, (.), ($), Integer, Float, Double)
import qualified Prelude as P
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Functor.Product as F


--import Data.Vector.Sized hiding (foldl')


infixr 2 **

-- | Tensor product.
--
type (f ** g) = Compose f g

infixr 1 ++

-- | Direct sum.
--
type (f ++ g) = F.Product f g


--type f $ a = N1 f a
-- | Hyphenation operator.
--type (g - f) a = f (g a)

newtype N0 a = N0 { getN0 :: a } deriving (Functor)

newtype N1 f a = N1 { getN1 :: f a } deriving (Functor)

newtype N2 f g a = N2 { getN2 :: f (g a) } deriving (Functor)

instance Applicative N0 where
  pure = N0
  N0 f <*> N0 a = N0 (f a)

instance Applicative f => Applicative (N1 f) where
  pure = N1 . pure
  N1 f <*> N1 a = N1 (f <*> a)

deriving via (Compose f g) instance (Applicative f, Applicative g) => Applicative (N2 f g) 


-- | A commutative 'Semigroup' under '+'.
newtype Additive a = Additive { getAdditive :: a }
  deriving stock (Eq, Generic, Ord, Show)
  deriving (Functor, Applicative) via Identity

-- | A (potentially non-commutative) 'Semigroup' under '*'.
newtype Multiplicative a = Multiplicative { getMultiplicative :: a }
  deriving stock (Eq, Generic, Ord, Show)
  deriving (Functor, Applicative) via Identity
{-
instance Presemiring a => Semigroup (Additive a) where
  Additive x <> Additive y = Additive $ x + y

instance Semiring a => Monoid (Additive a) where
  mempty = Additive zero

instance Presemiring a => Semigroup (Multiplicative a) where
  Multiplicative x <> Multiplicative y = Multiplicative $ x * y

instance Semiring a => Monoid (Multiplicative a) where
  mempty = Multiplicative one

--use for Semimodule?
instance Presemiring a => Semigroup (N1 Additive a) where
  N1 x <> N1 y = N1 $ liftA2 (+)

instance Semiring a => Monoid (N1 Additive a) where
  mempty = N1 $ pure zero
-}


type MinPlus a = Min a
type MaxPlus a = Min (Down a)
type MinTimes a = Max (Down a)
type MaxTimes a = Max a

newtype Tropical f g a = Tropical { getTropical :: f (g a) } deriving Show

instance (Applicative f, Semigroup (f (g a)), Semigroup (g a)) => Presemiring (Tropical f g a) where
  Tropical x * Tropical y = Tropical $ x <> y
  Tropical x + Tropical y = Tropical $ liftA2 (<>) x y

instance (Applicative f, Monoid (f (g a)), Monoid (g a)) => Semiring (Tropical f g a) where
  zero = Tropical mempty
  one = Tropical $ pure mempty
{-
(%%) :: (Add-Semigroup) a => a -> a -> a
a %% b = getNum (Num a <> Num b)
newtype Num a = Num { getNum :: a } deriving (Functor)

instance Applicative Num where
  pure = Add
  Num f <*> Num a = Num (f a)

instance (Semigroup a) => Semigroup (Num a) where
  (<>) = liftA2 (<>)

instance (Add-Semigroup) a => Presemiring a where
  (%%%) = (%%)

deriving via (Num P.String) instance Presemiring P.String 
-}
--deriving via (Sum Int) instance Presemiring Int -- Num a = Semigroup (Sum a)
--deriving via ((f++g) $ (a :: *)) instance (Applicative f, Applicative g, P.Num a) => Presemiring ((f++g) a) 
{-
instance (Sum-Semigroup) a => Presemiring a

--deriving instance Presemiring Int via (Sum Int)
--deriving via (Vector2D a) instance (Sum a) => Sum (Square a)

deriving via (Sum $ Double) instance Presemiring Double
deriving via (Sum P.String) instance Presemiring P.String -- Semigroup a => Semigroup (Sum a)

deriving via (Alt Maybe a) instance Presemiring (Maybe a) -- Alternative f => Semigroup (Alt f a)
-- Alternative f => Semigroup (Alt f a)

instance (Sum - Semigroup) a => Semigroup (Sum $ a) where
  (<>) = liftA2 (%%)

deriving via ((f++g) $ (a :: *)) instance (Sum-Semigroup) a => Presemiring ((f++g) a) --YESS!!! we can insert a 'node' between 'instance Num a' and 'instance Semigroup (Sum a)'

-}

{-
--TODO grok the difference between this and putting the constraint inthe class head
instance (forall f . Semigroup (f $ a)) => Presemiring a


deriving via (Sum $ Double) instance Presemiring Double
--deriving via (Fun (Alt Maybe) a) instance Presemiring a
deriving via ((f++g) $ (a :: *)) instance (Sum-Semigroup) a => Presemiring ((f++g) a) 
-}


-------------------------------------------------------------------------------
-- Presemiring
-------------------------------------------------------------------------------

--type PresemiringLaw a = ((Sum-Semigroup) a, (Product-Semigroup) a)

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
  default (+) :: Semigroup (Sum a) => a -> a -> a
  a + b = getSum (Sum a <> Sum b)
  {-# INLINE (+) #-}


  infixl 7 *

  -- | Product semigroup operation on a semiring.
  --
  -- >>> Dual [2] * Dual [3] :: Dual [Int]
  -- Dual {getDual = [5]}
  --
  (*) :: a -> a -> a
  default (*) :: Semigroup (Product a) => a -> a -> a
  a * b = getProduct (Product a <> Product b)
  {-# INLINE (*) #-}


instance (Semigroup (Sum a), Semigroup (Product a)) => Presemiring (N0 a) where
  N0 x * N0 y = N0 . getProduct $ Product x <> Product y
  N0 x + N0 y = N0 . getSum $ Sum x <> Sum y

instance (Alternative f, Semigroup a) => Presemiring (N1 f a) where
  N1 x * N1 y = N1 . getAp $ Ap x <> Ap y
  N1 x + N1 y = N1 . getAlt $ Alt x <> Alt y

instance (Applicative f, Applicative g, Presemiring a) => Presemiring (N2 f g a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*) -- should make this matrix mult instead? use Ap/Alt?

instance (Representable f, Presemiring a) => Presemiring (Co f a) where
  (+) = liftR2 (+)
  (*) = liftR2 (*)

--If R is a ring, we can define a dual ring which has the same underlying set and the same addition operation, but the opposite multiplication: 
-- > if a* b = c, then Dual b * Dual a = Dual c
-- Any left R-module M can then be seen to be a right module over Rop, and any right module over R can be considered a left module over Rop.
instance (Semigroup (Sum a), Semigroup (Product a)) => Presemiring (Dual a) where
  Dual x * Dual y = Dual . getProduct $ Product y <> Product x
  Dual x + Dual y = Dual . getSum $ Sum x <> Sum y


--  N0 x + N0 y = N0 . getSum $ Sum x <> Sum y
instance (Monoid (Sum a), Monoid (Product a)) => Semiring (N0 a) where
  one = N0 . getProduct $ mempty
  zero = N0 . getSum $ mempty

instance (Alternative f, Monoid a) => Semiring (N1 f a) where
  one = N1 . getAp $ mempty
  zero = N1 . getAlt $ mempty

instance (Applicative f, Applicative g, Semiring a) => Semiring (N2 f g a) where
  one = pure one
  zero = pure zero

instance (Monoid (Sum a), Monoid (Product a)) => Semiring (Dual a) where
  one = Dual . getProduct $ mempty
  zero = Dual . getSum $ mempty

instance (Group (Sum a), Monoid (Product a)) => Ring (N0 a) where
  N0 a - N0 b = N0 . getSum $ Sum a << Sum b

---TODO move upstream
--instance (Alternative f, Group a) => Magma (Alt f a) where
  
--instance (Alternative f, Group a) => Ring (N1 f a) where
--  N1 x - N1 y = N1 . getAlt $ Alt x << Alt y

--deriving via (Co (Vector n) a) instance (KnownNat n, Presemiring a) => Presemiring (Vector n a)

instance Presemiring Bool where
  (+) = (||)
  (*) = (&&)

instance Semiring Bool where
  one = True
  zero = False

deriving via (N0 Double) instance Presemiring Double
deriving via (N0 Int) instance Presemiring Int
deriving via (N0 Double) instance Semiring Double
deriving via (N0 Int) instance Semiring Int
--deriving via (N0 a) instance P.Num a => Presemiring a -- too generic?

instance Presemiring b => Presemiring (a -> b) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)

instance Semiring b => Semiring (a -> b) where
  one = pure one
  zero = pure zero

instance Ring b => Ring (a -> b) where
  (-) = liftA2 (-)

--deriving via (N1 ((->) r) a) instance Semigroup a => Presemiring (r -> a) 
deriving via (N1 Maybe a) instance Semigroup a => Presemiring (Maybe a) 
deriving via (N1 [] a) instance Semigroup a => Presemiring [a] 
deriving via (N1 ZipList a) instance Semigroup a => Presemiring (ZipList a) 
deriving via (N2 f g a) instance (Applicative f, Applicative g, Presemiring a) => Presemiring ((f**g) a) 

deriving via (N1 Maybe a) instance Monoid a => Semiring (Maybe a) 
deriving via (N1 [] a) instance Monoid a => Semiring [a] 
deriving via (N1 ZipList a) instance Monoid a => Semiring (ZipList a) 
deriving via (N2 f g a) instance (Applicative f, Applicative g, Semiring a) => Semiring ((f**g) a) 
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
deriving via (Tropical Sum Min a) instance (P.Num a, Ord a) => Presemiring (Min a)

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
deriving via (Tropical Product Max a) instance (P.Num a, Ord a) => Presemiring (Max a)



-- or try instance Num a => Semigroup (Product a) where..

{-
-- | Evaluate a non-empty presemiring sum using a given presemiring.
-- 
-- >>> evalWith1 Max $ (1 :| [2..5 :: Int]) :| [1 :| [2..5 :: Int]]
-- | Fold over a non-empty collection using the additive operation of an arbitrary semiring.
--
-- >>> sumWith1 First $ (1 :| [2..5 :: Int]) * (1 :| [2..5 :: Int])
-- First {getFirst = 1}
-- >>> sumWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
-- >>> sumWith1 Just $ 1 :| [2..5 :: Int]
-- Just 15
--
sumWith1 :: Foldable1 t => (b -> a) -> t b -> a
sumWith1 f = foldl1 (\a b -> a + f b) 
-- | Evaluate a non-empty presemiring product using a given presemiring.
-- 
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> productWith1 Just $ 1 :| [2..5 :: Int]
-- Just 120
-- >>> productWith1 First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
-- >>> productWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
productWith1 :: Foldable1 t => (b -> a) -> t b -> a
productWith1 f = getProduct . foldMap1 (Product . f)
{-# INLINE productWith1 #-}
-}

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
  default zero :: Monoid (Sum a) => a
  zero = getSum mempty
  {-# INLINE zero #-}

  -- | Product unit of a semiring.
  --
  one :: a
  default one :: Monoid (Product a) => a
  one = getProduct mempty
  {-# INLINE one #-}

  --infixr 8 ^

  -- | Evaluate a natural-numbered power of a semiring element.
  --
  -- @ 'one' = a '^' 0 @
  --
  -- >>> 8 ^ 0 :: Int
  -- 1
  --
  --(^) :: a -> Natural -> a
  --a ^ n = getMultiplicative $ mreplicate n (Multiplicative a)


--instance (Applicative f, Semigroup (f (g a)), Semigroup (g a)) => Presemiring (Tropical f g a) where


sum :: Semiring a => Foldable f => f a -> a
sum = sumWith id

-- | Evaluate a semiring sum using a given semiring.
-- 
sumWith :: Semiring a => Foldable f => (b -> a) -> f b -> a
sumWith f = foldl' (\a b -> a + f b) zero
{-# INLINE sumWith #-}

-- | Evaluate a semiring product using a given semiring.
--
-- @
-- 'product' f = 'Data.foldr'' (('*') . f) 'one'
-- @
--
-- >>> productWith Just [1..5 :: Int]
-- Just 120
--
productWith :: Semiring a => Foldable f => (b -> a) -> f b -> a
productWith f = foldl' (\a b -> a * f b) one
{-# INLINE productWith #-}


-------------------------------------------------------------------------------
-- Ring
-------------------------------------------------------------------------------

--type RingLaw a = ((Sum-Group) a, (Product-Monoid) a)

-- | Rings.
--
-- Fun ring /R/ is a commutative group with a second monoidal operation '*' that distributes over '+'.
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
-- See < https://en.wikipedia.org/wiki/Ring_(mathematics) >.
--
-- If the ring is < https://en.wikipedia.org/wiki/Ordered_ring ordered > (i.e. has an 'Ord' instance), then the following additional properties must hold:
--
-- @ a '<=' b ⇒ a '+' c '<=' b '+' c @
--
-- @ 'zero' '<=' a '&&' 'zero' '<=' b ⇒ 'zero' '<=' a '*' b @
--
-- See the properties module for a detailed specification of the laws.
--
class Semiring a => Ring a where

  infixl 6 -

  -- | Subtract two elements.
  --
  -- @
  -- a '-' b = 'subtract' b a
  -- @
  --
  (-) :: a -> a -> a
  (-) a b = a + negate b
  {-# INLINE (-) #-}

  -- | Reverse the sign of an element.
  --
  negate :: a -> a
  negate a = zero - a
  {-# INLINE negate #-}

  -- | Subtract two elements.
  --
  -- > subtract = flip (-)
  --
  --subtract :: a -> a -> a
  --subtract a b = b - a 
  --{-# INLINE subtract #-}

  -- | Absolute value of an element.
  --
  -- @ 'abs' r = r '*' ('signum' r) @
  --
  abs :: Prd a => a -> a
  abs x = bool (negate x) x $ zero <= x
  {-# INLINE abs #-}

  -- | Extract the sign of an element.
  --
  -- 'signum' satisfies a trichotomy law:
  --
  -- @ 'signum' r = 'negate' r || 'zero' || r @
  -- 
  -- This follows from the fact that ordered rings are abelian, linearly 
  -- ordered groups with respect to addition.
  --
  -- See < https://en.wikipedia.org/wiki/Linearly_ordered_group >.
  --
  signum :: Prd a => a -> a
  signum x = bool (negate one) one $ zero <= x
  {-# INLINE signum #-}



-------------------------------------------------------------------------------
-- Presemiring folds
-------------------------------------------------------------------------------

{-
-- | Evaluate a non-empty presemiring sum.
--
sum1 :: (Sum-Semigroup) a => Foldable1 f => f a -> a
sum1 = sumWith1 id


-- | Evaluate a non-empty presemiring product.
--
product1 :: (Product-Semigroup) a => Foldable1 f => f a -> a
product1 = productWith1 id



-- | Cross-multiply two non-empty collections.
--
-- >>> xmult1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
--
xmult1 :: Presemiring a => Foldable1 f => Apply f => f a -> f a -> a
xmult1 a b = sum1 $ liftF2 (*) a b
{-# INLINE xmult1 #-}

-- | Evaluate a presemiring expression.
-- 
eval1 :: Presemiring a => Functor f => Foldable1 f => Foldable1 g => f (g a) -> a
eval1 = sum1 . fmap product1

-- | Evaluate a presemiring expression using a given presemiring.
-- 
-- >>>  evalWith1 (Max . Down) $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = Down 9}
-- >>>  evalWith1 Max $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = 15}
-- 
evalWith1 :: Presemiring r => Functor f => Functor g => Foldable1 f => Foldable1 g => (a -> r) -> f (g a) -> r
evalWith1 f = sum1 . fmap product1 . (fmap . fmap) f

-------------------------------------------------------------------------------
-- Semiring
-------------------------------------------------------------------------------

type SemiringLaw a = ((Sum-Monoid) a, (Product-Monoid) a)



-- |
--
-- @
-- 'two' = 'one' '+' 'one'
-- @
--
two :: Semiring a => a
two = one + one
{-# INLINE two #-}



-------------------------------------------------------------------------------
-- Semiring folds
-------------------------------------------------------------------------------

-- | Evaluate a semiring sum.
-- 
-- >>> sum [1..5 :: Int]
-- 15
--
sum :: (Sum-Monoid) a => Foldable f => f a -> a
sum = sumWith id

-- | Evaluate a semiring sum using a given semiring.
-- 
sumWith :: (Sum-Monoid) a => Foldable f => (b -> a) -> f b -> a
sumWith f = foldr' ((+) . f) zero
{-# INLINE sumWith #-}

-- | Evaluate a semiring product.
--
-- >>> product [1..5 :: Int]
-- 120
--
product :: (Product-Monoid) a => Foldable f => f a -> a
product = productWith id

-- | Evaluate a semiring product using a given semiring.
--
-- @
-- 'product' f = 'Data.foldr'' (('*') . f) 'one'
-- @
--
-- >>> productWith Just [1..5 :: Int]
-- Just 120
--
productWith :: (Product-Monoid) a => Foldable f => (b -> a) -> f b -> a
productWith f = foldr' ((*) . f) one
{-# INLINE productWith #-}

-- | Cross-multiply two collections.
--
-- >>> xmult (V3 1 2 3) (V3 1 2 3)
-- 14
-- >>> xmult [1,2,3 :: Int] [1,2,3]
-- 36
-- >>> xmult [1,2,3 :: Int] []
-- 0
--
xmult :: Semiring a => Foldable f => Applicative f => f a -> f a -> a
xmult a b = sum $ liftA2 (*) a b
{-# INLINE xmult #-}

-- | Evaluate a semiring expression.
-- 
-- @ (a11 * .. * a1m) + (a21 * .. * a2n) + ... @
--
-- >>> eval [[1, 2], [3, 4 :: Int]] -- 1 * 2 + 3 * 4
-- 14
-- >>> eval $ sequence [[1, 2], [3, 4 :: Int]] -- 1 + 2 * 3 + 4
-- 21
--
eval :: Semiring a => Functor f => Foldable f => Foldable g => f (g a) -> a
eval = sum . fmap product

-- | Evaluate a semiring expression using a given semiring.
-- 
-- >>> evalWith Max [[1..4 :: Int], [0..2 :: Int]]
-- Max {getMax = 24}
--
evalWith :: Semiring r => Functor f => Functor g => Foldable f => Foldable g => (a -> r) -> f (g a) -> r
evalWith f = sum . fmap product . (fmap . fmap) f

-}

---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

{-
-- Semirings
instance Presemiring ()
instance Presemiring Bool
instance Presemiring Word
instance Presemiring Word8
instance Presemiring Word16
instance Presemiring Word32
instance Presemiring Word64
instance Presemiring Natural
instance Presemiring (Ratio Natural)

instance Presemiring Int
instance Presemiring Int8
instance Presemiring Int16
instance Presemiring Int32
instance Presemiring Int64
instance Presemiring Integer
instance Presemiring (Ratio Integer)

instance Presemiring Uni
instance Presemiring Deci
instance Presemiring Centi
instance Presemiring Milli
instance Presemiring Micro
instance Presemiring Nano
instance Presemiring Pico

instance Presemiring Float
instance Presemiring Double
instance Presemiring CFloat
instance Presemiring CDouble


instance Ring a => Presemiring (Complex a)
instance Presemiring a => Presemiring (e -> a)
--instance Presemiring a => Presemiring (Op a e)
instance (Presemiring a, Presemiring b) => Presemiring (Either a b)
instance Presemiring a => Presemiring (Maybe a)
instance (Sum-Semigroup) a => Presemiring [a]
instance (Sum-Semigroup) a => Presemiring (NonEmpty a)


instance Semiring ()
instance Semiring Bool
instance Semiring Word
instance Semiring Word8
instance Semiring Word16
instance Semiring Word32
instance Semiring Word64
instance Semiring Natural
instance Semiring (Ratio Natural)

instance Semiring Int
instance Semiring Int8
instance Semiring Int16
instance Semiring Int32
instance Semiring Int64
instance Semiring Integer
instance Semiring (Ratio Integer)

instance Semiring Uni
instance Semiring Deci
instance Semiring Centi
instance Semiring Milli
instance Semiring Micro
instance Semiring Nano
instance Semiring Pico

instance Semiring Float
instance Semiring Double
instance Semiring CFloat
instance Semiring CDouble

--instance Ring a => Semiring (Complex a)
instance Semiring a => Semiring (e -> a)
--instance Semiring a => Semiring (Op a e)
instance Semiring a => Semiring (Maybe a)
instance (Sum-Monoid) a => Semiring [a]

instance Presemiring IntSet.IntSet
instance Ord a => Presemiring (Set.Set a)
instance Presemiring a => Presemiring (IntMap.IntMap a)
instance (Ord k, Presemiring a) => Presemiring (Map.Map k a)
instance Semiring a => Semiring (IntMap.IntMap a)
instance (Ord k, (Product-Monoid) k, Semiring a) => Semiring (Map.Map k a)

-- Rings
instance Ring ()
instance Ring Int
instance Ring Int8
instance Ring Int16
instance Ring Int32
instance Ring Int64
instance Ring Integer
instance Ring (Ratio Integer)

instance Ring Uni
instance Ring Deci
instance Ring Centi
instance Ring Milli
instance Ring Micro
instance Ring Nano
instance Ring Pico

instance Ring Float
instance Ring Double
instance Ring CFloat
instance Ring CDouble

--instance Ring a => Ring (Complex a)
instance Ring a => Ring (e -> a)
--instance Ring a => Ring (Op a e)


import Data.Connection
import Data.Prd

  , forked
  , joined

  --, (&&&)
  , (|||)

joined :: Prd a => Trip a (Either a a)
joined = Trip Left (either id id) Right

--forked :: JoinSemilattice a => MeetSemilattice a => Trip (a, a) a
--forked = Trip (uncurry (∨)) (\x -> (x,x)) (uncurry (∧))

--infixr 3 &&&
--(&&&) :: Prd a => Prd b => JoinSemilattice c => MeetSemilattice c => Conn c a -> Conn c b -> Conn c (a, b)
--f &&& g = tripr forked >>> f `strong` g


{-
--(a ∧ b) ⊗ c = (a ⊗ c) ∧ (b ⊗ c), c ⊗ (a ∧ b) = (c ⊗ a) ∧ (c ⊗ b)
-- (meet x y) ∧ z = x ∧ z `meet` y ∧ z

-- idempotent sup dioids ? complete (join-semi)lattices derived from <=?
--connr-distributivity (the group (E\{ε}, ⊗) is therefore reticulated)
--
-- mon zero = const Nothing

-- bounded meet semilattice
-- need the codistributive property & absorbtion & commutativity

If E is a distributive lattice, then (E, ∨, ∧) is a doublyidempotent dioid, the order relation (canonical) of the dioid being defined as:
a ≤ b ⇔ a ∨ b = b.
Conversely, let (E, ⊕, ⊗) be a doubly-idempotent dioid for which ≤, the canonical
order relation relative to the law ⊕ is also a canonical order relation for ⊗:
x ≤ y ⇔ x ⊗ y = x.
Then E is a distributive lattice.
-}


-- Lattice types


type LatticeLaw a = (JoinSemilattice a, MeetSemilattice a)

type BoundedLatticeLaw a = (BoundedJoinSemilattice a, BoundedMeetSemilattice a)

type BoundedLattice a = (Lattice a, BoundedLatticeLaw a)

type LowerBoundedLattice a = (Lattice a, (Join-Monoid) a)

type UpperBoundedLattice a = (Lattice a, (Meet-Monoid) a)

type BoundedJoinSemilattice a = (JoinSemilattice a, (Join-Monoid) a)

type BoundedMeetSemilattice a = (MeetSemilattice a, (Meet-Monoid) a)


-- | Lattices.
--
-- A lattice is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- /Neutrality/
--
-- @
-- x '∨' 'zero' = x
-- x '∧' 'one' = x
-- @
--
-- /Associativity/
--
-- @
-- x '∨' (y '∨' z) = (x '∨' y) '∨' z
-- x '∧' (y '∧' z) = (x '∧' y) '∧' z
-- @
--
-- /Commutativity/
--
-- @
-- x '∨' y = y '∨' x
-- x '∧' y = y '∧' x
-- @
--
-- /Idempotency/
--
-- @
-- x '∨' x = x
-- x '∧' x = x
-- @
--
-- /Absorption/
--
-- @
-- (x '∨' y) '∧' y = y
-- (x '∧' y) '∨' y = y
-- @
--
-- See <http://en.wikipedia.org/wiki/Lattice_(order)> and <http://en.wikipedia.org/wiki/Absorption_law>.
--
-- Note that distributivity is _not_ a requirement for a lattice,
-- however distributive lattices are idempotent, commutative dioids.
-- 
class LatticeLaw a => Lattice a


-- | Birkhoff's self-dual < https://en.wikipedia.org/wiki/Median_algebra ternary median > operation.
--
-- If the lattice is distributive then 'glb' has the following properties.
--
-- @ 
-- 'glb' x y y = y
-- 'glb' x y z = 'glb' z x y
-- 'glb' x y z = 'glb' x z y
-- 'glb' ('glb' x w y) w z = 'glb' x w ('glb' y w z)
-- @
--
-- >>> glb 1 2 3 :: Int
-- 2
-- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
-- fromList [3,5]
--
-- See 'Data.Semilattice.Property'.
-- 
glb :: Lattice a => a -> a -> a -> a
glb = glbWith id

-- |
-- >>> glbWith N5 1 9 7
-- N5 {fromN5 = 7.0}
-- >>> glbWith N5 1 9 (0/0)
-- N5 {fromN5 = 9.0}
glbWith :: Lattice r => (a -> r) -> a -> a -> a -> r
glbWith f x y z = (f x ∨ f y) ∧ (f y ∨ f z) ∧ (f z ∨ f x)

-- | The order dual of 'glb'.
--
lub :: Lattice a => a -> a -> a -> a
lub = lubWith id

-- |
-- >>> lubWith N5 1 9 7
-- N5 {fromN5 = 7.0}
-- >>> lubWith N5 1 9 (0/0)
-- N5 {fromN5 = 1.0}
lubWith :: Lattice r => (a -> r) -> a -> a -> a -> r
lubWith f x y z = (f x ∧ f y) ∨ (f y ∧ f z) ∨ (f z ∧ f x)

{-
-- analagous to Maybe (Meet-Semigroup) instance
instance (Join-Semigroup) a => Semigroup (Join (Top a)) where
  Join Top <> _                      = Join Top
  Join (Fin{}) <> Join Top      = Join Top
  Join (Fin x) <> Join (Fin y) = Join . Fin $ x ∨ y

-- analagous to Maybe (Meet-Monoid) instance
instance (Join-Monoid) a => Monoid (Join (Top a)) where
  mempty = Join $ Fin bottom

instance (Meet-Semigroup) a => Semigroup (Meet (Top a)) where
  Meet (Fin x) <> Meet (Fin y) = Meet . Fin $ x ∧ y
  Meet (x@Fin{}) <> _             = Meet x
  Meet Top <> y                      = y

instance (Meet-Semigroup) a => Monoid (Meet (Top a)) where
  mempty = Meet Top

instance Lattice a => Lattice (Top a)

instance Covered (Top Float) where
  Bound x <. Bound y = shiftf 1 x == y

instance Graded (Top Float) where
  rank (Bound x) | ind x = 0
                   | otherwise = r where
    x' = floatInt32 x
    y' = floatInt32 (-1/0)
    r = fromIntegral . abs $ x' - y'
-}


-}

{-
-------------------------------------------------------------------------------
-- Sum
-------------------------------------------------------------------------------




instance Distributive Sum where
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Representable Sum where
  type Rep Sum = ()
  tabulate f = Sum (f ())
  {-# INLINE tabulate #-}

  index (Sum x) () = x
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- Product
-------------------------------------------------------------------------------


-- | A (potentially non-commutative) 'Semigroup' under '*'.
newtype Product a = Product { getProduct :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Product where
  pure = Product
  Product f <*> Product a = Product (f a)

instance Distributive Product where
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Representable Product where
  type Rep Product = ()
  tabulate f = Product (f ())
  {-# INLINE tabulate #-}

  index (Product x) () = x
  {-# INLINE index #-}


---------------------------------------------------------------------
-- Sum semigroup instances
---------------------------------------------------------------------

#define deriveSumSemigroup(ty)             \
instance Semigroup (Sum ty) where {        \
   a <> b = (P.+) <$> a <*> b                   \
;  {-# INLINE (<>) #-}                          \
}

deriveSumSemigroup(Int)
deriveSumSemigroup(Int8)
deriveSumSemigroup(Int16)
deriveSumSemigroup(Int32)
deriveSumSemigroup(Int64)
deriveSumSemigroup(Integer)

deriveSumSemigroup(Word)  --TODO clip these at maxBound to make dioids
deriveSumSemigroup(Word8)
deriveSumSemigroup(Word16)
deriveSumSemigroup(Word32)
deriveSumSemigroup(Word64)
deriveSumSemigroup(Natural)

deriveSumSemigroup(Uni)
deriveSumSemigroup(Deci)
deriveSumSemigroup(Centi)
deriveSumSemigroup(Milli)
deriveSumSemigroup(Micro)
deriveSumSemigroup(Nano)
deriveSumSemigroup(Pico)

deriveSumSemigroup(Float)
deriveSumSemigroup(CFloat)
deriveSumSemigroup(Double)
deriveSumSemigroup(CDouble)

#define deriveSumMonoid(ty)                \
instance Monoid (Sum ty) where {           \
   mempty = pure 0                              \
;  {-# INLINE mempty #-}                        \
}

deriveSumMonoid(Int)
deriveSumMonoid(Int8)
deriveSumMonoid(Int16)
deriveSumMonoid(Int32)
deriveSumMonoid(Int64)
deriveSumMonoid(Integer)

deriveSumMonoid(Word)
deriveSumMonoid(Word8)
deriveSumMonoid(Word16)
deriveSumMonoid(Word32)
deriveSumMonoid(Word64)
deriveSumMonoid(Natural)

deriveSumMonoid(Uni)
deriveSumMonoid(Deci)
deriveSumMonoid(Centi)
deriveSumMonoid(Milli)
deriveSumMonoid(Micro)
deriveSumMonoid(Nano)
deriveSumMonoid(Pico)

deriveSumMonoid(Float)
deriveSumMonoid(CFloat)
deriveSumMonoid(Double)
deriveSumMonoid(CDouble)

#define deriveSumMagma(ty)                 \
instance Magma (Sum ty) where {            \
   a << b = (P.-) <$> a <*> b                   \
;  {-# INLINE (<<) #-}                          \
}

deriveSumMagma(Int)
deriveSumMagma(Int8)
deriveSumMagma(Int16)
deriveSumMagma(Int32)
deriveSumMagma(Int64)
deriveSumMagma(Integer)

deriveSumMagma(Uni)
deriveSumMagma(Deci)
deriveSumMagma(Centi)
deriveSumMagma(Milli)
deriveSumMagma(Micro)
deriveSumMagma(Nano)
deriveSumMagma(Pico)

deriveSumMagma(Float)
deriveSumMagma(CFloat)
deriveSumMagma(Double)
deriveSumMagma(CDouble)

#define deriveSumQuasigroup(ty)            \
instance Quasigroup (Sum ty) where {             \
}

deriveSumQuasigroup(Int)
deriveSumQuasigroup(Int8)
deriveSumQuasigroup(Int16)
deriveSumQuasigroup(Int32)
deriveSumQuasigroup(Int64)
deriveSumQuasigroup(Integer)

deriveSumQuasigroup(Uni)
deriveSumQuasigroup(Deci)
deriveSumQuasigroup(Centi)
deriveSumQuasigroup(Milli)
deriveSumQuasigroup(Micro)
deriveSumQuasigroup(Nano)
deriveSumQuasigroup(Pico)

deriveSumQuasigroup(Float)
deriveSumQuasigroup(CFloat)
deriveSumQuasigroup(Double)
deriveSumQuasigroup(CDouble)

#define deriveSumLoop(ty)                  \
instance Loop (Sum ty) where {             \
   lreplicate n (Sum a) = Sum $ P.fromIntegral n  *  (-a) \
;  {-# INLINE lreplicate #-}                    \
}

deriveSumLoop(Int)
deriveSumLoop(Int8)
deriveSumLoop(Int16)
deriveSumLoop(Int32)
deriveSumLoop(Int64)
deriveSumLoop(Integer)

deriveSumLoop(Uni)
deriveSumLoop(Deci)
deriveSumLoop(Centi)
deriveSumLoop(Milli)
deriveSumLoop(Micro)
deriveSumLoop(Nano)
deriveSumLoop(Pico)

deriveSumLoop(Float)
deriveSumLoop(CFloat)
deriveSumLoop(Double)
deriveSumLoop(CDouble)

#define deriveSumGroup(ty)                 \
instance Group (Sum ty) where {            \
   greplicate n (Sum a) = Sum $ P.fromInteger n  *  a \
;  {-# INLINE greplicate #-}                    \
}

deriveSumGroup(Int)
deriveSumGroup(Int8)
deriveSumGroup(Int16)
deriveSumGroup(Int32)
deriveSumGroup(Int64)
deriveSumGroup(Integer)

deriveSumGroup(Uni)
deriveSumGroup(Deci)
deriveSumGroup(Centi)
deriveSumGroup(Milli)
deriveSumGroup(Micro)
deriveSumGroup(Nano)
deriveSumGroup(Pico)

deriveSumGroup(Float)
deriveSumGroup(CFloat)
deriveSumGroup(Double)
deriveSumGroup(CDouble)

instance ((Sum-Semigroup) a, Free f, Free g) => Semigroup (Sum ((f++g) a)) where
   (<>) = liftA2 $ mzipWithRep (+)
   {-# INLINE (<>) #-}

instance ((Sum-Monoid) a, Free f, Free g) => Monoid (Sum ((f++g) a)) where
   mempty = pure $ pureRep zero 
   {-# INLINE mempty #-}

instance ((Sum-Group) a, Free f, Free g) => Magma (Sum ((f++g) a)) where
   (<<) = liftA2 $ mzipWithRep (-)
   {-# INLINE (<<) #-}

instance ((Sum-Group) a, Free f, Free g) => Quasigroup (Sum ((f++g) a))
instance ((Sum-Group) a, Free f, Free g) => Loop (Sum ((f++g) a))
instance ((Sum-Group) a, Free f, Free g) => Group (Sum ((f++g) a))

instance ((Sum-Semigroup) a, Free f, Free g) => Semigroup (Sum ((f**g) a)) where
   (<>) = liftA2 $ mzipWithRep (+)
   {-# INLINE (<>) #-}

instance ((Sum-Monoid) a, Free f, Free g) => Monoid (Sum ((f**g) a)) where
   mempty = pure $ pureRep zero 
   {-# INLINE mempty #-}

instance ((Sum-Group) a, Free f, Free g) => Magma (Sum ((f**g) a)) where
   (<<) = liftA2 $ mzipWithRep (-)
   {-# INLINE (<<) #-}

instance ((Sum-Group) a, Free f, Free g) => Quasigroup (Sum ((f**g) a))
instance ((Sum-Group) a, Free f, Free g) => Loop (Sum ((f**g) a))
instance ((Sum-Group) a, Free f, Free g) => Group (Sum ((f**g) a))

instance (Sum-Semigroup) a => Semigroup (Sum (Complex a)) where
  Sum (a :+ b) <> Sum (c :+ d) = Sum $ (a + b) :+ (c + d)
  {-# INLINE (<>) #-}

instance (Sum-Monoid) a => Monoid (Sum (Complex a)) where
  mempty = Sum $ zero :+ zero

instance (Sum-Group) a => Magma (Sum (Complex a)) where
  Sum (a :+ b) << Sum (c :+ d) = Sum $ (subtract c a) :+ (subtract d b)
  {-# INLINE (<<) #-}

instance (Sum-Group) a => Quasigroup (Sum (Complex a))

instance (Sum-Group) a => Loop (Sum (Complex a)) where
  lreplicate n = mreplicate n . inv

instance (Sum-Group) a => Group (Sum (Complex a))

-- type Rng a = ((Sum-Group) a, (Product-Semigroup) a)
instance ((Sum-Group) a, (Product-Semigroup) a) => Semigroup (Product (Complex a)) where
  Product (a :+ b) <> Product (c :+ d) = Product $ (subtract (b * d) (a * c)) :+ (a * d + b * c)
  {-# INLINE (<>) #-}

{-
-- type Ring a = ((Sum-Group) a, (Product-Monoid) a)
instance ((Sum-Group) a, (Product-Monoid) a) => Monoid (Product (Complex a)) where
  mempty = Product $ one :+ zero

instance ((Sum-Group) a, (Product-Group) a) => Magma (Product (Complex a)) where
  Product (a :+ b) << Product (c :+ d) = Product $ ((a * c + b * d) / (c * c + d * d)) :+ ((subtract (a * d) (b * c)) / (c * c + d * d))
  {-# INLINE (<<) #-}

instance ((Sum-Group) a, (Product-Group) a) => Quasigroup (Product (Complex a))

instance ((Sum-Group) a, (Product-Group) a) => Loop (Product (Complex a)) where
  lreplicate n = mreplicate n . inv

instance ((Sum-Group) a, (Product-Group) a) => Group (Product (Complex a))
-}

instance ((Sum-Semigroup) a, (Product-Semigroup) a) => Semigroup (Sum (Ratio a)) where
  Sum (a :% b) <> Sum (c :% d) = Sum $ (a * d + c * b) :% (b  *  d)
  {-# INLINE (<>) #-}

instance ((Sum-Monoid) a, (Product-Monoid) a) => Monoid (Sum (Ratio a)) where
  mempty = Sum $ zero :% one

instance ((Sum-Group) a, (Product-Monoid) a) => Magma (Sum (Ratio a)) where
  Sum (a :% b) << Sum (c :% d) = Sum $ (subtract (c * b) (a * d)) :% (b  *  d)
  {-# INLINE (<<) #-}

instance ((Sum-Group) a, (Product-Monoid) a) => Quasigroup (Sum (Ratio a))

instance ((Sum-Group) a, (Product-Monoid) a) => Loop (Sum (Ratio a)) where
  lreplicate n = mreplicate n . inv

instance ((Sum-Group) a, (Product-Monoid) a) => Group (Sum (Ratio a))

instance (Sum-Semigroup) b => Semigroup (Sum (a -> b)) where
  (<>) = liftA2 . liftA2 $ (+)
  {-# INLINE (<>) #-}

instance (Sum-Monoid) b => Monoid (Sum (a -> b)) where
  mempty = pure . pure $ zero

instance (Sum-Group) b => Magma (Sum (a -> b)) where
  (<<) = liftA2 . liftA2 $ flip subtract 

instance (Sum-Group) b => Quasigroup (Sum (a -> b)) where
instance (Sum-Group) b => Loop (Sum (a -> b)) where
instance (Sum-Group) b => Group (Sum (a -> b)) where

instance ((Sum-Semigroup) a) => Semigroup (Sum (Op a b)) where
  Sum (Op f) <> Sum (Op g) = Sum . Op $ \b -> f b + g b
  {-# INLINE (<>) #-}

instance ((Sum-Monoid) a) => Monoid (Sum (Op a b)) where
  mempty = Sum . Op $ const zero

instance ((Sum-Group) a) => Magma (Sum (Op a b)) where
  Sum (Op f) << Sum (Op g) = Sum . Op $ \b -> f b - g b
  {-# INLINE (<<) #-}

instance ((Sum-Group) a) => Quasigroup (Sum (Op a b))
instance ((Sum-Group) a) => Loop (Sum (Op a b)) where
instance ((Sum-Group) a) => Group (Sum (Op a b))

instance Semigroup (Sum [a]) where
  (<>) = liftA2 (<>)

instance Monoid (Sum [a]) where
  mempty = pure mempty

-- >>> [1, 2] * [3, 4]
-- [4,5,5,6]
instance (Sum-Semigroup) a => Semigroup (Product [a]) where 
  (<>) = liftA2 . liftA2 $ (+) 
  {-# INLINE (<>) #-}

instance (Sum-Monoid) a => Monoid (Product [a]) where 
  mempty = pure [zero]

-- >>> (1 :| [2 :: Int]) * (3 :| [4 :: Int])
-- 4 :| [5,5,6]
instance Semigroup (Sum (NonEmpty a)) where
  (<>) = liftA2 (<>)

instance (Sum-Semigroup) a => Semigroup (Product (NonEmpty a)) where
  (<>) = liftA2 (+) 
  {-# INLINE (<>) #-}



-- MinPlus Predioid
-- >>> Min 1  *  Min 2 :: Min Int
-- Min {getMin = 3}
instance (Sum-Semigroup) a => Semigroup (Product (Min a)) where
  Product a <> Product b = Product $ liftA2 (+) a b

-- MinPlus Dioid
instance (Sum-Monoid) a => Monoid (Product (Min a)) where
  mempty = Product $ pure zero

instance (Sum-Semigroup) a => Semigroup (Sum (Down a)) where
  (<>) = liftA2 . liftA2 $ (+) 

instance (Sum-Monoid) a => Monoid (Sum (Down a)) where
  --Sum (Down a) <> Sum (Down b)
  mempty = pure . pure $ zero



instance Semigroup (Sum ()) where
  _ <> _ = pure ()
  {-# INLINE (<>) #-}

instance Monoid (Sum ()) where
  mempty = pure ()
  {-# INLINE mempty #-}

instance Magma (Sum ()) where
  _ << _ = pure ()

instance Quasigroup (Sum ()) 

instance Loop (Sum ()) 

instance Group (Sum ()) 

instance Semigroup (Sum Bool) where
  a <> b = (P.||) <$> a <*> b
  {-# INLINE (<>) #-}

instance Monoid (Sum Bool) where
  mempty = pure False
  {-# INLINE mempty #-}

--instance ((Sum-Semigroup) a, Minimal a) => Monoid (Sum a) where
--  mempty = Sum minimal

-- instance (Meet-Monoid) (Down a) => Monoid (Meet (Down a)) where mempty = Down <$> mempty

instance ((Sum-Semigroup) a, (Sum-Semigroup) b) => Semigroup (Sum (a, b)) where
  (<>) = liftA2 $ \(x1,y1) (x2,y2) -> (x1+x2, y1+y2)

instance ((Sum-Monoid) a, (Sum-Monoid) b) => Monoid (Sum (a, b)) where
  mempty = pure (zero, zero)

instance ((Sum-Semigroup) a, (Sum-Semigroup) b, (Sum-Semigroup) c) => Semigroup (Sum (a, b, c)) where
  (<>) = liftA2 $ \(x1,y1,z1) (x2,y2,z2) -> (x1+x2, y1+y2, z1+z2)

instance ((Sum-Monoid) a, (Sum-Monoid) b, (Sum-Monoid) c) => Monoid (Sum (a, b, c)) where
  mempty = pure (zero, zero, zero)

instance (Sum-Semigroup) a => Semigroup (Sum (Maybe a)) where
  Sum (Just x) <> Sum (Just y) = Sum . Just $ x + y
  Sum (x@Just{}) <> _           = Sum x
  Sum Nothing  <> y             = y

instance (Sum-Semigroup) a => Monoid (Sum (Maybe a)) where
  mempty = Sum Nothing

instance ((Sum-Semigroup) a, (Sum-Semigroup) b) => Semigroup (Sum (Either a b)) where
  Sum (Right x) <> Sum (Right y) = Sum . Right $ x + y

  Sum(x@Right{}) <> _     = Sum x
  Sum (Left x)  <> Sum (Left y)  = Sum . Left $ x + y
  Sum (Left _)  <> y     = y

instance Ord a => Semigroup (Sum (Set.Set a)) where
  (<>) = liftA2 Set.union 

instance (Ord k, (Sum-Semigroup) a) => Semigroup (Sum (Map.Map k a)) where
  (<>) = liftA2 (Map.unionWith (+))

instance (Sum-Semigroup) a => Semigroup (Sum (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.unionWith (+))

instance Semigroup (Sum IntSet.IntSet) where
  (<>) = liftA2 IntSet.union 

instance Monoid (Sum IntSet.IntSet) where
  mempty = Sum IntSet.empty

instance (Sum-Semigroup) a => Monoid (Sum (IntMap.IntMap a)) where
  mempty = Sum IntMap.empty

instance Ord a => Monoid (Sum (Set.Set a)) where
  mempty = Sum Set.empty

instance (Ord k, (Sum-Semigroup) a) => Monoid (Sum (Map.Map k a)) where
  mempty = Sum Map.empty




---------------------------------------------------------------------
-- Product Semigroup Instances
---------------------------------------------------------------------

#define deriveProductSemigroup(ty)       \
instance Semigroup (Product ty) where {  \
   a <> b = (P.*) <$> a <*> b                   \
;  {-# INLINE (<>) #-}                          \
}

deriveProductSemigroup(Int)
deriveProductSemigroup(Int8)
deriveProductSemigroup(Int16)
deriveProductSemigroup(Int32)
deriveProductSemigroup(Int64)
deriveProductSemigroup(Integer)

deriveProductSemigroup(Word)
deriveProductSemigroup(Word8)
deriveProductSemigroup(Word16)
deriveProductSemigroup(Word32)
deriveProductSemigroup(Word64)
deriveProductSemigroup(Natural)

deriveProductSemigroup(Uni)
deriveProductSemigroup(Deci)
deriveProductSemigroup(Centi)
deriveProductSemigroup(Milli)
deriveProductSemigroup(Micro)
deriveProductSemigroup(Nano)
deriveProductSemigroup(Pico)

deriveProductSemigroup(Float)
deriveProductSemigroup(CFloat)
deriveProductSemigroup(Double)
deriveProductSemigroup(CDouble)

#define deriveProductMonoid(ty)          \
instance Monoid (Product ty) where {     \
   mempty = pure 1                              \
;  {-# INLINE mempty #-}                        \
}

deriveProductMonoid(Int)
deriveProductMonoid(Int8)
deriveProductMonoid(Int16)
deriveProductMonoid(Int32)
deriveProductMonoid(Int64)
deriveProductMonoid(Integer)

deriveProductMonoid(Word)
deriveProductMonoid(Word8)
deriveProductMonoid(Word16)
deriveProductMonoid(Word32)
deriveProductMonoid(Word64)
deriveProductMonoid(Natural)

deriveProductMonoid(Uni)
deriveProductMonoid(Deci)
deriveProductMonoid(Centi)
deriveProductMonoid(Milli)
deriveProductMonoid(Micro)
deriveProductMonoid(Nano)
deriveProductMonoid(Pico)

deriveProductMonoid(Float)
deriveProductMonoid(CFloat)
deriveProductMonoid(Double)
deriveProductMonoid(CDouble)

#define deriveProductMagma(ty)                 \
instance Magma (Product ty) where {            \
   a << b = (P./) <$> a <*> b                         \
;  {-# INLINE (<<) #-}                                \
}

deriveProductMagma(Uni)
deriveProductMagma(Deci)
deriveProductMagma(Centi)
deriveProductMagma(Milli)
deriveProductMagma(Micro)
deriveProductMagma(Nano)
deriveProductMagma(Pico)

deriveProductMagma(Float)
deriveProductMagma(CFloat)
deriveProductMagma(Double)
deriveProductMagma(CDouble)

#define deriveProductQuasigroup(ty)            \
instance Quasigroup (Product ty) where {       \
}

deriveProductQuasigroup(Uni)
deriveProductQuasigroup(Deci)
deriveProductQuasigroup(Centi)
deriveProductQuasigroup(Milli)
deriveProductQuasigroup(Micro)
deriveProductQuasigroup(Nano)
deriveProductQuasigroup(Pico)

deriveProductQuasigroup(Float)
deriveProductQuasigroup(CFloat)
deriveProductQuasigroup(Double)
deriveProductQuasigroup(CDouble)

#define deriveProductLoop(ty)                  \
instance Loop (Product ty) where {             \
   lreplicate n = mreplicate n . inv                  \
}

deriveProductLoop(Uni)
deriveProductLoop(Deci)
deriveProductLoop(Centi)
deriveProductLoop(Milli)
deriveProductLoop(Micro)
deriveProductLoop(Nano)
deriveProductLoop(Pico)

deriveProductLoop(Float)
deriveProductLoop(CFloat)
deriveProductLoop(Double)
deriveProductLoop(CDouble)

#define deriveProductGroup(ty)           \
instance Group (Product ty) where {      \
   greplicate n (Product a) = Product $ a P.^^ P.fromInteger n \
;  {-# INLINE greplicate #-}                    \
}

deriveProductGroup(Uni)
deriveProductGroup(Deci)
deriveProductGroup(Centi)
deriveProductGroup(Milli)
deriveProductGroup(Micro)
deriveProductGroup(Nano)
deriveProductGroup(Pico)

deriveProductGroup(Float)
deriveProductGroup(CFloat)
deriveProductGroup(Double)
deriveProductGroup(CDouble)



instance (Product-Semigroup) a => Semigroup (Product (Ratio a)) where
  Product (a :% b) <> Product (c :% d) = Product $ (a * c) :% (b * d)
  {-# INLINE (<>) #-}

instance (Product-Monoid) a => Monoid (Product (Ratio a)) where
  mempty = Product $ getProduct mempty :% getProduct mempty

instance (Product-Monoid) a => Magma (Product (Ratio a)) where
  Product (a :% b) << Product (c :% d) = Product $ (a * d) :% (b * c)
  {-# INLINE (<<) #-}

instance (Product-Monoid) a => Quasigroup (Product (Ratio a))

instance (Product-Monoid) a => Loop (Product (Ratio a)) where
  lreplicate n = mreplicate n . inv

instance (Product-Monoid) a => Group (Product (Ratio a))


---------------------------------------------------------------------
-- Misc
---------------------------------------------------------------------

--instance ((Product-Semigroup) a, Maximal a) => Monoid (Product a) where
--  mempty = Product maximal

instance Semigroup (Product ()) where
  _ <> _ = pure ()
  {-# INLINE (<>) #-}

instance Monoid (Product ()) where
  mempty = pure ()
  {-# INLINE mempty #-}

instance  Magma (Product ()) where
  _ << _ = pure ()
  {-# INLINE (<<) #-}

instance Quasigroup (Product ())

instance Loop (Product ())

instance Group (Product ())

instance Semigroup (Product Bool) where
  a <> b = (P.&&) <$> a <*> b
  {-# INLINE (<>) #-}

instance Monoid (Product Bool) where
  mempty = pure True
  {-# INLINE mempty #-}

instance (Product-Semigroup) a => Semigroup (Product (Dual a)) where
  (<>) = liftA2 . liftA2 $ flip (*)

instance (Product-Monoid) a => Monoid (Product (Dual a)) where
  mempty = pure . pure $ one

instance (Product-Semigroup) a => Semigroup (Product (Down a)) where
  --Sum (Down a) <> Sum (Down b)
  (<>) = liftA2 . liftA2 $ (*) 

instance (Product-Monoid) a => Monoid (Product (Down a)) where
  mempty = pure . pure $ one

-- MaxTimes Predioid

instance (Product-Semigroup) a => Semigroup (Product (Max a)) where
  Product a <> Product b = Product $ liftA2 (*) a b

-- MaxTimes Dioid
instance (Product-Monoid) a => Monoid (Product (Max a)) where
  mempty = Product $ pure one

instance ((Product-Semigroup) a, (Product-Semigroup) b) => Semigroup (Product (a, b)) where
  Product (x1, y1) <> Product (x2, y2) = Product (x1 * x2, y1 * y2)

instance (Product-Semigroup) b => Semigroup (Product (a -> b)) where
  (<>) = liftA2 . liftA2 $ (*)
  {-# INLINE (<>) #-}

instance (Product-Monoid) b => Monoid (Product (a -> b)) where
  mempty = pure . pure $ one

{-
instance ((Product-Semigroup) a) => Semigroup (Product (Op a b)) where
  Product (Op f) <> Product (Op g) = Product . Op $ \b -> f b * g b
  {-# INLINE (<>) #-}

instance ((Product-Monoid) a) => Monoid (Product (Op a b)) where
  mempty = Product . Op $ const one
-}

instance (Product-Semigroup) a => Semigroup (Product (Maybe a)) where
  Product Nothing  <> _             = Product Nothing
  Product (Just{}) <> Product Nothing   = Product Nothing
  Product (Just x) <> Product (Just y) = Product . Just $ x * y
  -- Mul a <> Mul b = Mul $ liftA2 (*) a b

instance (Product-Monoid) a => Monoid (Product (Maybe a)) where
  mempty = Product $ pure one

instance ((Product-Semigroup) a, (Product-Semigroup) b) => Semigroup (Product (Either a b)) where
  Product (Right x) <> Product (Right y) = Product . Right $ x * y
  Product (Right{}) <> y     = y
  Product (Left x) <> Product (Left y)  = Product . Left $ x * y
  Product (x@Left{}) <> _     = Product x

instance Ord a => Semigroup (Product (Set.Set a)) where
  (<>) = liftA2 Set.intersection 

instance (Ord k, (Product-Semigroup) a) => Semigroup (Product (Map.Map k a)) where
  (<>) = liftA2 (Map.intersectionWith (*))

{-
A 'HashMap k' is not Applicative, but it is an instance of Apply
A 'Map k' is not Applicative, but it is an instance of Apply
An IntMap is not Applicative, but it is an instance of Apply
-}
instance (Product-Semigroup) a => Semigroup (Product (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.intersectionWith (*))

instance Semigroup (Product IntSet.IntSet) where
  (<>) = liftA2 IntSet.intersection 

instance (Ord k, (Product-Monoid) k, (Product-Monoid) a) => Monoid (Product (Map.Map k a)) where
  mempty = Product $ Map.singleton one one

instance (Product-Monoid) a => Monoid (Product (IntMap.IntMap a)) where
  mempty = Product $ IntMap.singleton 0 one

-}
