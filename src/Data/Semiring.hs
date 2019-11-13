{-# Language ConstrainedClassMethods #-}

{-# Language DeriveFunctor #-}
{-# Language DeriveGeneric #-}

module Data.Semiring where

import Control.Applicative
import Control.Monad
import Data.Foldable hiding (product)
import Data.Functor.Apply
import Data.Functor.Classes
import Data.Functor.Contravariant
import Data.Functor.Contravariant (Predicate(..), Equivalence(..), Op(..))
import Data.Functor.Contravariant.Divisible
import Data.Functor.Identity (Identity(..))
import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Orphan ()
import Data.Typeable (Typeable)
import Foreign.Storable (Storable)
import GHC.Generics (Generic, Generic1)
import GHC.Real (even, quot)
import Numeric.Natural
import Prelude hiding ((^), replicate, sum, product)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap

-- | Right pre-semirings and (non-unital and unital) right semirings.
-- 
-- A right pre-semiring (sometimes referred to as a bisemigroup) is a type /R/ endowed 
-- with two associative binary (i.e. semigroup) operations: (<>) and (><), along with a 
-- right-distributivity property connecting them:
--
-- @
-- (a <> b) >< c ≡ (a >< c) <> (b >< c)
-- @
--
-- A non-unital right semiring (sometimes referred to as a bimonoid) is a pre-semiring 
-- with a 'mempty' element that is neutral with respect to both addition and multiplication.
--
-- A unital right semiring is a pre-semiring with two distinct neutral elements, 'mempty' 
-- and 'unit', such that 'mempty' is right-neutral wrt addition, 'unit' is right-neutral wrt
--  multiplication, and 'mempty' is right-annihilative wrt multiplication. 
--
-- Note that 'unit' needn't be distinct from 'mempty', moreover addition and multiplication
-- needn't be commutative or left-distributive.
--
-- See the properties module for a detailed specification of the laws.
--
class Semigroup r => Semiring r where

  -- Multiplicative operation
  (><) :: r -> r -> r  

  -- A semiring homomorphism from the Boolean semiring to @r@. 
  -- If this map is injective then @r@ has a distinct unit.
  fromBoolean :: Monoid r => Bool -> r
  fromBoolean _ = mempty

unit :: (Monoid r, Semiring r) => r
unit = fromBoolean True

fromBooleanDef :: (Monoid r, Semiring r) => r -> Bool -> r
fromBooleanDef _ False = mempty
fromBooleanDef o True = o

-- | Fold over a collection using the multiplicative operation of a semiring.
-- 
-- @
-- 'product' f ≡ 'Data.foldr'' ((><) . f) 'unit'
-- @
--
-- >>> (foldMap . product) id [[1, 2], [3, (4 :: Int)]] -- 1 >< 2 <> 3 >< 4
-- 14
--
-- >>> (product . foldMap) id [[1, 2], [3, (4 :: Int)]] -- 1 <> 2 >< 3 <> 4
-- 21
--
-- For semirings without a distinct multiplicative unit this is equivalent to @const mempty@:
--
-- >>> product Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'product1'.
--
product :: Foldable t => Monoid r => Semiring r => (a -> r) -> t a -> r
product f = foldr' ((><) . f) unit

-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
--
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> product1 Just $ 1 :| [2..(5 :: Int)]
-- Just 120
--
product1 :: Foldable1 t => Semiring r => (a -> r) -> t a -> r
product1 f = getProd . foldMap1 (Prod . f)

-- | Cross-multiply two collections.
--
-- >>> cross [1,2,3 :: Int] [1,2,3]
-- 36
--
-- >>> cross [1,2,3 :: Int] []
-- 0
--
cross :: Foldable f => Applicative f => Monoid r => Semiring r => f r -> f r -> r
cross a b = fold $ liftA2 (><) a b

-- | Cross-multiply two non-empty collections.
--
-- >>> cross1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
--
cross1 :: Foldable1 f => Apply f => Semiring r => f r -> f r -> r
cross1 a b = fold1 $ liftF2 (><) a b

-- | Fold with additive & multiplicative units.
--
-- This function will zero out if there is no multiplicative unit.
--
unital :: Monoid r => Semiring r => Foldable f => Foldable g => (a -> r) -> f (g a) -> r
unital = foldMap . product

-- | Fold with no multiplicative unit.
--
nonunital :: Monoid r => Semiring r => Foldable f => Foldable1 g => (a -> r) -> f (g a) -> r
nonunital = foldMap . product1

-- | Fold with no additive or multiplicative unit.
--
presemiring :: Semiring r => Foldable1 f => Foldable1 g => (a -> r) -> f (g a) -> r
presemiring = foldMap1 . product1

-- | A generalization of 'Data.List.replicate' to an arbitrary 'Monoid'. 
--
-- Adapted from <http://augustss.blogspot.com/2008/07/lost-and-found-if-i-write-108-in.html>.
--
replicate :: Monoid r => Natural -> r -> r
replicate y0 x0
    | y0 == 0 = mempty
    | otherwise = f x0 y0
    where
        f x y 
            | even y = f (x <> x) (y `quot` 2)
            | y == 1 = x
            | otherwise = g (x <> x) ((y - 1) `quot` 2) x
        g x y z 
            | even y = g (x <> x) (y `quot` 2) z
            | y == 1 = x <> z
            | otherwise = g (x <> x) ((y - 1) `quot` 2) (x <> z)
{-# INLINE replicate #-}

replicate' :: Monoid r => Semiring r => Natural -> r -> r
replicate' n r = getProd $ replicate n (Prod r)

infixr 8 ^

(^) :: Monoid r => Semiring r => r -> Natural -> r
(^) = flip replicate'

powers :: Monoid r => Semiring r => Natural -> r -> r
powers n a = foldr' (<>) unit . flip unfoldr n $ \m -> 
  if m == 0 then Nothing else Just (a^m,m-1)

-------------------------------------------------------------------------------
-- Pre-semirings
-------------------------------------------------------------------------------

-- | 'First a' forms a pre-semiring for any semigroup @a@.
--
-- >>> foldMap1 First $ 1 :| [2..(5 :: Int)] >< 1 :| [2..(5 :: Int)]
-- First {getFirst = 1}
--
-- >>> product1 First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
--
-- >>> foldMap1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
--
-- >>> product1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
instance Semigroup a => Semiring (First a) where
  (><) = liftA2 (<>)
  {-# INLINE (><)  #-}

instance Semigroup a => Semiring (Last a) where
  (><) = liftA2 (<>)
  {-# INLINE (><)  #-}

instance Ord a => Semiring (Max a) where
  (><) = min
  {-# INLINE (><)  #-}

instance Ord a => Semiring (Min a) where
  (><) = max
  {-# INLINE (><)  #-}

instance Semigroup a => Semiring (Either e a) where
  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

-- >>> (1 :| [2 :: Int]) >< (3 :| [4 :: Int])
-- 4 :| [5,5,6]
instance Semigroup a => Semiring (NonEmpty a) where
  (><) = liftA2 (<>) 
  {-# INLINE (><) #-}

-------------------------------------------------------------------------------
-- Semirings
-------------------------------------------------------------------------------

instance Semiring () where
  (><) _ _ = ()

  fromBoolean _ = ()

instance Semiring Ordering where
  LT >< LT = LT
  LT >< GT = LT
  _  >< EQ = EQ
  EQ >< _  = EQ
  GT >< x  = x

  fromBoolean = fromBooleanDef GT

instance Semiring Bool where
  (><) = (&&)

  fromBoolean = id

instance Semiring Natural where
  (><) = (*)

  fromBoolean = fromBooleanDef 1

instance Semiring Int where
  (><) = (*)

  fromBoolean = fromBooleanDef 1

instance Semiring Word where
  (><) = (*)

  fromBoolean = fromBooleanDef 1

-- >>> (> (0::Int)) >< ((< 10) <> (== 15)) $ 10
-- False
-- >>> (> (0::Int)) >< ((< 10) <> (== 15)) $ 15
-- True
instance (Monoid b, Semiring b) => Semiring (a -> b) where
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = const . fromBoolean

instance (Monoid a, Semiring a) => Semiring (Op a b) where
  Op f >< Op g = Op $ \x -> f x >< g x
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Op (const unit)

instance (Monoid a, Monoid b, Semiring a, Semiring b) => Semiring (a, b) where
  (a, b) >< (c, d) = (a><c, b><d)
  {-# INLINE (><) #-}

  fromBoolean = liftA2 (,) fromBoolean fromBoolean

instance Monoid a => Semiring [a] where 
  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

instance (Monoid a, Semiring a) => Semiring (Maybe a) where 
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

instance (Monoid a, Semiring a) => Semiring (Dual a) where
  (><) = liftA2 $ flip (><)
  {-# INLINE (><)  #-}

  fromBoolean = Dual . fromBoolean
  {-# INLINE fromBoolean #-}

instance (Monoid a, Semiring a) => Semiring (Const a b) where
  (Const x) >< (Const y) = Const (x >< y)
  {-# INLINE (><)  #-}

  fromBoolean = Const . fromBoolean
  {-# INLINE fromBoolean #-}

instance (Monoid a, Semiring a) => Semiring (Identity a) where
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

instance Semiring Any where 
  Any x >< Any y = Any $ x && y
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Any True

instance Semiring All where 
  All x >< All y = All $ x || y
  {-# INLINE (><) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean False = All True
  fromBoolean True = All False

instance (Monoid a, Semiring a) => Semiring (IO a) where 
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

---------------------------------------------------------------------
--  Instances (contravariant)
---------------------------------------------------------------------

-- Note that due to the underlying 'Monoid' instance this instance
-- has 'All' semiring semantics rather than 'Any'.
instance Semiring (Predicate a) where
  Predicate f >< Predicate g = Predicate $ \x -> f x || g x
  {-# INLINE (><) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean False = Predicate $ const True
  fromBoolean True = Predicate $ const False


-- Note that due to the underlying 'Monoid' instance this instance
-- has 'All' semiring semantics rather than 'Any'.
instance Semiring (Equivalence a) where
  Equivalence f >< Equivalence g = Equivalence $ \x y -> f x y || g x y
  {-# INLINE (><) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean False = Equivalence $ \_ _ -> True
  fromBoolean True = Equivalence $ \_ _ -> False


instance Semiring (Comparison a) where
  Comparison f >< Comparison g = Comparison $ \x y -> f x y >< g x y
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Comparison $ \_ _ -> GT

---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------

instance Ord a => Semiring (Set.Set a) where
  (><) = Set.intersection

instance Monoid a => Semiring (Seq.Seq a) where
  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Seq.singleton mempty

instance (Ord k, Monoid k, Monoid a) => Semiring (Map.Map k a) where
  xs >< ys = foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Map.singleton mempty mempty

instance Monoid a => Semiring (IntMap.IntMap a) where
  xs >< ys = foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ IntMap.singleton 0 mempty

---------------------------------------------------------------------
-- Newtype wrappers
---------------------------------------------------------------------

-- | Monoid under '><'. Analogous to 'Data.Monoid.Product', but uses the
-- 'Semiring' constraint, rather than 'Num'.
newtype Prod a = Prod { getProd :: a }
  deriving (Eq,Ord,Show,Bounded,Generic,Generic1,Typeable,Functor)

instance Applicative Prod where
  pure = Prod
  Prod f <*> Prod a = Prod (f a)

instance Semiring a => Semigroup (Prod a) where
  (<>) = liftA2 (><)
  {-# INLINE (<>) #-}

-- Note that 'unit' must be distinct from 'mempty' for this instance to be legal.
instance (Monoid a, Semiring a) => Monoid (Prod a) where
  mempty = Prod unit
  {-# INLINE mempty #-}
