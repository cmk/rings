{-# Language ConstrainedClassMethods #-}
{-# Language ConstraintKinds   #-}
{-# Language DefaultSignatures #-}
{-# Language DeriveFunctor #-}
{-# Language DeriveGeneric #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE CPP #-}
module Data.Semiring where

import safe Control.Applicative
import safe Control.Monad
import safe Data.Complex
import safe Data.Int
import safe Data.Word
import safe Data.Fixed
import safe Data.Foldable hiding (product)
import safe Data.Functor.Apply
import safe Data.Functor.Classes
import safe Data.Functor.Contravariant (Predicate(..), Equivalence(..), Op(..))
import safe Data.Functor.Identity (Identity(..))
import safe Data.List (unfoldr)
import safe Data.List.NonEmpty (NonEmpty(..))
import safe Data.Semigroup
import safe Data.Semigroup.Foldable
import safe Data.Typeable (Typeable)
import safe Foreign.Storable (Storable)
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic, Generic1)
import safe GHC.Real hiding ((^))-- (even, quot)
import safe Numeric.Natural
import safe Prelude hiding ((^), replicate, sum, product)
import safe qualified Data.Map as Map
import safe qualified Data.Sequence as Seq
import safe qualified Data.Set as Set
import safe qualified Data.IntMap as IntMap

-- | Constraint kind representing a unital semiring.
--
-- Used for convenience and to distinguish unital semirings from semirings with only an additive unit.
--
type Unital a = (Monoid a, Semiring a)

infixl 7 ><

-- | Right pre-semirings and (non-unital and unital) right semirings.
-- 
-- A right pre-semiring (sometimes referred to as a bisemigroup) is a type /R/ endowed 
-- with two associative binary (i.e. semigroup) operations: (<>) and (><), along with a 
-- right-distributivity property connecting them:
--
-- @
-- (a '<>' b) '><' c ≡ (a '><' c) '<>' (b '><' c)
-- @
--
-- A non-unital right semiring (sometimes referred to as a bimonoid) is a pre-semiring 
-- with a 'mempty' element that is neutral with respect to both addition and multiplication.
--
-- A unital right semiring is a pre-semiring with two distinct neutral elements, 'mempty' 
-- and 'sunit', such that 'mempty' is right-neutral wrt addition, 'sunit' is right-neutral wrt
--  multiplication, and 'mempty' is right-annihilative wrt multiplication. 
--
-- Note that 'sunit' needn't be distinct from 'mempty', moreover addition and multiplication
-- needn't be commutative or left-distributive.
--
-- See the properties module for a detailed specification of the laws.
--
class Semigroup a => Semiring a where

  -- | Multiplicative operation.
  (><) :: a -> a -> a  

  -- | Semiring homomorphism from the Boolean semiring to @r@.
  --
  -- If this map is injective then @r@ has a distinct multiplicative unit.
  --
  fromBoolean :: Monoid a => Bool -> a
  fromBoolean _ = mempty

-- | Default implementation of 'fromBoolean' given a multiplicative unit.
--
fromBooleanDef :: Unital a => a -> Bool -> a
fromBooleanDef _ False = mempty
fromBooleanDef o True = o
{-# INLINE fromBooleanDef #-}

-- | Multiplicative unit.
--
-- Note that 'sunit' needn't be distinct from 'mempty' for a semiring to be valid.
--
sunit :: Unital a => a
sunit = fromBoolean True
{-# INLINE sunit #-}

-- | Fold over a collection using the multiplicative operation of a semiring.
-- 
-- @
-- 'product' f ≡ 'Data.foldr'' ((><) . f) 'sunit'
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
product :: Foldable t => Unital a => (b -> a) -> t b -> a
product f = foldr' ((><) . f) sunit
{-# INLINE product #-}

-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
--
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> product1 Just $ 1 :| [2..(5 :: Int)]
-- Just 120
--
product1 :: Foldable1 t => Semiring a => (b -> a) -> t b -> a
product1 f = getProd . foldMap1 (Prod . f)
{-# INLINE product1 #-}

-- | Cross-multiply two collections.
--
-- >>> cross [1,2,3 :: Int] [1,2,3]
-- 36
--
-- >>> cross [1,2,3 :: Int] []
-- 0
--
cross :: Foldable f => Applicative f => Unital a => f a -> f a -> a
cross a b = fold $ liftA2 (><) a b
{-# INLINE cross #-}

-- | Cross-multiply two non-empty collections.
--
-- >>> cross1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
--
cross1 :: Foldable1 f => Apply f => Semiring a => f a -> f a -> a
cross1 a b = fold1 $ liftF2 (><) a b
{-# INLINE cross1 #-}

infixr 8 ^

(^) :: Unital a => a -> Natural -> a
(^) = flip replicate'
{-# INLINE (^) #-}

-- | A generalization of 'Data.List.replicate' to an arbitrary 'Monoid'. 
--
-- Adapted from <http://augustss.blogspot.com/2008/07/lost-and-found-if-i-write-108-in.html>.
--
replicate :: Monoid a => Natural -> a -> a
replicate n a
    | n == 0 = mempty
    | otherwise = f a n
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

replicate' :: Unital a => Natural -> a -> a
replicate' n a = getProd $ replicate n (Prod a)
{-# INLINE replicate' #-}

powers :: Unital a => Natural -> a -> a
powers n a = foldr' (<>) sunit . flip unfoldr n $ \m -> 
  if m == 0 then Nothing else Just (a^m,m-1)
{-# INLINE powers #-}

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

#define deriveSemiring(ty)         \
instance Semiring (ty) where {     \
   (><) = (*)                      \
;  fromBoolean = fromBooleanDef 1  \
;  {-# INLINE (><) #-}             \
;  {-# INLINE fromBoolean #-}      \
}

deriveSemiring(Word)
deriveSemiring(Word8)
deriveSemiring(Word16)
deriveSemiring(Word32)
deriveSemiring(Word64)
deriveSemiring(Natural)

deriveSemiring(Int)
deriveSemiring(Int8)
deriveSemiring(Int16)
deriveSemiring(Int32)
deriveSemiring(Int64)
deriveSemiring(Integer)

deriveSemiring(Uni)
deriveSemiring(Deci)
deriveSemiring(Centi)
deriveSemiring(Milli)
deriveSemiring(Micro)
deriveSemiring(Nano)
deriveSemiring(Pico)

deriveSemiring(Float)
deriveSemiring(CFloat)
deriveSemiring(Double)
deriveSemiring(CDouble)

instance Semiring () where
  (><) _ _ = ()

  fromBoolean _ = ()

instance Semiring Bool where
  (><) = (&&)
  {-# INLINE (><) #-}

  fromBoolean = id
  {-# INLINE fromBoolean #-}

instance Semiring Ordering where
  LT >< LT = LT
  LT >< GT = LT
  _  >< EQ = EQ
  EQ >< _  = EQ
  GT >< x  = x

  fromBoolean = fromBooleanDef GT

instance Semiring a => Semigroup (Ratio a) where
  x1 :% y1 <> x2 :% y2 = (x1><y2 <> y1><x2) :% (y1><y2)

instance Unital a => Monoid (Ratio a) where
  mempty = mempty :% sunit

instance Unital a => Semiring (Ratio a) where
  x1 :% y1 >< x2 :% y2 = (x1><x2) :% (y1><y2)

  fromBoolean x = fromBoolean x :% sunit

-- >>> (> (0::Int)) >< ((< 10) <> (== 15)) $ 10
-- False
-- >>> (> (0::Int)) >< ((< 10) <> (== 15)) $ 15
-- True
instance Unital b => Semiring (a -> b) where
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = const . fromBoolean

instance Unital a => Semiring (Op a b) where
  Op f >< Op g = Op $ \x -> f x >< g x
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Op (const sunit)

instance (Unital a, Unital b) => Semiring (a, b) where
  (a, b) >< (c, d) = (a><c, b><d)
  {-# INLINE (><) #-}

  fromBoolean = liftA2 (,) fromBoolean fromBoolean

instance (Unital a, Unital b, Unital c) => Semiring (a, b, c) where
  (a, b, c) >< (d, e, f) = (a><d, b><e, c><f)
  {-# INLINE (><) #-}

  fromBoolean = liftA3 (,,) fromBoolean fromBoolean fromBoolean

-- >>> [1, 2] >< [3, 4]
-- [4,5,5,6]
instance Monoid a => Semiring [a] where 
  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

instance Unital a => Semiring (Maybe a) where 
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

instance Unital a => Semiring (Dual a) where
  (><) = liftA2 $ flip (><)
  {-# INLINE (><)  #-}

  fromBoolean = Dual . fromBoolean
  {-# INLINE fromBoolean #-}

instance Unital a => Semiring (Const a b) where
  (Const x) >< (Const y) = Const (x >< y)
  {-# INLINE (><)  #-}

  fromBoolean = Const . fromBoolean
  {-# INLINE fromBoolean #-}

instance Unital a => Semiring (Identity a) where
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

instance Unital a => Semiring (IO a) where 
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

{-
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
-}

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
-- Instances (orphans)
---------------------------------------------------------------------

instance Semigroup Bool where
  (<>) = (||)
  {-# INLINE (<>) #-}

instance Monoid Bool where mempty = False

instance Semigroup a => Semigroup (Complex a) where
  (x1 :+ y1) <> (x2 :+ y2) = (x1 <> x2) :+ (y1 <> y2)
  {-# INLINE (<>) #-}

instance Monoid a => Monoid (Complex a) where
  mempty = mempty :+ mempty

#define deriveSemigroup(ty)        \
instance Semigroup (ty) where {    \
   (<>) = (+)                      \
;  {-# INLINE (<>) #-}             \
}

#define deriveMonoid(ty)           \
instance Monoid (ty) where {       \
   mempty = 0                      \
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

deriveSemigroup(Int)
deriveSemigroup(Int8)
deriveSemigroup(Int16)
deriveSemigroup(Int32)
deriveSemigroup(Int64)
deriveSemigroup(Integer)

deriveMonoid(Int)
deriveMonoid(Int8)
deriveMonoid(Int16)
deriveMonoid(Int32)
deriveMonoid(Int64)
deriveMonoid(Integer)

deriveSemigroup(Uni)
deriveSemigroup(Deci)
deriveSemigroup(Centi)
deriveSemigroup(Milli)
deriveSemigroup(Micro)
deriveSemigroup(Nano)
deriveSemigroup(Pico)

deriveMonoid(Uni)
deriveMonoid(Deci)
deriveMonoid(Centi)
deriveMonoid(Milli)
deriveMonoid(Micro)
deriveMonoid(Nano)
deriveMonoid(Pico)

deriveSemigroup(Float)
deriveSemigroup(CFloat)
deriveMonoid(Float)
deriveMonoid(CFloat)

deriveSemigroup(Double)
deriveSemigroup(CDouble)
deriveMonoid(Double)
deriveMonoid(CDouble)

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

-- Note that 'sunit' must be distinct from 'mempty' for this instance to be legal.
instance Unital a => Monoid (Prod a) where
  mempty = Prod sunit
  {-# INLINE mempty #-}
