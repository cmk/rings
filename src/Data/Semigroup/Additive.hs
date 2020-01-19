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
{-# LANGUAGE TypeFamilies               #-}

module Data.Semigroup.Additive where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Maybe
import safe Data.Either
import safe Data.Distributive
import safe Data.Functor.Rep
import safe Data.Fixed
import safe Data.Foldable hiding (sum)
import safe Data.Group
import safe Data.Int
import safe Data.List
import safe Data.List.NonEmpty
import safe Data.Magma
import safe Data.Ord
import safe Data.Semigroup
import safe Data.Semigroup.Foldable
import safe Data.Semigroup.Multiplicative
import safe Data.Tuple
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..), div, (^^), (^), (%))
import safe Numeric.Natural

import safe Prelude ( Eq(..), Ord(..), Show, Ordering(..), Bounded(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet


add :: (Additive-Semigroup) a => a -> a -> a
a `add` b = unAdditive (Additive a <> Additive b)
{-# INLINE add #-}

sub :: (Additive-Group) a => a -> a -> a
a `sub` b = unAdditive (Additive a << Additive b)
{-# INLINE sub #-}

zero :: (Additive-Monoid) a => a
zero = unAdditive mempty
{-# INLINE zero #-}

-- | A commutative 'Semigroup' under '`add`'.
newtype Additive a = Additive { unAdditive :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Additive where
  pure = Additive
  Additive f <*> Additive a = Additive (f a)

instance Distributive Additive where
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Representable Additive where
  type Rep Additive = ()
  tabulate f = Additive (f ())
  {-# INLINE tabulate #-}

  index (Additive x) () = x
  {-# INLINE index #-}




{-
newtype Ordered a = Ordered { unOrdered :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Ordered where
  pure = Ordered
  Ordered f <*> Ordered a = Ordered (f a)

instance Distributive Ordered where
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Representable Ordered where
  type Rep Ordered = ()
  tabulate f = Ordered (f ())
  {-# INLINE tabulate #-}

  index (Ordered x) () = x
  {-# INLINE index #-}

newtype Plus a = Plus { unPlus :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Plus where
  pure = Plus
  Plus f <*> Plus a = Plus (f a)

instance Distributive Plus where
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Representable Plus where
  type Rep Plus = ()
  tabulate f = Plus (f ())
  {-# INLINE tabulate #-}

  index (Plus x) () = x
  {-# INLINE index #-}

instance (Additive-Semigroup) a => Semigroup (Multiplicative (Plus a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 add a b

instance (Additive-Monoid) a => Monoid (Multiplicative (Plus a)) where
  mempty = Multiplicative $ pure zero

-}
{-
instance (Multiplicative-Semigroup) (Plus a) => Semigroup (Multiplicative ((Min-Plus) a)) where
  (<>) = liftA2 (<>)

instance (Multiplicative-Monoid) (Plus a) => Monoid (Multiplicative ((Min-Plus) a)) where
  mempty = pure mempty
-}
{-
instance Semigroup (Min a) => Semigroup ((Min-Plus) a) where
  (<>) = liftA2 (<>)

instance Monoid (Min a) => Monoid ((Min-Plus) a) where
  mempty = pure mempty

instance Semigroup (Max a) => Semigroup ((Max-Plus) a) where
  (<>) = liftA2 (<>)

instance Monoid (Max a) => Monoid ((Max-Plus) a) where
  mempty = pure mempty
-}



---------------------------------------------------------------------
-- Num-based
---------------------------------------------------------------------

#define deriveAdditiveSemigroup(ty)             \
instance Semigroup (Additive ty) where {        \
   a <> b = (P.+) <$> a <*> b                   \
;  {-# INLINE (<>) #-}                          \
}

deriveAdditiveSemigroup(Int)
deriveAdditiveSemigroup(Int8)
deriveAdditiveSemigroup(Int16)
deriveAdditiveSemigroup(Int32)
deriveAdditiveSemigroup(Int64)
deriveAdditiveSemigroup(Integer)

deriveAdditiveSemigroup(Word)
deriveAdditiveSemigroup(Word8)
deriveAdditiveSemigroup(Word16)
deriveAdditiveSemigroup(Word32)
deriveAdditiveSemigroup(Word64)
deriveAdditiveSemigroup(Natural)

deriveAdditiveSemigroup(Uni)
deriveAdditiveSemigroup(Deci)
deriveAdditiveSemigroup(Centi)
deriveAdditiveSemigroup(Milli)
deriveAdditiveSemigroup(Micro)
deriveAdditiveSemigroup(Nano)
deriveAdditiveSemigroup(Pico)

deriveAdditiveSemigroup(Float)
deriveAdditiveSemigroup(CFloat)
deriveAdditiveSemigroup(Double)
deriveAdditiveSemigroup(CDouble)

#define deriveAdditiveMonoid(ty)                \
instance Monoid (Additive ty) where {           \
   mempty = pure 0                              \
;  {-# INLINE mempty #-}                        \
}

deriveAdditiveMonoid(Int)
deriveAdditiveMonoid(Int8)
deriveAdditiveMonoid(Int16)
deriveAdditiveMonoid(Int32)
deriveAdditiveMonoid(Int64)
deriveAdditiveMonoid(Integer)

deriveAdditiveMonoid(Word)
deriveAdditiveMonoid(Word8)
deriveAdditiveMonoid(Word16)
deriveAdditiveMonoid(Word32)
deriveAdditiveMonoid(Word64)
deriveAdditiveMonoid(Natural)

deriveAdditiveMonoid(Uni)
deriveAdditiveMonoid(Deci)
deriveAdditiveMonoid(Centi)
deriveAdditiveMonoid(Milli)
deriveAdditiveMonoid(Micro)
deriveAdditiveMonoid(Nano)
deriveAdditiveMonoid(Pico)

deriveAdditiveMonoid(Float)
deriveAdditiveMonoid(CFloat)
deriveAdditiveMonoid(Double)
deriveAdditiveMonoid(CDouble)

#define deriveAdditiveMagma(ty)                 \
instance Magma (Additive ty) where {            \
   a << b = (P.-) <$> a <*> b                   \
;  {-# INLINE (<<) #-}                          \
}

deriveAdditiveMagma(Int)
deriveAdditiveMagma(Int8)
deriveAdditiveMagma(Int16)
deriveAdditiveMagma(Int32)
deriveAdditiveMagma(Int64)
deriveAdditiveMagma(Integer)

deriveAdditiveMagma(Uni)
deriveAdditiveMagma(Deci)
deriveAdditiveMagma(Centi)
deriveAdditiveMagma(Milli)
deriveAdditiveMagma(Micro)
deriveAdditiveMagma(Nano)
deriveAdditiveMagma(Pico)

deriveAdditiveMagma(Float)
deriveAdditiveMagma(CFloat)
deriveAdditiveMagma(Double)
deriveAdditiveMagma(CDouble)

#define deriveAdditiveQuasigroup(ty)            \
instance Quasigroup (Additive ty) where {             \
}

deriveAdditiveQuasigroup(Int)
deriveAdditiveQuasigroup(Int8)
deriveAdditiveQuasigroup(Int16)
deriveAdditiveQuasigroup(Int32)
deriveAdditiveQuasigroup(Int64)
deriveAdditiveQuasigroup(Integer)

deriveAdditiveQuasigroup(Uni)
deriveAdditiveQuasigroup(Deci)
deriveAdditiveQuasigroup(Centi)
deriveAdditiveQuasigroup(Milli)
deriveAdditiveQuasigroup(Micro)
deriveAdditiveQuasigroup(Nano)
deriveAdditiveQuasigroup(Pico)

deriveAdditiveQuasigroup(Float)
deriveAdditiveQuasigroup(CFloat)
deriveAdditiveQuasigroup(Double)
deriveAdditiveQuasigroup(CDouble)

#define deriveAdditiveLoop(ty)                  \
instance Loop (Additive ty) where {             \
   lreplicate n (Additive a) = Additive $ P.fromIntegral n  `mul`  (-a) \
;  {-# INLINE lreplicate #-}                    \
}

deriveAdditiveLoop(Int)
deriveAdditiveLoop(Int8)
deriveAdditiveLoop(Int16)
deriveAdditiveLoop(Int32)
deriveAdditiveLoop(Int64)
deriveAdditiveLoop(Integer)

deriveAdditiveLoop(Uni)
deriveAdditiveLoop(Deci)
deriveAdditiveLoop(Centi)
deriveAdditiveLoop(Milli)
deriveAdditiveLoop(Micro)
deriveAdditiveLoop(Nano)
deriveAdditiveLoop(Pico)

deriveAdditiveLoop(Float)
deriveAdditiveLoop(CFloat)
deriveAdditiveLoop(Double)
deriveAdditiveLoop(CDouble)

#define deriveAdditiveGroup(ty)                 \
instance Group (Additive ty) where {            \
   greplicate n (Additive a) = Additive $ P.fromInteger n  `mul`  a \
;  {-# INLINE greplicate #-}                    \
}

deriveAdditiveGroup(Int)
deriveAdditiveGroup(Int8)
deriveAdditiveGroup(Int16)
deriveAdditiveGroup(Int32)
deriveAdditiveGroup(Int64)
deriveAdditiveGroup(Integer)

deriveAdditiveGroup(Uni)
deriveAdditiveGroup(Deci)
deriveAdditiveGroup(Centi)
deriveAdditiveGroup(Milli)
deriveAdditiveGroup(Micro)
deriveAdditiveGroup(Nano)
deriveAdditiveGroup(Pico)

deriveAdditiveGroup(Float)
deriveAdditiveGroup(CFloat)
deriveAdditiveGroup(Double)
deriveAdditiveGroup(CDouble)

---------------------------------------------------------------------
-- Complex
---------------------------------------------------------------------

instance (Additive-Semigroup) a => Semigroup (Additive (Complex a)) where
  Additive (a :+ b) <> Additive (c :+ d) = Additive $ (a `add` b) :+ (c `add` d)
  {-# INLINE (<>) #-}

instance (Additive-Monoid) a => Monoid (Additive (Complex a)) where
  mempty = Additive $ zero :+ zero

instance (Additive-Group) a => Magma (Additive (Complex a)) where
  Additive (a :+ b) << Additive (c :+ d) = Additive $ (a `sub` c) :+ (b `sub` d)
  {-# INLINE (<<) #-}

instance (Additive-Group) a => Quasigroup (Additive (Complex a))

instance (Additive-Group) a => Loop (Additive (Complex a)) where
  lreplicate n = mreplicate n . inv

instance (Additive-Group) a => Group (Additive (Complex a))

-- type Rng a = ((Additive-Group) a, (Multiplicative-Semigroup) a)
instance ((Additive-Group) a, (Multiplicative-Semigroup) a) => Semigroup (Multiplicative (Complex a)) where
  Multiplicative (a :+ b) <> Multiplicative (c :+ d) = Multiplicative $ (a `mul` c `sub` b `mul` d) :+ (a `mul` d `add` b `mul` c)
  {-# INLINE (<>) #-}

-- type Ring a = ((Additive-Group) a, (Multiplicative-Monoid) a)
instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Monoid (Multiplicative (Complex a)) where
  mempty = Multiplicative $ one :+ zero

instance ((Additive-Group) a, (Multiplicative-Group) a) => Magma (Multiplicative (Complex a)) where
  Multiplicative (a :+ b) << Multiplicative (c :+ d) = Multiplicative $ ((a `mul` c `add` b `mul` d) `div` (c `mul` c `add` d `mul` d)) :+ ((b `mul` c `sub` a `mul` d) `div` (c `mul` c `add` d `mul` d))
  {-# INLINE (<<) #-}

instance ((Additive-Group) a, (Multiplicative-Group) a) => Quasigroup (Multiplicative (Complex a))

instance ((Additive-Group) a, (Multiplicative-Group) a) => Loop (Multiplicative (Complex a)) where
  lreplicate n = mreplicate n . inv

instance ((Additive-Group) a, (Multiplicative-Group) a) => Group (Multiplicative (Complex a))

---------------------------------------------------------------------
-- Ratio
---------------------------------------------------------------------

instance ((Additive-Semigroup) a, (Multiplicative-Semigroup) a) => Semigroup (Additive (Ratio a)) where
  Additive (a :% b) <> Additive (c :% d) = Additive $ (a `mul` d `add` c `mul` b) :% (b  `mul`  d)
  {-# INLINE (<>) #-}

instance ((Additive-Monoid) a, (Multiplicative-Monoid) a) => Monoid (Additive (Ratio a)) where
  mempty = Additive $ zero :% one

instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Magma (Additive (Ratio a)) where
  Additive (a :% b) << Additive (c :% d) = Additive $ (a `mul` d `sub` c `mul` b) :% (b  `mul`  d)
  {-# INLINE (<<) #-}

instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Quasigroup (Additive (Ratio a))

instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Loop (Additive (Ratio a)) where
  lreplicate n = mreplicate n . inv

instance ((Additive-Group) a, (Multiplicative-Monoid) a) => Group (Additive (Ratio a))

instance (Additive-Semigroup) b => Semigroup (Additive (a -> b)) where
  (<>) = liftA2 . liftA2 $ add
  {-# INLINE (<>) #-}

instance (Additive-Monoid) b => Monoid (Additive (a -> b)) where
  mempty = pure . pure $ zero

instance Semigroup (Additive [a]) where
  (<>) = liftA2 (<>)

instance Monoid (Additive [a]) where
  mempty = pure mempty

-- >>> [1, 2] * [3, 4]
-- [4,5,5,6]
instance (Additive-Semigroup) a => Semigroup (Multiplicative [a]) where 
  (<>) = liftA2 . liftA2 $ add 
  {-# INLINE (<>) #-}

instance (Additive-Monoid) a => Monoid (Multiplicative [a]) where 
  mempty = pure [zero]

-- >>> (1 :| [2 :: Int]) * (3 :| [4 :: Int])
-- 4 :| [5,5,6]
instance Semigroup (Additive (NonEmpty a)) where
  (<>) = liftA2 (<>)

instance (Additive-Semigroup) a => Semigroup (Multiplicative (NonEmpty a)) where
  (<>) = liftA2 add 
  {-# INLINE (<>) #-}

---------------------------------------------------------------------
-- Idempotent and selective instances
---------------------------------------------------------------------

instance Semigroup (First a) => Semigroup (Additive (First a)) where
  (<>) = liftA2 (<>)

{-
instance Ord a => Semigroup (Additive (Down a)) where
  (<>) = liftA2 . liftA2 $ add

instance (Additive-Monoid) a => Monoid (Additive (Down a)) where
  mempty = pure . pure $ zero
-}

-- for MinPlus, MaxTimes

instance (Additive-Semigroup) a => Semigroup (Additive (Dual a)) where
  (<>) = liftA2 . liftA2 $ flip add

instance (Additive-Monoid) a => Monoid (Additive (Dual a)) where
  mempty = pure . pure $ zero

-- FirstPlus Predioid
instance (Additive-Semigroup) a => Semigroup (Multiplicative (First a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 add a b

instance Semigroup (Last a) => Semigroup (Additive (Last a)) where
  (<>) = liftA2 (<>)

-- LastPlus Predioid
instance (Additive-Semigroup) a => Semigroup (Multiplicative (Last a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 add a b

instance (Additive-Semigroup) a => Semigroup (Additive (Down a)) where
  (<>) = liftA2 . liftA2 $ add 

instance (Additive-Monoid) a => Monoid (Additive (Down a)) where
  --Additive (Down a) <> Additive (Down b)
  mempty = pure . pure $ zero

-- >>> Min 1 `add` Min 2 :: Min Int
-- Min {getMin = 1}
instance Semigroup (Min a) => Semigroup (Additive (Min a)) where
  (<>) = liftA2 (<>)

instance Semigroup (Max a) => Semigroup (Additive (Max a)) where
  (<>) = liftA2 (<>)

-- MinPlus Predioid
-- >>> Min 1  `mul`  Min 2 :: Min Int
-- Min {getMin = 3}
instance (Additive-Semigroup) a => Semigroup (Multiplicative (Min a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 add a b

-- MinPlus Dioid
instance (Additive-Monoid) a => Monoid (Multiplicative (Min a)) where
  mempty = Multiplicative $ pure zero


instance Semigroup (Additive ()) where
  _ <> _ = pure ()
  {-# INLINE (<>) #-}

instance Monoid (Additive ()) where
  mempty = pure ()
  {-# INLINE mempty #-}

instance Magma (Additive ()) where
  _ << _ = pure ()

instance Quasigroup (Additive ()) 

instance Loop (Additive ()) 

instance Group (Additive ()) 

instance Semigroup (Additive Bool) where
  a <> b = (P.||) <$> a <*> b
  {-# INLINE (<>) #-}

instance Monoid (Additive Bool) where
  mempty = pure False
  {-# INLINE mempty #-}

--instance ((Additive-Semigroup) a, Minimal a) => Monoid (Additive a) where
--  mempty = Additive minimal

-- instance (Meet-Monoid) (Down a) => Monoid (Meet (Down a)) where mempty = Down <$> mempty

instance ((Additive-Semigroup) a, (Additive-Semigroup) b) => Semigroup (Additive (a, b)) where
  Additive (x1, y1) <> Additive (x2, y2) = Additive (x1 `add` x2, y1 `add` y2)

instance (Additive-Semigroup) a => Semigroup (Additive (Maybe a)) where
  Additive (Just x) <> Additive (Just y) = Additive . Just $ x `add` y
  Additive (x@Just{}) <> _           = Additive x
  Additive Nothing  <> y             = y

instance ((Additive-Semigroup) a, (Additive-Semigroup) b) => Semigroup (Additive (Either a b)) where
  Additive (Right x) <> Additive (Right y) = Additive . Right $ x `add` y

  Additive(x@Right{}) <> _     = Additive x
  Additive (Left x)  <> Additive (Left y)  = Additive . Left $ x `add` y
  Additive (Left _)  <> y     = y

instance Ord a => Semigroup (Additive (Set.Set a)) where
  a <> b = Set.union <$> a <*> b

instance (Ord k, (Additive-Semigroup) a) => Semigroup (Additive (Map.Map k a)) where
  a <> b = Map.unionWith add <$> a <*> b

instance (Additive-Semigroup) a => Semigroup (Additive (IntMap.IntMap a)) where
  a <> b = IntMap.unionWith add <$> a <*> b

instance Semigroup (Additive IntSet.IntSet) where
  a <> b = IntSet.union <$> a <*> b

instance Monoid (Additive IntSet.IntSet) where
  mempty = Additive IntSet.empty

instance (Additive-Semigroup) a => Monoid (Additive (IntMap.IntMap a)) where
  mempty = Additive IntMap.empty

instance Ord a => Monoid (Additive (Set.Set a)) where
  mempty = Additive Set.empty

instance (Ord k, (Additive-Semigroup) a) => Monoid (Additive (Map.Map k a)) where
  mempty = Additive Map.empty

instance (Additive-Semigroup) a => Monoid (Additive (Maybe a)) where
  mempty = Additive Nothing
