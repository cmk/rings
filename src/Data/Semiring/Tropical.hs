{-# Language DeriveGeneric #-}

module Data.Dioid.Tropical where

import Data.Prd
import Data.Semigroup hiding (Min,Max)
import Data.Semiring
import Data.Dioid
--import Data.Number.Refined
import GHC.Generics                (Generic, Generic1)
import Foreign.Storable            (Storable)

import Prelude
--import Data.Number.LogFloat

type MinFirst a = Min (First a)
type MinLast  a = Min (Last a)
type MinPlus  a = Min (Additive a)

-- | The 'Min' dioid.
--
-- Typically multiplication is given by either 'Additive' or 'First'.
--
-- Note that the underlying monoid instance must be right-distributive
-- wrt 'min':
--
-- @
-- ('min' b c) <> a == 'min' (b '<>' a) (c '<>' a)
-- @
-- 
newtype Min a = Min { unMin :: a } deriving (Eq, Ord, Show, Generic, Generic1)

instance Prd a => Prd (Min a) where
  (Min a) <~ (Min b) = a <~ b
  (Min a) >~ (Min b) = a >~ b

instance Maximal a => Maximal (Min a) where
  maximal = Min maximal

instance Ord a => Semigroup (Min a) where
  Min a <> Min b = Min $ min a b

instance (Maximal a, Ord a) => Monoid (Min a) where
  mempty = maximal

instance (Maximal a, Monoid a, Eq a, Ord a) => Semiring (Min a) where
  Min a >< Min b | a == maximal || b == maximal = maximal -- need this for e.g. MinFirst / MinLast 
                 | otherwise = Min $ a <> b
  fromBoolean = fromBooleanDef $ Min mempty

{-
-- | The 'Min' dioid.
--
-- Typically multiplication is given by either 'Additive' or 'First'.
--
-- Note that the underlying monoid instance must be right-distributive
-- wrt 'min':
--
-- @
-- ('min' b c) <> a == 'min' (b '<>' a) (c '<>' a)
-- @
-- 
data Min a = PInf | Min !a deriving (Eq, Show, Functor, Generic, Typeable)



maybe2Min :: (forall a. a -> a) -> Maybe a -> Min a
maybe2Min _ Nothing = PInf
maybe2Min f (Just a) = Min $ f a

min2Maybe :: (forall a. a -> a) -> Min a -> Maybe a
min2Maybe  _ PInf = Nothing
min2Maybe f (Min a) = Just $ f a

instance Ord a => Prd (Min a) where
  Min a <~ Min b = a <= b
  a <~ PInf = True
  PInf <~ a = False
  pcompare = pcompareOrd

instance Ord a => Ord (Min a) where
  Min a <= Min b = a <= b
  a <= PInf = True
  PInf <= a = False

instance Ord a => Semigroup (Min a) where
  Min a <> Min b = Min $ min a b
  a <> PInf = a
  PInf <> a = a

instance Ord a => Monoid (Min a) where
  mempty = PInf

instance (Monoid a, Ord a) => Semiring (Min a) where
  Min a >< Min b = Min $ a <> b
  _ >< PInf = PInf
  PInf >< _ = PInf
  fromBoolean = fromBooleanDef $ Min mempty

-- instance (Monoid a, Ord a) => Dioid (Min a) where (<~) = (>=) 
{-
instance Kleene (Min Natural) where
  plus a = a >< star a

  star PInf = one
  star _    = PInf

instance Num a => Closed (Min (NonNegative a)) where
  star PInf = one
  star _    = PInf


instance Num a => Closed (Min (Positive a)) where
  star PInf = one
  star _    = PInf
-}


-- | The max dioid.
--
-- Typically multiplication is given by either 'Additive' or 'First'.
--
-- Note that the underlying monoid instance must be right-distributive
-- wrt 'max':
--
-- @
-- ('max' b c) <> a == 'max' (b '<>' a) (c '<>' a)
-- @
-- 
data Max a = NInf | Max !a deriving (Eq, Show, Functor, Generic, Typeable)

type MaxFirst a = Max (First a)
type MaxLast  a = Max (Last a)
type MaxPlus  a = Max (Additive a)

maybe2Max :: (forall a. a -> a) -> Maybe a -> Max a
maybe2Max _ Nothing = NInf
maybe2Max f (Just a) = Max $ f a

max2Maybe :: (forall a. a -> a) -> Max a -> Maybe a
max2Maybe  _ NInf = Nothing
max2Maybe f (Max a) = Just $ f a

instance Ord a => Ord (Max a) where
  Max a <= Max b = a <= b
  NInf <= a = True
  a <= NInf = False

instance Ord a => Semigroup (Max a) where
  Max a <> Max b = Max $ max a b
  a <> NInf = a
  NInf <> a = a

instance Ord a => Monoid (Max a) where
  mempty = NInf

instance (Monoid a, Ord a) => Semiring (Max a) where
  Max a >< Max b = Max $ a <> b
  _ >< NInf = NInf
  NInf >< _ = NInf

  fromBoolean = fromBooleanDef $ Max mempty

--instance (Monoid a, Ord a) => Dioid (Max a) where (<~) = (<=)

-}

{-
type MinTimes a = Min (Prod a)

E is the setR+of nonnegateative reals.⊕is the operation Max (maximum of two real numbers) with neutral elementε=0.⊗is the operation×(product of two real numbers) with unit element e=1.⊕is selective and⊗endowsR+\{0}with a group structure.It is therefore a selective-invertible dioid.The dioid(R+,Max,×)is isomorphic to the dioid(R∪{−∞},Max,+)throughthe one-to-one correspondence: x→ex.We observe that if we take⊗to be the addition of real numbers instead of themultiplication of real numbers, we obtain the structure(R+,Max,+)which is apre-dioid(see Sect. 2.4.1).

newtype MaxP = MaxP { unMaxP :: Double }

-- for floating pt types dont adjoin a separate infinity
instance Monoid MaxP where
  mempty = MaxP $ -1/0

-}

-- | The 'Log' dioid.
--
-- 'Log' tends to 'MaxPlus' in the limit as the base goes to infinity, 
-- and towards 'MinPlus' in the limit as the base goes to zero.
--
-- 'Log' uses 'Maybe's addition, where 'Nothing' is a tropical 
-- negateative infinity.
--
-- See also < https://en.wikipedia.org/wiki/Log_semiring >
--
{-
type Log = Maybe LogFloat

logmean :: Log -> Log -> Log
logmean (Just a) (Just b) = Just $ a + b - logFloat 2
logmean _ _ = Nothing

-- Orphan instances
instance Semigroup LogFloat where
  (<>) = (+)

instance Monoid LogFloat where
  mempty = 0

instance Semiring LogFloat where
  (><) = (*)
  fromBoolean = fromBooleanDef 1
-}
