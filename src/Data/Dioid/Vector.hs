{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic (
    module Type
  , module Property
  , module Carrier
  , module Operator
  , module Index
  , module Iso
  , module Lens
  , module Prism
  , module Grate
  , module Affine
  , module Option
  , module Traversal
  , module Fold
  , module Cotraversal
  , module View
  , module Setter
  , module Zoom
  , module Data.Profunctor.Optic 
) where

import Data.Profunctor.Optic.Types            as Type
import Data.Profunctor.Optic.Property         as Property
import Data.Profunctor.Optic.Carrier          as Carrier
import Data.Profunctor.Optic.Operator         as Operator
import Data.Profunctor.Optic.Index            as Index
import Data.Profunctor.Optic.Iso              as Iso
import Data.Profunctor.Optic.Lens             as Lens
import Data.Profunctor.Optic.Prism            as Prism
import Data.Profunctor.Optic.Grate            as Grate
import Data.Profunctor.Optic.Affine           as Affine
import Data.Profunctor.Optic.Option           as Option
import Data.Profunctor.Optic.Traversal        as Traversal
import Data.Profunctor.Optic.Fold             as Fold
import Data.Profunctor.Optic.Cotraversal      as Cotraversal
import Data.Profunctor.Optic.View             as View
import Data.Profunctor.Optic.Setter           as Setter
import Data.Profunctor.Optic.Zoom             as Zoom
import Data.Profunctor.Optic.Import hiding ((<.>), tabulate, Representable, Rep, Apply(..),sum)

import Data.Foldable as Foldable (fold, foldl')
import Data.Semigroup.Foldable as Foldable1 (fold1) 
import Data.Functor.Rep
import Data.Semiring
import Data.Group
import Data.Ring
import Data.Prd



{-
indexed :: Eq (Rep f) => Representable f => Rep f -> Lens' (f a) a
indexed
-}

--TODO push to rings
lensRep :: Eq (Rep f) => Representable f => Functor g => Rep f -> (a -> g a) -> f a -> g (f a)
lensRep i f s = setter s <$> f (getter s)
  where getter = flip index i
        setter s' b = tabulate (\j -> if i == j then b else index s' j)

grateRep :: Representable f => Functor g => (Rep f -> g a -> b) -> g (f a) -> f b
grateRep iab s = tabulate $ \i -> iab i (fmap (`index` i) s)

--TODO: get Data.Dioid.Index done and remove Foldable1
type Vector a = (Foldable1 a, Representable a)
type Unital a = (Monoid a, Semiring a)


{-
-- | Sum over multiple vectors
--
-- >>> fsum [V2 1 1, V2 3 4]
-- V2 4 5
fsum :: (Semigroup a, Semigroup (g a), Foldable1 f) => f (g a) -> g a
fsum = fold1
{-# INLINE fsum #-}
-}



infixl 6 `sum`
-- | Compute the sum of two distributive functors
--
-- >>> V2 1 2 `sum` V2 3 4
-- V2 4 6
--
-- >>> V2 1 2 <> V2 3 4
-- V2 4 6
--
-- >>> V2 (V2 1 2) (V2 3 4) <> V2 (V2 1 2) (V2 3 4)
-- V2 (V2 2 4) (V2 6 8)
--
sum :: Semigroup a => Representable f => f a -> f a -> f a
sum = liftR2 (<>)

fempty :: Monoid a => Representable f => f a
fempty = pureRep mempty

infixl 6 `diff`
-- | Compute the difference between two distributive functors.
--
-- >>> V2 4 5 `diff` V2 3 1
-- V2 1 4
--
-- >>> V2 4 5 << V2 3 1
-- V2 1 4
--
diff :: Group a => Representable f => f a -> f a -> f a
diff x y = x `sum` fmap negate y

-- | Compute the negation of a vector
--
-- >>> neg (V2 2 4)
-- V2 (-2) (-4)
neg :: (Functor f, Group a) => f a -> f a
neg = fmap negate
{-# INLINE neg #-}




-- | Outer (tensor) product of two vectors
outer :: Semiring a => Functor f => Functor g => f a -> g a -> f (g a)
outer a b = fmap (\x->fmap (><x) b) a

infixl 7 <., .>

-- | Compute the left scalar product
--
-- >>> 2 .> V2 3 4
-- V2 6 8
(.>) :: Semiring a => Functor f => a -> f a -> f a
(.>) a = fmap (a ><)
{-# INLINE (.>) #-}

-- | Compute the right scalar product
--
-- >>> V2 3 4 <. 2
-- V2 6 8
(<.) :: Semiring a => Functor f => f a -> a -> f a
f <. a = fmap (>< a) f
{-# INLINE (<.) #-}

infixl 6 <.>
--dot product
(<.>) :: Semiring a => Vector t => t a -> t a -> a
(<.>) a b = fold1 $ liftR2 (><) a b 

quadrance :: Semiring a => Vector f => f a -> a
quadrance v = v <.> v

-- | Create a unit vector.
--
-- >>> funit (indexed I21) :: V2 Int
-- V2 1 0
--
funit :: Unital a => Representable f => Optic' (->) (f a) a -> f a
funit o = set o Data.Semiring.sunit fempty

row :: Representable f => Rep f -> f c -> c
row i = flip index i

col :: Functor f => Representable g => Rep g -> f (g a) -> f a
col j m = flip index j $ distribute m

infixl 7 <#, #>, <#>

-- | Multiply a matrix on the left by a row vector.
--
-- >>> V2 1 2 #> V2 (V3 3 4 5) (V3 6 7 8)
-- V3 15 18 21
--
(#>) :: (Semiring a, Vector f, Vector g) => f a -> f (g a) -> g a
x #> y = tabulate (\j -> x <.> col j y)

-- | Multiply a matrix on the right by a column vector.
--
-- >>> V2 (V3 1 2 3) (V3 4 5 6) <# V3 7 8 9
-- V2 50 122
--
(<#) :: (Semiring a, Vector f, Vector g) => f (g a) -> g a -> f a
x <# y = tabulate (\i -> row i x <.> y)

{-
λ> V2 (V2 1 2) (V2 3 4) <#> V2 (V2 1 2) (V2 3 4) :: V2 (V2 Int)
V2 (V2 7 10) (V2 15 22)

>>> V2 (V3 1 2 3) (V3 4 5 6) <#> V3 (V2 1 2) (V2 3 4) (V2 4 5)
V2 (V2 19 25) (V2 43 58)
-}
(<#>) :: (Semiring a, Vector f, Vector g, Vector h) => f (g a) -> g (h a) -> f (h a)
(<#>) x y = getCompose $ tabulate (\(i,j) -> row i x <.> col j y)




-- | Compute the quadrance of the difference
qd :: Ring a => Vector f => f a -> f a -> a
qd f g = quadrance $ f `diff` g

-- | Linearly interpolate between two vectors.
lerp :: Ring a => Representable f => a -> f a -> f a -> f a
lerp alpha u v = (alpha .> u) `sum` (sunit << alpha) .> v
{-# INLINE lerp #-}





-- Data.Dioid.Vector
-- * Matrices
--
-- Matrices use a row-major representation.

-- | A 2x2 matrix with row-major representation
type M22 a = V2 (V2 a)
-- | A 2x3 matrix with row-major representation
type M23 a = V2 (V3 a)
{-
-- | A 2x4 matrix with row-major representation
type M24 a = V2 (V4 a)
-- | A 3x2 matrix with row-major representation
type M32 a = V3 (V2 a)
-- | A 3x3 matrix with row-major representation
type M33 a = V3 (V3 a)
-- | A 3x4 matrix with row-major representation
type M34 a = V3 (V4 a)
-- | A 4x2 matrix with row-major representation
type M42 a = V4 (V2 a)
-- | A 4x3 matrix with row-major representation
type M43 a = V4 (V3 a)
-- | A 4x4 matrix with row-major representation
type M44 a = V4 (V4 a)
-}

{-
>>> V2 (V3 1 2 3) (V3 4 5 6) <> V2 (V3 7 8 9) (V3 1 2 3)
V2 (V3 8 10 12) (V3 5 7 9)

>>> V2 (V3 1 2 3) (V3 4 5 6) << V2 (V3 7 8 9) (V3 1 2 3)
V2 (V3 (-6) (-6) (-6)) (V3 3 3 3)
-}
data V2 a = V2 !a !a deriving (Eq,Ord,Show)

instance Semigroup a => Semigroup (V2 a) where
  (<>) = zipsWith distributed (<>)

instance Monoid a => Monoid (V2 a) where
  mempty = coview distributed mempty

instance Semiring a => Semiring (V2 a) where
  (><) = zipsWith distributed (<>)

instance Group a => Group (V2 a) where
  (<<) = zipsWith distributed (<<)

instance Functor V2 where
  fmap f (V2 a b) = V2 (f a) (f b)
  {-# INLINE fmap #-}
  a <$ _ = V2 a a
  {-# INLINE (<$) #-}

instance Foldable V2 where
  foldMap f (V2 a b) = f a <> f b
  {-# INLINE foldMap #-}
  null _ = False
  length _ = 2

instance Foldable1 V2 where
  foldMap1 f (V2 a b) = f a <> f b
  {-# INLINE foldMap1 #-}

instance Distributive V2 where
  distribute f = V2 (fmap (\(V2 x _) -> x) f) (fmap (\(V2 _ y) -> y) f)
  {-# INLINE distribute #-}

data I2 = I21 | I22 deriving (Eq, Ord, Show)

instance Representable V2 where
  type Rep V2 = I2
  tabulate f = V2 (f I21) (f I22)
  {-# INLINE tabulate #-}

  index (V2 x _) I21 = x
  index (V2 _ y) I22 = y
  {-# INLINE index #-}

instance Prd I2 where
  (<~) = (<=)
  (>~) = (>=)
  pcompare = pcompareOrd

instance Minimal I2 where
  minimal = I21

instance Maximal I2 where
  maximal = I22



data V3 a = V3 !a !a !a deriving (Eq,Ord,Show)

-- | cross product
cross' :: Ring a => V3 a -> V3 a -> V3 a
cross' (V3 a b c) (V3 d e f) = V3 (b><f << c><e) (c><d << a><f) (a><e << b><d)
{-# INLINABLE cross' #-}

-- | scalar triple product
triple :: Ring a => V3 a -> V3 a -> V3 a -> a
triple a b c = a <.> (cross' b c)
{-# INLINE triple #-}

instance Semigroup a => Semigroup (V3 a) where
  (<>) = zipsWith distributed (<>)

instance Monoid a => Monoid (V3 a) where
  mempty = coview distributed mempty

instance Semiring a => Semiring (V3 a) where
  (><) = zipsWith distributed (<>)

instance Group a => Group (V3 a) where
  (<<) = zipsWith distributed (<<)

instance Functor V3 where
  fmap f (V3 a b c) = V3 (f a) (f b) (f c)
  {-# INLINE fmap #-}
  a <$ _ = V3 a a a
  {-# INLINE (<$) #-}

instance Foldable V3 where
  foldMap f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap #-}
  null _ = False
  length _ = 3

instance Foldable1 V3 where
  foldMap1 f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap1 #-}

instance Distributive V3 where
  distribute f = V3 (fmap (\(V3 x _ _) -> x) f) (fmap (\(V3 _ y _) -> y) f) (fmap (\(V3 _ _ z) -> z) f)
  {-# INLINE distribute #-}

instance Representable V3 where
  type Rep V3 = I3
  tabulate f = V3 (f I31) (f I32) (f I33)
  {-# INLINE tabulate #-}

  index (V3 x _ _) I31 = x
  index (V3 _ y _) I32 = y
  index (V3 _ _ z) I33 = z
  {-# INLINE index #-}

data I3 = I31 | I32 | I33 deriving (Eq, Ord, Show)

instance Prd I3 where
  (<~) = (<=)
  (>~) = (>=)
  pcompare = pcompareOrd

instance Minimal I3 where
  minimal = I31

instance Maximal I3 where
  maximal = I33
