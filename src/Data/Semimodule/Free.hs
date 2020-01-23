{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Semimodule.Free where

import safe Data.Algebra
import safe Data.Distributive
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Functor.Rep
import safe Data.Magma
import safe Data.Group
import safe Data.Semimodule
--import safe Data.Prd hiding (zero)
import safe Data.Semiring
import safe Data.Semigroup.Foldable as Foldable1


import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe qualified Prelude as P


data V2 a = V2 !a !a deriving (Eq,Ord,Show)

{-


-- | Entry-wise vector or matrix addition.
--
-- >>> V2 (V3 1 2 3) (V3 4 5 6) <> V2 (V3 7 8 9) (V3 1 2 3)
-- V2 (V3 8 10 12) (V3 5 7 9)
--
instance Semigroup a => Semigroup (V2 a) where
  (<>) = mzipWithRep (<>)

instance Monoid a => Monoid (V2 a) where
  mempty = pureRep mempty

instance Semiring a => Semimodule a (V2 a) where
  a .# f = (a ><) <$> f

-- | Entry-wise vector or matrix multiplication.
--
-- >>> V2 (V3 1 2 3) (V3 4 5 6) >< V2 (V3 7 8 9) (V3 1 2 3)
-- V2 (V3 7 16 27) (V3 4 10 18)
--
instance Unital a => Semiring (V2 a) where
  (><) = mzipWithRep (><)
  fromBoolean = pureRep . fromBoolean

instance (Monoid a, Dioid a) => Dioid (V2 a) where
  fromNatural = pureRep . fromNatural

-- | Entry-wise vector or matrix subtraction.
--
-- >>> V2 (V3 1 2 3) (V3 4 5 6) << V2 (V3 7 8 9) (V3 1 2 3)
-- V2 (V3 (-6) (-6) (-6)) (V3 3 3 3)
--
instance Group a => Group (V2 a) where
  (<<) = mzipWithRep (<<)
-}

instance Functor V2 where
  fmap f (V2 a b) = V2 (f a) (f b)
  {-# INLINE fmap #-}
  a <$ _ = V2 a a
  {-# INLINE (<$) #-}

instance Foldable V2 where
  foldMap f (V2 a b) = f a <> f b
  {-# INLINE foldMap #-}
  null _ = False
  length _ = two

instance Foldable1 V2 where
  foldMap1 f (V2 a b) = f a <> f b
  {-# INLINE foldMap1 #-}

instance Distributive V2 where
  distribute f = V2 (fmap (\(V2 x _) -> x) f) (fmap (\(V2 _ y) -> y) f)
  {-# INLINE distribute #-}

instance Representable V2 where
  type Rep V2 = I2
  tabulate f = V2 (f I21) (f I22)
  {-# INLINE tabulate #-}

  index (V2 x _) I21 = x
  index (V2 _ y) I22 = y
  {-# INLINE index #-}


data I2 = I21 | I22 deriving (Eq, Ord, Show)

--instance Semigroup I2 where (<>) = P.error "TODO"

type Dim2 f = (Representable f, Rep f ~ I2)

i2 :: Dim2 f => a -> a -> f a
i2 a b = tabulate f where
  f I21 = a
  f I22 = b


type HyperbolicBasis = I2


-- @ (x+jy) * (u+jv) = (xu+yv) + j(xv+yu) @
-- >>> (V2 1 2) >< (V2 1 2)
-- V2 5 4
-- https://en.wikipedia.org/wiki/Split-complex_number
--instance Semimodule r HyperbolicBasis => Algebra r HyperbolicBasis where
instance Semiring r => Algebra r HyperbolicBasis where
  multiplyWith f = f' where
    i21 = f I21 I21 + f I22 I22
    i22 = f I21 I22 + f I22 I21
    f' I21 = i21
    f' I22 = i22


-- http://hackage.haskell.org/package/algebra-4.3.1/docs/src/Numeric-Coalgebra-Hyperbolic.html#line-25
{-


-- | the trivial diagonal algebra
instance Semiring k => Algebra k HyperBasis where
  multiplyWith f = f' where
    fs = f Sinh Sinh
    fc = f Cosh Cosh
    f' Sinh = fs
    f' Cosh = fc

instance Semiring k => UnitalAlgebra k HyperBasis where
  unital = const

-- | the hyperbolic trigonometric coalgebra
instance (Commutative k, Semiring k) => Coalgebra k HyperBasis where
  comultiplyWith f = f' where
     fs = f Sinh
     fc = f Cosh
     f' Sinh Sinh = fc
     f' Sinh Cosh = fs 
     f' Cosh Sinh = fs
     f' Cosh Cosh = fc

instance (Commutative k, Semiring k) => CounitalCoalgebra k HyperBasis where
  counital f = f Cosh

instance (Commutative k, Semiring k) => Bialgebra k HyperBasis

instance (Commutative k, Group k, InvolutiveSemiring k) => InvolutiveAlgebra k HyperBasis where
  inv f = f' where
    afc = adjoint (f Cosh)
    nfs = negate (f Sinh)
    f' Cosh = afc
    f' Sinh = nfs

instance (Commutative k, Group k, InvolutiveSemiring k) => InvolutiveCoalgebra k HyperBasis where

-}



-- | Scalar triple product.
--
triple :: Ring a => V3 a -> V3 a -> V3 a -> a
triple a b c = a .*. b >< c
{-# INLINE triple #-}

data V3 a = V3 !a !a !a deriving (Eq,Ord,Show)

instance (Additive-Semigroup) a => Semigroup (V3 a) where
  (<>) = mzipWithRep (+)

instance (Additive-Monoid) a => Monoid (V3 a) where
  mempty = pureRep zero

instance (Additive-Group) a => Magma (V3 a) where
  (<<) = mzipWithRep (-)

instance (Additive-Group) a => Quasigroup (V3 a)

instance (Additive-Group) a => Loop (V3 a)

instance (Additive-Group) a => Group (V3 a)

--instance Semiring a => Semimodule a (V3 a) where 
--  a *. f = (a *) <$> f

instance Functor V3 where
  fmap f (V3 a b c) = V3 (f a) (f b) (f c)
  {-# INLINE fmap #-}
  a <$ _ = V3 a a a
  {-# INLINE (<$) #-}

instance Foldable V3 where
  foldMap f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap #-}
  null _ = False
  --length _ = 3

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


data V4 a = V4 !a !a !a !a deriving (Eq,Ord,Show)

type Dim4 f = (Representable f, Rep f ~ I4)

i4 :: Dim4 f => a -> a -> a -> a -> f a
i4 a b c d = tabulate f where
  f I41 = a
  f I42 = b
  f I43 = c
  f I44 = d

{-
instance Semigroup a => Semigroup (V4 a) where
  (<>) = mzipWithRep (<>)

instance Monoid a => Monoid (V4 a) where
  mempty = pureRep mempty

instance Semiring a => Semimodule a (V4 a) where
  a .# f = (a ><) <$> f

instance Unital a => Semiring (V4 a) where
  (><) = mzipWithRep (><)
  fromBoolean = pureRep . fromBoolean


instance Group a => Group (V4 a) where
  (<<) = mzipWithRep (<<)
-}
instance Functor V4 where
  fmap f (V4 a b c d) = V4 (f a) (f b) (f c) (f d)
  {-# INLINE fmap #-}
  a <$ _ = V4 a a a a
  {-# INLINE (<$) #-}

instance Foldable V4 where
  foldMap f (V4 a b c d) = f a <> f b <> f c <> f d
  {-# INLINE foldMap #-}
  null _ = False
  length _ = two + two

instance Foldable1 V4 where
  foldMap1 f (V4 a b c d) = f a <> f b <> f c <> f d
  {-# INLINE foldMap1 #-}

instance Distributive V4 where
  distribute f = V4 (fmap (\(V4 x _ _ _) -> x) f) (fmap (\(V4 _ y _ _) -> y) f) (fmap (\(V4 _ _ z _) -> z) f) (fmap (\(V4 _ _ _ w) -> w) f)
  {-# INLINE distribute #-}

instance Representable V4 where
  type Rep V4 = I4
  tabulate f = V4 (f I41) (f I42) (f I43) (f I44)
  {-# INLINE tabulate #-}

  index (V4 x _ _ _) I41 = x
  index (V4 _ y _ _) I42 = y
  index (V4 _ _ z _) I43 = z
  index (V4 _ _ _ w) I44 = w
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- I3
-------------------------------------------------------------------------------

data I3 = I31 | I32 | I33 deriving (Eq, Ord, Show)


type Dim3 f = (Representable f, Rep f ~ I3)

i3 :: Dim3 f => a -> a -> a -> f a
i3 a b c = tabulate f where
  f I31 = a
  f I32 = b
  f I33 = c

instance Ring r => Algebra r I3 where
  multiplyWith f = f' where
    i31 = f I32 I33 - f I33 I32
    i32 = f I33 I31 - f I31 I33
    i33 = f I31 I32 - f I32 I31 
    f' I31 = i31
    f' I32 = i32
    f' I33 = i33

type QuaternionBasis = Maybe I3

instance Ring r => Algebra r QuaternionBasis where
  multiplyWith f = maybe fe f' where
    e = Nothing
    i = Just I31
    j = Just I32
    k = Just I33
    fe = f e e - (f i i + f j j + f k k)
    fi = f e i + f i e + (f j k - f k j)
    fj = f e j + f j e + (f k i - f i k)
    fk = f e k + f k e + (f i j - f j i)
    f' I31 = fi
    f' I32 = fj
    f' I33 = fk

instance Ring r => Unital r QuaternionBasis where
  unitWith x Nothing = x 
  unitWith _ _ = zero

instance Ring r => Composition r QuaternionBasis where
  conjugateWith f = maybe fe f' where
    fe = f Nothing
    f' I31 = negate . f $ Just I31
    f' I32 = negate . f $ Just I32
    f' I33 = negate . f $ Just I33

data I4 = I41 | I42 | I43 | I44 deriving (Eq, Ord, Show)


