{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE Safe #-}

module Data.Semimodule.V2 (
    V2(..)
  , type Dim2
  , I2(..)
  , i2
) where

import safe Data.Algebra
--import safe Data.Dioid
import safe Data.Distributive
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Functor.Rep
import safe Data.Group
import safe Data.Semimodule
import safe Data.Semiring
import safe Data.Semigroup.Foldable as Foldable1

import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative
import safe Prelude hiding (Num(..), Fractional(..), sum, product)

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
  length _ = 2

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


