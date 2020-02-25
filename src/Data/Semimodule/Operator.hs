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
{-# LANGUAGE RankNTypes               #-}

module Data.Semimodule.Operator (
  -- * Types
    type Free
  , type Basis
  , type Basis2
  , type Basis3
  -- * Vector accessors and constructors
  , dual
  , dirac
  , idx
  , elt
  , lensRep
  , grateRep
  -- * Vector arithmetic
  , (.*)
  , (!*)
  , (.#)
  , (!#)
  , (*.)
  , (*!)
  , (#.)
  , (#!)
  , inner
  , outer
  , lerp
  , quadrance
  -- * Matrix accessors and constructors
  , tran
  , elt2
  , row
  , rows
  , col
  , cols
  , diag
  , codiag
  , scalar
  , identity
  -- * Matrix arithmetic
  , (.#.)
  , (!#!)
  , trace
  , transpose
) where

import safe Control.Arrow
import safe Control.Applicative
import safe Data.Bool
import safe Data.Functor.Compose
import safe Data.Functor.Rep hiding (Co)
import safe Data.Semimodule
import safe Data.Semimodule.Algebra
import safe Data.Semimodule.Dual
import safe Data.Semiring
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe qualified Control.Monad as M

-------------------------------------------------------------------------------
-- Vector constructors & acessors
-------------------------------------------------------------------------------

-- | Take the dual of a vector.
--
-- >>> dual (V2 3 4) !% V2 1 2 :: Int
-- 11
--
dual :: FreeCounital a f => f a -> Dual a (Rep f)
dual f = Dual $ \k -> f `inner` tabulate k

-- | Dirac delta function.
--
dirac :: Eq i => Semiring a => i -> i -> a
dirac i j = bool zero one (i == j)
{-# INLINE dirac #-}

-- | Create a unit vector at an index.
--
-- >>> idx E21 :: V2 Int
-- V2 1 0
--
-- >>> idx E42 :: V4 Int
-- V4 0 1 0 0
--
idx :: Semiring a => Basis b f => b -> f a
idx i = tabulate $ dirac i
{-# INLINE idx #-}

-- | Retrieve an element of a vector.
--
-- >>> elt E21 (V2 1 2)
-- 1
--
elt :: Basis b f => b -> f a -> a
elt = flip index
{-# INLINE elt #-}

-- | Create a lens from a representable functor.
--
lensRep :: Basis b f => b -> forall g. Functor g => (a -> g a) -> f a -> g (f a) 
lensRep i f s = setter s <$> f (getter s)
  where getter = flip index i
        setter s' b = tabulate $ \j -> bool (index s' j) b (i == j)
{-# INLINE lensRep #-}

-- | Create an indexed grate from a representable functor.
--
grateRep :: Basis b f => forall g. Functor g => (b -> g a1 -> a2) -> g (f a1) -> f a2
grateRep iab s = tabulate $ \i -> iab i (fmap (`index` i) s)
{-# INLINE grateRep #-}


-------------------------------------------------------------------------------
-- Vector operations
-------------------------------------------------------------------------------

infixr 7 .#

-- | Multiply a matrix on the right by a column vector.
--
-- @ ('.#') = ('!#') . 'tran' @
--
-- >>> tran (m23 1 2 3 4 5 6) !# V3 7 8 9 :: V2 Int
-- V2 50 122
-- >>> m23 1 2 3 4 5 6 .# V3 7 8 9 :: V2 Int
-- V2 50 122
-- >>> m22 1 0 0 0 .# m23 1 2 3 4 5 6 .# V3 7 8 9 :: V2 Int
-- V2 50 0
--
(.#) :: Free f => FreeCounital a g => (f**g) a -> g a -> f a
x .# y = tabulate (\i -> row i x `inner` y)
{-# INLINE (.#) #-}

infixl 7 #.

-- | Multiply a matrix on the left by a row vector.
--
-- >>> V2 1 2 #. m23 3 4 5 6 7 8
-- V3 15 18 21
--
-- >>> V2 1 2 #. m23 3 4 5 6 7 8 #. m32 1 0 0 0 0 0 :: V2 Int
-- V2 15 0
--
(#.) :: FreeCounital a f => Free g => f a -> (f**g) a -> g a
x #. y = tabulate (\j -> x `inner` col j y)
{-# INLINE (#.) #-}

infix 6 `inner`

-- | Inner product.
--
-- This is a variant of 'Data.Semiring.xmult' restricted to free functors.
--
-- >>> V3 1 2 3 `inner` V3 1 2 3
-- 14
-- 
inner :: FreeCounital a f => f a -> f a -> a
inner x y = counit $ liftR2 (*) x y
{-# INLINE inner #-}

-- | Outer product.
--
-- >>> V2 1 1 `outer` V2 1 1
-- Compose (V2 (V2 1 1) (V2 1 1))
--
outer :: Semiring a => Free f => Free g => f a -> g a -> (f**g) a
outer x y = Compose $ fmap (\z-> fmap (*z) y) x

-- | Squared /l2/ norm of a vector.
--
quadrance :: FreeCounital a f => f a -> a
quadrance = M.join inner 
{-# INLINE quadrance #-}

-------------------------------------------------------------------------------
-- Matrix accessors and constructors
-------------------------------------------------------------------------------

-- | Lift a matrix into a linear transformation
--
-- @ ('.#') = ('!#') . 'tran' @
--
tran :: Free f => FreeCounital a g => (f**g) a -> Tran a (Rep f) (Rep g) 
tran m = Tran $ \k -> index $ m .# tabulate k

-- | Retrieve an element of a matrix.
--
-- >>> elt2 E21 E21 $ m22 1 2 3 4
-- 1
--
elt2 :: Basis2 b c f g => b -> c -> (f**g) a -> a
elt2 i j = elt i . col j
{-# INLINE elt2 #-}

-- | Retrieve a row of a matrix.
--
-- >>> row E22 $ m23 1 2 3 4 5 6
-- V3 4 5 6
--
row :: Free f => Rep f -> (f**g) a -> g a
row i = flip index i . getCompose
{-# INLINE row #-}

-- | Obtain a matrix by stacking rows.
--
-- >>> rows (V2 1 2) :: M22 Int
-- V2 (V2 1 2) (V2 1 2)
--
rows :: Free f => Free g => g a -> (f**g) a
rows g = arr snd !# g
{-# INLINE rows #-}

-- | Retrieve a column of a matrix.
--
-- >>> elt E22 . col E31 $ m23 1 2 3 4 5 6
-- 4
--
col :: Free f => Free g => Rep g -> (f**g) a -> f a
col j = flip index j . distributeRep . getCompose
{-# INLINE col #-}

-- | Obtain a matrix by stacking columns.
--
-- >>> cols (V2 1 2) :: M22 Int
-- V2 (V2 1 1) (V2 2 2)
--
cols :: Free f => Free g => f a -> (f**g) a
cols f = arr fst !# f
{-# INLINE cols #-}

-- | Obtain a < https://en.wikipedia.org/wiki/Diagonal_matrix#Scalar_matrix scalar matrix > from a scalar.
--
-- >>> scalar 4.0 :: M22 Double
-- Compose (V2 (V2 4.0 0.0) (V2 0.0 4.0))
--
scalar :: FreeCoalgebra a f => a -> (f**f) a
scalar = codiag . pureRep

-- | Obtain an identity matrix.
--
-- >>> identity :: M33 Int
-- Compose (V3 (V3 1 0 0) (V3 0 1 0) (V3 0 0 1))
--
identity :: FreeCoalgebra a f => (f**f) a
identity = scalar one
{-# INLINE identity #-}

-------------------------------------------------------------------------------
-- Matrix operators
-------------------------------------------------------------------------------


infixr 7 .#.

-- | Multiply two matrices.
--
-- >>> m22 1 2 3 4 .#. m22 1 2 3 4 :: M22 Int
-- Compose (V2 (V2 7 10) (V2 15 22))
-- 
-- >>> m23 1 2 3 4 5 6 .#. m32 1 2 3 4 4 5 :: M22 Int
-- Compose (V2 (V2 19 25) (V2 43 58))
--
(.#.) :: Free f => FreeCounital a g => Free h => (f**g) a -> (g**h) a -> (f**h) a
(.#.) x y = tabulate (\(i,j) -> row i x `inner` col j y)
{-# INLINE (.#.) #-}

-- | Trace of an endomorphism.
--
-- >>> trace $ m22 1.0 2.0 3.0 4.0
-- 5.0
--
trace :: FreeBialgebra a f => (f**f) a -> a
trace = counit . diag

-- | Transpose a matrix.
--
-- >>> transpose $ m23 1 2 3 4 5 6 :: M32 Int
-- V3 (V2 1 4) (V2 2 5) (V2 3 6)
--
transpose :: Free f => Free g => (f**g) a -> (g**f) a
transpose fg = braid !# fg
{-# INLINE transpose #-}