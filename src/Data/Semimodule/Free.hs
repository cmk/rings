{-# LANGUAGE Safe                       #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ViewPatterns               #-}
-- | < https://ncatlab.org/nlab/show/free+module >
module Data.Semimodule.Free (
  -- * Types
    type (**), type (++)
  , type Free
  , type FreeModule
  , type FreeSemimodule
  , type FreeAlgebra
  , type FreeUnital
  , type FreeCoalgebra
  , type FreeCounital
  , type FreeBialgebra
  -- * Coltor accessors and constructors
  , at
  , unit
  , counit
  , indexed
  , tabulated
  -- * Coltor operations
  , (.*)
  , (*.)
  , (/^)
  , (^/)
  , (!*!)
  , lerp
  , inner
  , innerR
  , innerL
  , outer
  , quadrance
  , projectL
  , projectR
  -- * Matrix accessors and constructors
  , idx2
  , row
  , fromRows
  , fromRow
  , col
  , fromCols
  , fromCol
  , diag
  , codiag
  , scalar
  , identity
  , transform
  , Transform(..)
  -- * Matrix operations
  , (!#)
  , (#!)
  , (!#!)
  , lcomp
  , rcomp
  , dicomp
  , trace
  , transpose
) where

import safe Control.Category
import safe Data.Bool
import safe Data.Functor.Apply
import safe Data.Functor.Compose
import safe Data.Functor.Rep hiding (tabulated)
import safe Data.Profunctor.Composition (eta)
import safe Data.Ring
import safe Data.Semimodule
import safe Data.Semimodule.Algebra
import safe Data.Semimodule.Transform
import safe Prelude hiding (Num(..), Fractional(..), (.), id, init, negate, sum, product)
import safe qualified Control.Monad as M

-- >>> :set -XDataKinds
-- >>> import Data.Coltor.Sized



type FreeModule a f = (Free f, Bimodule a a (f a))

type FreeSemimodule a f = (Free f, Bisemimodule a a (f a))

-- | An algebra over a free module /f/^
--
-- Note that this is distinct from a < https://en.wikipedia.org/wiki/Free_algebra free algebra >.
--
type FreeAlgebra a f = (FreeSemimodule a f, Algebra a (Rep f))

-- | A unital algebra over a free semimodule /f/^
--
type FreeUnital a f = (FreeAlgebra a f, Unital a (Rep f))

-- | A coalgebra over a free semimodule /f/^
--
type FreeCoalgebra a f = (FreeSemimodule a f, Coalgebra a (Rep f))

-- | A counital coalgebra over a free semimodule /f/^
--
type FreeCounital a f = (FreeCoalgebra a f, Counital a (Rep f))

-- | A bialgebra over a free semimodule /f/^
--
type FreeBialgebra a f = (FreeAlgebra a f, FreeCoalgebra a f, Bialgebra a (Rep f))

-------------------------------------------------------------------------------
-- Coltors & Rowtors
-------------------------------------------------------------------------------

-- | Create a unit vector at an index.
--
-- >>> i = 4 :: Finite 5
-- >>> at i 1 :: Coltor 5 Double
-- Coltor [0.0,0.0,0.0,0.0,1.0]
-- 
-- >>> at E21 1 :: V2 Int
-- V2 1 0
-- >>> at E42 1 :: V4 Int
-- V4 0 1 0 0
--
at :: (Semiring a, Free f, Eq (Rep f)) => Rep f -> a -> f a
at i x = tabulate $ \j -> bool zero x (i == j)
{-# INLINE at #-}

-- | Retrieve the coefficient of a basis element
--
-- >>> idx E21 (V2 1 2)
-- 1
--
idx :: Free f => Rep f -> f a -> a
idx = flip index
{-# INLINE idx #-}

-- | Insert an element into an algebra.
--
-- When the algebra is trivial this is equal to 'pureRep'.
--
-- >>> V4 1 2 3 4 !*! unit two :: V4 Int
-- V4 2 4 6 8
--
unit :: FreeUnital a f => a -> f a
unit = tabulate . unital

-- | Reduce a coalgebra over a free semimodule.
--
-- /Note/: for the stock 'Counital' instances (e.g. 'E2', 'Finite', etc) this is summation.
--
-- >>> x = fromTuple (7, 4) :: Coltor 2 Int
-- >>> counit x
-- 11
-- 
counit :: FreeCounital a f => f a -> a
counit = counital . index

-- | Obtain a vector from an etaay of coefficients and a basis.
--
indexed :: FreeUnital a f => f a -> Col a (Rep f)
indexed = Col . index

-- | Obtain a covector from an etaay of coefficients and a basis.
--
-- >>> x = fromTuple (7, 4) :: Coltor 2 Int
-- >>> y = fromTuple (1, 2) :: Coltor 2 Int
-- >>> tabulated x !* index y :: Int
-- >>> tabulated (V2 7 4) !* index (V2 1 2) :: Int
-- 11
--
tabulated :: FreeCounital a f => f a -> Row a (Rep f)
tabulated f = Row $ \k -> f `inner` tabulate k

-------------------------------------------------------------------------------
-- Coltor operations
-------------------------------------------------------------------------------

infixl 7 !*!

-- | Multiplication operator on an algebra over a free semimodule.
--
-- >>> E22 & (index $ V2 1 2) !*! (index $ V2 7 4)
-- 8
--
-- /Caution/ in general '!*!' needn't be commutative, nor associative.
--
(!*!) :: FreeAlgebra a f => f a -> f a -> f a
(!*!) x y = tabulate $ joined (\i j -> index x i * index y j)

infix 6 `inner`, `innerL`, `innerR`

-- | Inner product.
--
-- >>> 1 :+ 2 `inner` 3 :+ 4 
-- 11
-- 
-- See also 'Data.Semimodule.Transform.functional'.
--
inner :: FreeCounital a f => f a -> f a -> a
inner x y = counit $ liftR2 (*) x y
{-# INLINE inner #-}

-- | Apply a co-vector to a vector from the left.
--
innerL :: Free f => Row a (Rep f) -> f a -> a 
innerL (runRow -> r) = r . index 

-- | Apply a co-vector to a vector from the right.
--
innerR :: Free f => f a -> Row a (Rep f) -> a
innerR = flip innerL

infix 6 `outer`
-- | Outer product.
--
-- >>> V2 1 1 `outer` V2 1 1
-- Compose (V2 (V2 1 1) (V2 1 1))
--
outer :: (Semiring a, Free f, Free g) => f a -> g a -> (f**g) a
outer x y = Compose $ fmap (\z-> fmap (*z) y) x
{-# INLINE outer #-}

-- | Squared /l2/ norm of a vector.
--
quadrance :: FreeCounital a f => f a -> a
quadrance = M.join inner 
{-# INLINE quadrance #-}

-- | Project onto the left-hand component of a direct sum.
--
projectL :: (Free f, Free g) => (f++g) a -> f a
projectL fg = eta Left .# fg
{-# INLINE projectL #-}

-- | Project onto the right-hand component of a direct sum.
--
projectR :: (Free f, Free g) => (f++g) a -> g a
projectR fg = eta Right .# fg
{-# INLINE projectR #-}

-------------------------------------------------------------------------------
-- Matrix accessors and constructors
-------------------------------------------------------------------------------

-- | Obtain a linear transformation from a matrix.
--
-- @ ('!#') = ('.#') . 'transform' @
--
transform :: (Free f, FreeCounital a g) => (f**g) a -> Transform a (Rep f) (Rep g) 
transform x = Transform $ \k -> index (x !# tabulate k)

-- | Retrieve an element of a matrix.
--
idx2 :: (Free f, Free g) => Rep f -> Rep g -> (f**g) a -> a
idx2 i j = idx i . col j
{-# INLINE idx2 #-}

-- | Retrieve a row of a matrix.
--
row :: Free f => Rep f -> (f**g) a -> g a
row i = idx i . getCompose
{-# INLINE row #-}

-- | Retrieve a column of a matrix.
--
col :: (Free f, Free g) => Rep g -> (f**g) a -> f a
col j = idx j . distributeRep . getCompose
{-# INLINE col #-}

-- | Obtain a matrix by repeating a row.
--
fromRow :: (Free f, Free g) => g a -> (f**g) a
fromRow g = eta snd .# g
{-# INLINE fromRow #-}

-- | Obtain a matrix from a collection of rows.
--
fromRows :: (Free f, Free g) => f (g a) -> (f**g) a
fromRows = Compose
{-# INLINE fromRows #-}

-- | Obtain a matrix by repeating a column.
--
fromCol :: (Free f, Free g) => f a -> (f**g) a
fromCol f = eta fst .# f
{-# INLINE fromCol #-}

-- | Obtain a matrix from a collection of columns.
--
fromCols :: (Free f, Free g) => g (f a) -> (f**g) a
fromCols = transpose . Compose

-- | Obtain a vector from a tensor.
--
-- @ 'diag' f = 'diagonal' '.#' f @
--
-- When the algebra is trivial we have:
--
-- @ 'diag' f = 'tabulate' $ 'joined' $ 'index' . 'index' ('getCompose' f) @
--
diag :: FreeAlgebra a f => (f**f) a -> f a
diag f = diagonal .# f

-- | Obtain a tensor from a vector.
--
-- @ 'codiag' f = 'codiagonal' '.#' f @
--
-- When the coalgebra is trivial we have:
--
-- @ 'codiag' = 'flip' 'bindRep' 'id' '.' 'getCompose' @
--
codiag :: FreeCoalgebra a f => f a -> (f**f) a
codiag f = codiagonal .# f

-- | Obtain a < https://en.wikipedia.org/wiki/Diagonal_matrix#Scalar_matrix scalar matrix > from a scalar.
--
scalar :: FreeCoalgebra a f => a -> (f**f) a
scalar = codiag . pureRep

-- | The identity matrix.
--
identity :: FreeCoalgebra a f => (f**f) a
identity = scalar one
{-# INLINE identity #-}

-------------------------------------------------------------------------------
-- Matrix operators
-------------------------------------------------------------------------------

infixr 7 !#

-- | Multiply a matrix on the right by a column vector.
--
-- @ ('!#') = ('.#') . 'transform' @
--
(!#) :: (Free f, FreeCounital a g) => (f**g) a -> g a -> f a
x !# y = tabulate (\i -> row i x `inner` y)
{-# INLINE (!#) #-}

infixl 7 #!

-- | Multiply a matrix on the left by a row vector.
--
(#!) :: (Free g, FreeCounital a f) => f a -> (f**g) a -> g a
x #! y = tabulate (\j -> x `inner` col j y)
{-# INLINE (#!) #-}

infixr 7 !#!

-- | Multiply two matrices.
--
(!#!) :: (Free f, Free h, FreeCounital a g) => (f**g) a -> (g**h) a -> (f**h) a
(!#!) x y = tabulate (\(i,j) -> row i x `inner` col j y)
{-# INLINE (!#!) #-}

-- | Trace of an endomorphism.
--
trace :: FreeBialgebra a f => (f**f) a -> a
trace = counit . diag
{-# INLINE trace #-}

-- | Transpose a matrix.
--
transpose :: (Free f, Free g) => (f**g) a -> (g**f) a
transpose fg = braid .# fg
{-# INLINE transpose #-}
