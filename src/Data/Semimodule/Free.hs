{-# LANGUAGE CPP                        #-}
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
  -- * Vector accessors and constructors
  , at
  , unit
  , counit
  , indexed
  , tabulated
  -- * Vector operations
  , (.*)
  , (*.)
  , (/.)
  , (./)
  , (.*.)
  , lerp
  , inner
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
  , (.#)
  , (#.)
  , (.#.)
  , compl
  , compr
  , complr
  , trace
  , transpose
) where

import Control.Arrow
import Control.Applicative
import Control.Category (Category, (<<<), (>>>))
import Control.Monad (MonadPlus(..))
import Data.Bool
import Data.Functor.Apply
import Data.Functor.Product
import Data.Functor.Compose
import Data.Functor.Contravariant (Contravariant(..))
import Data.Functor.Rep hiding (tabulated)
import Data.Ring
import Data.Semiring
import Data.Semimodule
import Data.Semimodule.Algebra
import Data.Semimodule.Transform
import Prelude hiding (Num(..), Fractional(..), init, negate, sum, product)
import qualified Control.Category as C
import qualified Control.Monad as M
import qualified Data.Profunctor.Rep as PR

-- >>> :set -XDataKinds
-- >>> import Data.Vector.Sized

infixr 1 ++

-- | A direct sum.
--
type (f ++ g) = Product f g

infixr 2 **

-- | A tensor product.
--
type (f ** g) = Compose f g

type FreeModule a f = (Free f, Bimodule a a (f a))

type FreeSemimodule a f = (Free f, Bisemimodule a a (f a))

-- | An algebra over a free module /f/.
--
-- Note that this is distinct from a < https://en.wikipedia.org/wiki/Free_algebra free algebra >.
--
type FreeAlgebra a f = (FreeSemimodule a f, Algebra a (Rep f))

-- | A unital algebra over a free semimodule /f/.
--
type FreeUnital a f = (FreeAlgebra a f, Unital a (Rep f))

-- | A coalgebra over a free semimodule /f/.
--
type FreeCoalgebra a f = (FreeSemimodule a f, Coalgebra a (Rep f))

-- | A counital coalgebra over a free semimodule /f/.
--
type FreeCounital a f = (FreeCoalgebra a f, Counital a (Rep f))

-- | A bialgebra over a free semimodule /f/.
--
type FreeBialgebra a f = (FreeAlgebra a f, FreeCoalgebra a f, Bialgebra a (Rep f))

-------------------------------------------------------------------------------
-- Vectors & Covectors
-------------------------------------------------------------------------------

-- | Create a unit vector at an index.
--
-- >>> i = 4 :: Finite 5
-- >>> at i 1 :: Vector 5 Double
-- Vector [0.0,0.0,0.0,0.0,1.0]
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
-- >>> V4 1 2 3 4 .*. unit two :: V4 Int
-- V4 2 4 6 8
--
unit :: FreeUnital a f => a -> f a
unit = tabulate . unital

-- | Reduce a coalgebra over a free semimodule.
--
-- /Note/: for the stock 'Counital' instances (e.g. 'E2', 'Finite', etc) this is summation.
--
-- >>> x = fromTuple (7, 4) :: Vector 2 Int
-- >>> counit x
-- 11
-- 
counit :: FreeCounital a f => f a -> a
counit = counital . index

-- | Obtain a vector from an array of coefficients and a basis.
--
indexed :: FreeUnital a f => f a -> Vec a (Rep f)
indexed = Vec . index

-- | Obtain a covector from an array of coefficients and a basis.
--
-- >>> x = fromTuple (7, 4) :: Vector 2 Int
-- >>> y = fromTuple (1, 2) :: Vector 2 Int
-- >>> tabulated x !* index y :: Int
-- >>> tabulated (V2 7 4) !* index (V2 1 2) :: Int
-- 11
--
tabulated :: FreeCounital a f => f a -> Covec a (Rep f)
tabulated f = Covec $ \k -> f `inner` tabulate k

-------------------------------------------------------------------------------
-- Vector operations
-------------------------------------------------------------------------------

infixr 7 /.
-- | Right-divide a vector by a scalar (on the left).
--
(/.) :: (Semifield a, Free f) => a -> f a -> f a
a /. f = (/ a) <$> f

infixl 7 ./
-- | Right-divide a vector by a scalar.
--
(./) :: (Semifield a, Free f) => f a -> a -> f a
(./) = flip (/.)

infixl 7 .*.
-- | Multiplication operator on an algebra over a free semimodule.
--
-- > (.*.) :: Vec a b -> Vec a b -> Vec a b
--
-- >>> E22 & (index $ V2 1 2) .*. (index $ V2 7 4)
-- 8
--
-- /Caution/ in general '.*.' needn't be commutative, nor associative.
--
(.*.) :: FreeAlgebra a f => f a -> f a -> f a
(.*.) x y = tabulate $ joined (\i j -> index x i * index y j)

infix 6 `inner`
-- | Inner product.
--
-- >>> V3 1 2 3 `inner` V3 1 2 3
-- 14
-- 
inner :: FreeCounital a f => f a -> f a -> a
inner x y = counit $ liftR2 (*) x y
{-# INLINE inner #-}

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
projectL fg = arr Left !# fg
{-# INLINE projectL #-}

-- | Project onto the right-hand component of a direct sum.
--
projectR :: (Free f, Free g) => (f++g) a -> g a
projectR fg = arr Right !# fg
{-# INLINE projectR #-}

-------------------------------------------------------------------------------
-- Matrix accessors and constructors
-------------------------------------------------------------------------------

-- | Obtain a linear transformation from a matrix.
--
-- @ ('.#') = ('!#') . 'transform' @
--
transform :: (Free f, FreeCounital a g) => (f**g) a -> Transform a (Rep f) (Rep g) 
transform x = Transform $ \k -> index (x .# tabulate k)

-- | Retrieve an element of a matrix.
--
-- >>> idx2 E21 E21 $ m22 1 2 3 4
-- 1
--
idx2 :: (Free f, Free g) => Rep f -> Rep g -> (f**g) a -> a
idx2 i j = idx i . col j
{-# INLINE idx2 #-}

-- | Retrieve a row of a matrix.
--
-- >>> row E22 $ m23 1 2 3 4 5 6
-- V3 4 5 6
--
row :: Free f => Rep f -> (f**g) a -> g a
row i = idx i . getCompose
{-# INLINE row #-}

-- | Retrieve a column of a matrix.
--
-- >>> idx E22 . col E31 $ m23 1 2 3 4 5 6
-- 4
--
col :: (Free f, Free g) => Rep g -> (f**g) a -> f a
col j = idx j . distributeRep . getCompose
{-# INLINE col #-}

-- | Obtain a matrix by repeating a row.
--
-- >>> fromRows (V2 1 2) :: M22 Int
-- V2 (V2 1 2) (V2 1 2)
--
fromRow :: (Free f, Free g) => g a -> (f**g) a
fromRow g = arr snd !# g
{-# INLINE fromRow #-}

-- | Obtain a matrix from a collection of fromRows.
--
fromRows :: (Free f, Free g) => f (g a) -> (f**g) a
fromRows = Compose
{-# INLINE fromRows #-}

-- | Obtain a matrix by repeating a column.
--
-- >>> fromCols (V2 1 2) :: M22 Int
-- V2 (V2 1 1) (V2 2 2)
--
fromCol :: (Free f, Free g) => f a -> (f**g) a
fromCol f = arr fst !# f
{-# INLINE fromCol #-}

-- | Obtain a matrix from a collection of columns.
--
fromCols :: (Free f, Free g) => g (f a) -> (f**g) a
fromCols = transpose . Compose

-- | Obtain a vector from a tensor.
--
-- When the algebra is trivial we have:
--
-- @ 'diag' f = 'tabulate' $ 'joined' ('index' . 'index' ('getCompose' f)) @
--
-- >>> diag $ m22 1.0 2.0 3.0 4.0
-- V2 1.0 4.0
--
diag :: FreeAlgebra a f => (f**f) a -> f a
diag f = diagonal !# f

-- | Obtain a tensor from a vector.
--
-- When the coalgebra is trivial we have:
--
-- @ 'codiag' = 'flip' 'bindRep' 'id' '.' 'getCompose' @
--
codiag :: FreeCoalgebra a f => f a -> (f**f) a
codiag f = codiagonal !# f

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

infixr 7 .#

-- | Multiply a matrix on the right by a column vector.
--
-- @ ('.#') = ('!#') . 'transform' @
--
-- >>> transform (m23 1 2 3 4 5 6) !# V3 7 8 9 :: V2 Int
-- V2 50 122
-- >>> m23 1 2 3 4 5 6 .# V3 7 8 9 :: V2 Int
-- V2 50 122
-- >>> m22 1 0 0 0 .# m23 1 2 3 4 5 6 .# V3 7 8 9 :: V2 Int
-- V2 50 0
--
(.#) :: (Free f, FreeCounital a g) => (f**g) a -> g a -> f a
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
(#.) :: (Free g, FreeCounital a f) => f a -> (f**g) a -> g a
x #. y = tabulate (\j -> x `inner` col j y)
{-# INLINE (#.) #-}

infixr 7 .#.

-- | Multiply two matrices.
--
-- >>> m22 1 2 3 4 .#. m22 1 2 3 4 :: M22 Int
-- Compose (V2 (V2 7 10) (V2 15 22))
-- 
-- >>> m23 1 2 3 4 5 6 .#. m32 1 2 3 4 4 5 :: M22 Int
-- Compose (V2 (V2 19 25) (V2 43 58))
--
(.#.) :: (Free f, Free h, FreeCounital a g) => (f**g) a -> (g**h) a -> (f**h) a
(.#.) x y = tabulate (\(i,j) -> row i x `inner` col j y)
{-# INLINE (.#.) #-}

-- | Left (post) composition with a linear transformation.
--
compl :: (Free f1, Free f2, Free g) => Transform a (Rep f1) (Rep f2) -> (f2**g) a -> (f1**g) a
compl t fg = first t !# fg

-- | Right (pre) composition with a linear transformation.
--
compr :: (Free f, Free g1, Free g2) => Transform a (Rep g1) (Rep g2) -> (f**g2) a -> (f**g1) a
compr t fg = second t !# fg

-- | Left and right composition with a linear transformation.
--
-- @ f *** g !# v = 'compl' f '>>>' 'compr' g @
--
complr :: (Free f1, Free f2, Free g1, Free g2) => Transform a (Rep f1) (Rep f2) -> Transform a (Rep g1) (Rep g2) -> (f2**g2) a -> (f1**g1) a
complr t1 t2 fg = (t1 *** t2) !# fg

-- | Trace of an endomorphism.
--
-- >>> trace $ m22 1.0 2.0 3.0 4.0
-- 5.0
--
trace :: FreeBialgebra a f => (f**f) a -> a
trace = counit . diag
{-# INLINE trace #-}

-- | Transpose a matrix.
--
-- >>> transpose $ m23 1 2 3 4 5 6 :: M32 Int
-- V3 (V2 1 4) (V2 2 5) (V2 3 6)
--
transpose :: (Free f, Free g) => (f**g) a -> (g**f) a
transpose fg = braid !# fg
{-# INLINE transpose #-}
