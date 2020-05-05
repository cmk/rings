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

module Data.Semiring.Free (
  -- * Types
    type Free
  , type FreeModule
  , type FreeSemimodule
  , type FreeAlgebra
  , type FreeUnital
  , type FreeCoalgebra
  , type FreeCounital
  , type FreeBialgebra
  -- * Vectors
  , Vec(..)
  , vec
  , init
  , join
  , vmap
  , augment
  -- * Covectors
  , Cov(..)
  , cov
  , images
  , coinit
  , cojoin
  , cmap
  , comult
  -- * Linear transformations
  , Mat(..)
  , End 
  , mat
  , fin
  , image
  , invmap
  , initial
  , coinitial
  , diagonal
  , codiagonal
  , braid
  , cobraid 
  , split
  , cosplit
  , convolve
  -- * Vector accessors and constructors
  , exl
  , exr
  , elt
  , unit
  , unit'
  , counit
  , dirac
  -- * Vector operators
  , (!*)
  , (*!)
  , (.*)
  , (*.)
  --, (/.)
 -- , (\.)
 -- , (./)
 -- , (.\)
  , (.*.)
  , (.+.)
  , lerp
  , inner
  , outer
  , quadrance
  -- * Matrix accessors and constructors
  , elt2
  , row
  , rows
  , col
  , cols
  , diag
  , codiag
  , scalar
  , identity
  -- * Matrix operators
  , (!#)
  , (#!)
  , (.#)
  , (#.)
  , (.#.)
  , compl
  , compr
  , complr
  , trace
  , transpose
) where

import Control.Applicative
import Control.Arrow
import Control.Category (Category, (<<<), (>>>))
import Control.Monad (MonadPlus(..))
import Data.Algebra
import Data.Bool
import Data.Connection (Conn(..))
import Data.Finite (Finite, finites)
import Data.Foldable (foldl')
import Data.Functor.Apply
import Data.Functor.Compose
import Data.Functor.Contravariant (Contravariant(..))
import Data.Functor.Rep
import Data.Group
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Semiring
import Data.Semifield
import Data.Tuple (swap)
import GHC.TypeNats (KnownNat(..))
import Prelude hiding (Num(..), Fractional(..), init, negate, sum, product)
import qualified Control.Category as C
import qualified Control.Monad as M
import qualified Data.Profunctor.Rep as PR

-- >>> :set -XDataKinds
-- >>> import Data.Vector.Sized


type Free = Representable

--type FreeModule f a = (Ring a, Free f, Group (f a))

--type FreeSemimodule f a = (Semiring a, Free f, Monoid (f a))

type FreeModule f a = (Ring a, Free f)

type FreeSemimodule f a = (Semiring a, Free f)
-- | An algebra over a free module /f/.
--
-- Note that this is distinct from a < https://en.wikipedia.org/wiki/Free_algebra free algebra >.
--
type FreeAlgebra f a = (FreeSemimodule f a, Algebra a (Rep f))

-- | A unital algebra over a free semimodule /f/.
--
type FreeUnital f a = (FreeAlgebra f a, Unital a (Rep f))

-- | A coalgebra over a free semimodule /f/.
--
type FreeCoalgebra f a = (FreeSemimodule f a, Coalgebra a (Rep f))
-- | A counital coalgebra over a free semimodule /f/.
--
type FreeCounital f a = (FreeCoalgebra f a, Counital a (Rep f))

-- | A bialgebra over a free semimodule /f/.
--
type FreeBialgebra f a = (FreeAlgebra f a, FreeCoalgebra f a, Bialgebra a (Rep f))

-------------------------------------------------------------------------------
-- Vectors
-------------------------------------------------------------------------------

--infixr 3 `runVec`

--runVec = id

-- | A vector in a vector space or free semimodule.
--
-- Equivalent to < https://hackage.haskell.org/package/base/docs/Data-Functor-Contravariant.html#t:Op Op >.
--
-- Vectors transform contravariantly as f aunction of their bases.
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
type Vec a b = b -> a

-- | Obtain a vector from an array of coefficients and a basis.
--
vec :: Free f => f a -> Vec a (Rep f)
vec = index

-- | Obtain a vector from the unit of a unital algebra.
--
-- @
-- 'init' a = 'vmap' 'initial' ('Vec' $ \_ -> a)
-- @
--
init :: Unital a b => a -> Vec a b
init = unital

-- | Obtain a vector from a vector on the tensor product space.
--
join :: Algebra a b => Vec a (b, b) -> Vec a b
join = vmap diagonal

-- | Use a linear transformation to map over a vector space.
--
-- Note that the basis transforms < https://en.wikipedia.org/wiki/Covariant_transformation#Contravariant_transformation > contravariantly.
--
vmap :: Mat a b c -> Vec a c -> Vec a b
vmap = vmap

-- | The < https://en.wikipedia.org/wiki/Augmentation_(algebra) augmentation > ring homomorphism.
--
augment :: Semiring a => Mat a b c -> Vec a b
augment l = l !# const one

-------------------------------------------------------------------------------
-- Covectors
-------------------------------------------------------------------------------


infixr 3 `runCov`

-- | Linear functionals on a free semimodule.
--
-- @ 
-- f '!*' (x '+' y) = (f '!*' x) '+' (f '!*' y)
-- f '!*' (x '.*' a) = a '*' (f '!*' x)
-- @
--
-- /Caution/: You must ensure these laws hold when using the default constructor.
--
-- Co-vectors transform covariantly as f aunction of their bases.
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
newtype Covec a c = Covec { runCovec :: Vec a c -> a }

-- | Obtain a covector from an array of coefficients and a basis.
--
-- >>> x = fromTuple (7, 4) :: Vector 2 Int
-- >>> y = fromTuple (1, 2) :: Vector 2 Int
-- >>> cov x !* vec y :: Int
-- >>> cov (V2 7 4) !* vec (V2 1 2) :: Int
-- 11
--
cov :: FreeCounital f a => f a -> Covec a (Rep f)
cov f = Covec $ \k -> f `inner` tabulate k

-- | Obtain a covector from a linear combination of basis elements.
--
-- >>> images [(2, E31),(3, E32)] !* vec (V3 1 1 1) :: Int
-- 5
--
images :: Semiring a => Foldable f => f (a, c) -> Covec a c
images f = Covec $ \k -> foldl' (\acc (a, c) -> acc + a * k c) zero f 

-- | Obtain a covector from the counit of a counital coalgebra.
--
-- @
-- 'coinit' = 'cmap' 'coinitial' ('Cov' $ \f -> f ())
-- @
--
coinit :: Counital a c => Covec a c
coinit = Covec counital

-- | Obtain a covector from a covector on the tensor product space.
--
cojoin :: Coalgebra a c => Covec a (c, c) -> Covec a c
cojoin = cmap codiagonal

-- | Use a linear transformation to map over a dual space.
--
-- Note that the basis transforms < https://en.wikipedia.org/wiki/Covariant_transformation covariantly >.
--
cmap :: Mat a b c -> Covec a b -> Covec a c
cmap f g = Covec $ runCovec g . vmap f

infixr 7 `comult`

-- | Multiplication operator on a coalgebra over f a free semimodule.
--
-- >>> flip runCovec (e2 1 1) $ comult (cov $ V2 1 2) (cov $ V2 7 4)
-- 11
--
-- /Caution/ in general 'comult' needn't be commutative, nor coassociative.
--
comult :: Coalgebra a c => Covec a c -> Covec a c -> Covec a c
comult (Covec f) (Covec g) = Covec $ \k -> f (\m -> g (cojoined k m))

-------------------------------------------------------------------------------
-- Linear transformations
-------------------------------------------------------------------------------

-- | An endomorphism over a free semimodule.
--
-- >>> one + two !# V2 1 2 :: V2 Double
-- V2 3.0 6.0
--
type End a b = Mat a b b

-- | An map between finite dimensional vector spaces with dimensions /m/ & /n/.
--
type Fin a m n = Mat a (Finite m) (Finite n)

-- | A linear transformation between free semimodules indexed with bases /b/ and /c/.
--
-- @
-- f '!#' x '+' y = (f '!#' x) + (f '!#' y)
-- f '!#' (r '.*' x) = r '.*' (f '!#' x)
-- @
--
-- Usable with a wide range of vector representations, for example via < http://hackage.haskell.org/package/vector-sized-1.4.0.0/docs/Data-Vector-Sized.html#v:generate > (Note that < http://hackage.haskell.org/package/vector-sized-1.4.0.0/docs/Data-Vector-Generic-Sized.html#t:Vector Vector > is /Representable/).
--
-- /Caution/: You must ensure these laws hold when using the default constructor.
--
-- Prefer 'mat', 'fin', or 'image' where appropriate.
--
newtype Mat a b c = Mat ( Vec a c -> Vec a b )

-- | Obtain a linear transformation from a matrix.
--
-- @ ('.#') = ('!#') . 'mat' @
--
mat :: Free f => FreeCounital g a => (f**g) a -> Mat a (Rep f) (Rep g) 
mat m = Mat $ \k -> vec (m .# tabulate k)

-- | Obtain a finite linear transformation from a function of row and column indices.
--
fin :: KnownNat n => Semiring a => (Finite m -> Finite n -> a) -> Fin a m n 
fin f = image $ \b -> (f b &&& id) <$> finites

-- | Create a linear transformation from an image of basis elements.
--
-- >>> image (e2 [(2, E31),(3, E32)] [(1, E33)]) !# V3 1 1 1 :: V2 Int
-- V2 5 1
--
image :: Semiring a => (b -> [(a, c)]) -> Mat a b c
image f = Mat $ \k b -> sum [ a * k c | (a, c) <- f b ]

-- | 'Mat' is an invariant functor.
--
-- See also < http://comonad.com/reader/2008/rotten-bananas/ >.
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Mat a1 b c -> Mat a2 b c
invmap f g (Mat t) = Mat $ \x -> t (x >>> g) >>> f

-- | Use a Galois connection to switch the base ring of a linear transformation.
--
galois :: Conn a1 a2 -> Mat a1 b c -> Mat a2 b c
galois (Conn f g) = invmap f g

-- | TODO: Document
--
initial :: Unital a b => Mat a b ()
initial = Mat $ \k -> unital $ k ()

-- | TODO: Document
--
coinitial :: Counital a c => Mat a () c
coinitial = Mat $ const . counital

-- |
--
-- @
-- 'rmap' (\((c1,()),(c2,())) -> (c1,c2)) '$' ('C.id' '***' 'initial') 'C..' 'diagonal' = 'C.id'
-- 'rmap' (\(((),c1),((),c2)) -> (c1,c2)) '$' ('initial' '***' 'C.id') 'C..' 'diagonal' = 'C.id'
-- @
--
diagonal :: Algebra a b => Mat a b (b,b)
diagonal = Mat $ joined . curry

-- |
--
-- @
-- 'lmap' (\(c1,c2) -> ((c1,()),(c2,()))) '$' ('C.id' '***' 'coinitial') 'C..' 'codiagonal' = 'C.id'
-- 'lmap' (\(c1,c2) -> (((),c1),((),c2))) '$' ('coinitial' '***' 'C.id') 'C..' 'codiagonal' = 'C.id'
-- @
--
codiagonal :: Coalgebra a c => Mat a (c, c) c
codiagonal = Mat $ uncurry . cojoined

-- | Swap components of a tensor product.
--
-- This is equivalent to a matrix transpose.
--
braid :: Mat a (b, c) (c, b)
braid = arr swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
cobraid :: Mat a (Either b c) (Either c b)
cobraid = arr $ Right ||| Left
{-# INLINE cobraid #-}

-- | TODO: Document
--
split :: (b -> (b1 , b2)) -> Mat a b1 c -> Mat a b2 c -> Mat a b c
split f x y = dimap f fst $ x *** y
{-# INLINE split #-}

-- | TODO: Document
--
cosplit :: ((Either c1 c2) -> c) -> Mat a b c1 -> Mat a b c2 -> Mat a b c
cosplit f x y = dimap Left f $ x +++ y
{-# INLINE cosplit #-}

{-
λ> foo = convolve (mat $ m22 1 0 0 1) (mat $ m22 1 0 0 1)
λ> foo !# V2 1 2 :: V2 Int
V2 1 2
λ> foo = convolve (mat $ m22 1 0 0 1) (mat $ m22 1 1 1 1)
λ> foo !# V2 1 2 :: V2 Int
V2 1 2
λ> foo = convolve (mat $ m22 1 1 1 1) (mat $ m22 1 1 1 1)
λ> foo !# V2 1 2 :: V2 Int
V2 3 3
-}

-- | Convolution with an associative algebra and coassociative coalgebra
--
convolve :: Algebra a b => Coalgebra a c => Mat a b c -> Mat a b c -> Mat a b c
convolve f g = codiagonal <<< (f *** g) <<< diagonal

-------------------------------------------------------------------------------
-- Vector constructors & acessors
-------------------------------------------------------------------------------

-- | Project onto the left-hand component of a direct sum.
--
exl :: Free f => Free g => (f++g) a -> f a
exl fg = arr Left !# fg
{-# INLINE exl #-}

-- | Project onto the right-hand component of a direct sum.
--
exr :: Free f => Free g => (f++g) a -> g a
exr fg = arr Right !# fg
{-# INLINE exr #-}

-- | Retrieve the coefficient of a basis element
--
-- >>> elt E21 (V2 1 2)
-- 1
--
elt :: Free f => Rep f -> f a -> a
elt = flip index
{-# INLINE elt #-}

-- | Insert an element into an algebra.
--
-- When the algebra is trivial this is equal to 'pureRep'.
--
-- >>> V4 1 2 3 4 .*. unit two :: V4 Int
-- V4 2 4 6 8
--
unit :: FreeUnital f a => a -> f a
unit = tabulate . unital

-- | Unital element of a unital algebra over a free semimodule.
--
-- >>> unit' :: Complex Int
-- 1 :+ 0
--
unit' :: FreeUnital f a => f a
unit' = unit one

-- | Reduce a coalgebra over a free semimodule.
--
-- /Note/: for the stock 'Counital' instances (e.g. 'E2', 'Finite', etc) this is summation.
--
-- >>> x = fromTuple (7, 4) :: Vector 2 Int
-- >>> counit x
-- 11
-- 
counit :: FreeCounital f a => f a -> a
counit = counital . vec

-- | Create a unit vector at an index.
--
-- >>> i = 4 :: Finite 5
-- >>> dirac i :: Vector 5 Double
-- Vector [0.0,0.0,0.0,0.0,1.0]
-- 
-- >>> dirac E21 :: V2 Int
-- V2 1 0
-- >>> dirac E42 :: V4 Int
-- V4 0 1 0 0
--
dirac :: Semiring a => Free f => Eq (Rep f) => Rep f -> f a
dirac i = tabulate $ \j -> bool zero one (i == j)
{-# INLINE dirac #-}

-------------------------------------------------------------------------------
-- Vector operators
-------------------------------------------------------------------------------

infixr 7 !*

-- | Apply a covector to a vector on the right.
--
-- > (!*) :: Vec a b -> Covec a b -> a 
--
(!*) :: Free f => f a -> Covec a (Rep f) -> a 
(!*) = flip (*!)

infixl 7 *!

-- | Apply a covector to a vector on the left.
--
-- > (*!) :: Covec a b -> Vec a b -> a
--
(*!) :: Free f => Covec a (Rep f) -> f a -> a
(*!) x = runCovec x . index

--infixr 7 *., \., /.

-- | Left-multiply a module element by a scalar.
--
(*.) :: Semiring a => Functor f => a -> f a -> f a
(*.) a f = (a *) <$> f

-- | Right-multiply a module element by a scalar.
--
(.*) :: Semiring a => Functor f => f a -> a -> f a
(.*) f a = (* a) <$> f

-- | Right-divide a vector by a scalar (on the left).
--
--(/.) :: Semifield a => Functor f => a -> f a -> f a
--a /. f = (/ a) <$> f

-- | Left-divide a vector by a scalar.
--
--(\.) :: Semifield a => Functor f => a -> f a -> f a
--a \. f = (a \\)  <$> f

--infixl 7 .*, .\, ./

-- | Right-divide a vector by a scalar.
--
--(./) :: Semifield a => Functor f => f a -> a -> f a
--(./) = flip (/.)

-- | Left-divide a vector by a scalar (on the right).
--
--(.\) :: Semifield a => Functor f => f a -> a -> f a
--(.\) = flip (\.)

infixl 6 .+.

-- | Addition operator on a vector space.
--
-- > (.+.) :: Vec a b -> Vec a b -> Vec a b
--
-- >>> E22 & (vec $ V2 1 2) .+. (vec $ V2 7 4)
-- 8
--
(.+.) :: Semiring a => Free f => f a -> f a -> f a
(.+.) = liftR2 (+)

infixl 7 .*.

-- | Multiplication operator on an algebra over a free semimodule.
--
-- > (.*.) :: Vec a b -> Vec a b -> Vec a b
--
-- >>> E22 & (vec $ V2 1 2) .*. (vec $ V2 7 4)
-- 8
--
-- /Caution/ in general '.*.' needn't be commutative, nor associative.
--
(.*.) :: FreeAlgebra f a => f a -> f a -> f a
(.*.) x y = tabulate $ joined (\i j -> vec x i * vec y j)

-- | Linearly interpolate between two vectors.
--
-- >>> u = V3 (1 :% 1) (2 :% 1) (3 :% 1) :: V3 Rational
-- >>> v = V3 (2 :% 1) (4 :% 1) (6 :% 1) :: V3 Rational
-- >>> r = 1 :% 2 :: Rational
-- >>> lerp r u v
-- V3 (6 % 4) (12 % 4) (18 % 4)
--
lerp :: FreeModule f a => Presemiring (f a) => a -> f a -> f a -> f a
lerp r f g = r *. f + (one - r) *. g

infix 6 `inner`

-- | Inner product.
--
-- When the coalgebra is trivial this is a variant of 'Data.Semiring.xmult' restricted to free functors.
--
-- >>> V3 1 2 3 `inner` V3 1 2 3
-- 14
-- 
inner :: FreeCounital f a => f a -> f a -> a
inner x y = counit $ liftR2 (*) x y
{-# INLINE inner #-}

-- | Outer product.
--
-- >>> V2 1 1 `outer` V2 1 1
-- Compose (V2 (V2 1 1) (V2 1 1))
--
outer :: Semiring a => Free f => Free g => f a -> g a -> (f**g) a
outer x y = Compose $ fmap (\z-> fmap (*z) y) x
{-# INLINE outer #-}

-- | Squared /l2/ norm of a vector.
--
quadrance :: FreeCounital f a => f a -> a
quadrance = M.join inner 
{-# INLINE quadrance #-}

-------------------------------------------------------------------------------
-- Matrix accessors and constructors
-------------------------------------------------------------------------------

-- | Retrieve an element of a matrix.
--
-- >>> elt2 E21 E21 $ m22 1 2 3 4
-- 1
--
elt2 :: Free f => Free g => Rep f -> Rep g -> (f**g) a -> a
elt2 i j = elt i . col j
{-# INLINE elt2 #-}

-- | Retrieve a row of a matrix.
--
-- >>> row E22 $ m23 1 2 3 4 5 6
-- V3 4 5 6
--
row :: Free f => Rep f -> (f**g) a -> g a
row i = elt i . getCompose
{-# INLINE row #-}

-- | Obtain a matrix from a collection of rows.
--
rows :: Free f => Free g => f (g a) -> (f**g) a
rows = Compose
{-# INLINE rows #-}

-- | Obtain a matrix by repeating a row.
--
-- >>> rows (V2 1 2) :: M22 Int
-- V2 (V2 1 2) (V2 1 2)
--
rows' :: Free f => Free g => g a -> (f**g) a
rows' g = arr snd !# g
{-# INLINE rows' #-}

-- | Retrieve a column of a matrix.
--
-- >>> elt E22 . col E31 $ m23 1 2 3 4 5 6
-- 4
--
col :: Free f => Free g => Rep g -> (f**g) a -> f a
col j = flip vec j . distributeRep . getCompose
{-# INLINE col #-}

-- | Obtain a matrix from a collection of columns.
--
cols :: Free f => Free g => g (f a) -> (f**g) a
cols = transpose . Compose

-- | Obtain a matrix by repeating a column.
--
-- >>> cols (V2 1 2) :: M22 Int
-- V2 (V2 1 1) (V2 2 2)
--
cols' :: Free f => Free g => f a -> (f**g) a
cols' f = arr fst !# f
{-# INLINE cols' #-}

-- | Obtain a vector from a tensor.
--
-- When the algebra is trivial we have:
--
-- @ 'diag' f = 'tabulate' $ 'joined' ('vec' . 'vec' ('getCompose' f)) @
--
-- >>> diag $ m22 1.0 2.0 3.0 4.0
-- V2 1.0 4.0
--
diag :: FreeAlgebra f a => (f**f) a -> f a
diag f = diagonal !# f

-- | Obtain a tensor from a vector.
--
-- When the coalgebra is trivial we have:
--
-- @ 'codiag' = 'flip' 'bindRep' 'id' '.' 'getCompose' @
--
codiag :: FreeCoalgebra f a => f a -> (f**f) a
codiag f = codiagonal !# f

-- | Obtain a < https://en.wikipedia.org/wiki/Diagonal_matrix#Scalar_matrix scalar matrix > from a scalar.
--
-- >>> scalar 4.0 :: M22 Double
-- Compose (V2 (V2 4.0 0.0) (V2 0.0 4.0))
--
scalar :: FreeCoalgebra f a => a -> (f**f) a
scalar = codiag . pureRep

-- | Obtain an identity matrix.
--
-- >>> identity :: M33 Int
-- Compose (V3 (V3 1 0 0) (V3 0 1 0) (V3 0 0 1))
--
identity :: FreeCoalgebra f a => (f**f) a
identity = scalar one
{-# INLINE identity #-}

-------------------------------------------------------------------------------
-- Matrix operators
-------------------------------------------------------------------------------

infixr 2 !#

-- | Apply a transformation to a vector.
--
(!#) :: Free f => Free g => Mat a (Rep f) (Rep g) -> g a -> f a
(!#) t = tabulate . vmap t . index

infixl 2 #!

-- | Apply a transformation to a vector.
--
(#!) :: Free f => Free g => g a -> Mat a (Rep f) (Rep g) -> f a
(#!) = flip (!#)

infixr 7 .#

-- | Multiply a matrix on the right by a column vector.
--
-- @ ('.#') = ('!#') . 'mat' @
--
-- >>> mat (m23 1 2 3 4 5 6) !# V3 7 8 9 :: V2 Int
-- V2 50 122
-- >>> m23 1 2 3 4 5 6 .# V3 7 8 9 :: V2 Int
-- V2 50 122
-- >>> m22 1 0 0 0 .# m23 1 2 3 4 5 6 .# V3 7 8 9 :: V2 Int
-- V2 50 0
--
(.#) :: Free f => FreeCounital g a => (f**g) a -> g a -> f a
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
(#.) :: Free g => FreeCounital f a => f a -> (f**g) a -> g a
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
(.#.) :: Free f => Free h => FreeCounital g a => (f**g) a -> (g**h) a -> (f**h) a
(.#.) x y = tabulate (\(i,j) -> row i x `inner` col j y)
{-# INLINE (.#.) #-}
 
-- | Left (post) composition with a linear transformation.
--
compl :: Free f1 => Free f2 => Free g => Mat a (Rep f1) (Rep f2) -> (f2**g) a -> (f1**g) a
compl t fg = first t !# fg

-- | Right (pre) composition with a linear transformation.
--
compr :: Free f => Free g1 => Free g2 => Mat a (Rep g1) (Rep g2) -> (f**g2) a -> (f**g1) a
compr t fg = second t !# fg

-- | Left and right composition with a linear transformation.
--
-- @ f *** g !# v = 'compl' f '>>>' 'compr' g @
--
complr :: Free f1 => Free f2 => Free g1 => Free g2 => Mat a (Rep f1) (Rep f2) -> Mat a (Rep g1) (Rep g2) -> (f2**g2) a -> (f1**g1) a
complr t1 t2 fg = (t1 *** t2) !# fg

-- | Trace of an endomorphism.
--
-- >>> trace $ m22 1.0 2.0 3.0 4.0
-- 5.0
--
trace :: FreeBialgebra f a => (f**f) a -> a
trace = counit . diag
{-# INLINE trace #-}

-- | Transpose a matrix.
--
-- >>> transpose $ m23 1 2 3 4 5 6 :: M32 Int
-- V3 (V2 1 4) (V2 2 5) (V2 3 6)
--
transpose :: Free f => Free g => (f**g) a -> (g**f) a
transpose fg = braid !# fg
{-# INLINE transpose #-}

-------------------------------------------------------------------------------
-- Covec instances
-------------------------------------------------------------------------------

instance Functor (Covec a) where
  fmap f m = Covec $ \k -> m `runCov` k . f

instance Applicative (Covec a) where
  pure a = Covec $ \k -> k a
  mf <*> ma = Covec $ \k -> mf `runCov` \f -> ma `runCov` k . f

instance Monad (Covec a) where
  return a = Covec $ \k -> k a
  m >>= f = Covec $ \k -> m `runCov` \a -> f a `runCov` k

{-
instance Presemiring a => Presemiring (Covec a b) where
  (<>) (Covec m) (Covec n) = Covec $ m + n

instance Semiring a => Monoid (Covec a b) where
  mempty = Covec zero

instance Ring a => Magma (Covec a b) where
  (<<) (Covec m) (Covec n) = Covec $ m - n

instance Ring a => Quasigroup (Covec a b)
instance Ring a => Loop (Covec a b)
instance Ring a => Group (Covec a b)
-}

-------------------------------------------------------------------------------
-- Mat instances
-------------------------------------------------------------------------------

addMat :: Semiring a => Mat a b c -> Mat a b c -> Mat a b c
addMat (Mat f) (Mat g) = Mat $ f + g

subMat :: Ring a => Mat a b c -> Mat a b c -> Mat a b c
subMat (Mat f) (Mat g) = Mat $ \h -> f h - g h

mulMat :: Semiring a => Mat a b c -> Mat a b c -> Mat a b c
mulMat (Mat f) (Mat g) = Mat $ \h -> f h * g h

instance Functor (Mat a b) where
  fmap f m = Mat $ \k -> m !# k . f

instance Category (Mat a) where
  id = Mat id
  Mat f . Mat g = Mat $ g . f

instance Apply (Mat a b) where
  mf <.> ma = Mat $ \k b -> (mf !# \f -> (ma !# k . f) b) b

instance Applicative (Mat a b) where
  pure a = Mat $ \k _ -> k a
  (<*>) = (<.>)

instance Profunctor (Mat a) where
  -- | 'Mat' is a profunctor in the category of semimodules.
  --
  -- /Caution/: Arbitrary mapping functions may violate linearity.
  --
  -- >>> dimap id (e3 True True False) (arr id) !# 4 :+ 5 :: V3 Int
  -- V3 5 5 4
  --
  dimap l r f = arr r <<< f <<< arr l

instance Strong (Mat a) where
  first' = first
  second' = second

instance Choice (Mat a) where
  left' = left
  right' = right

instance Sieve (Mat a) (Covec a) where
  sieve l b = Covec $ \k -> (l !# k) b 

instance PR.Representable (Mat a) where
  type Rep (Mat a) = Covec a
  tabulate f = Mat $ \k b -> runCovec (f b) k

instance Representable (Mat a b) where
  type Rep (Mat a b) = Covec a b
  index = sieve
  tabulate = PR.tabulate

instance Monad (Mat a b) where
  return a = Mat $ \k _ -> k a
  m >>= f = Mat $ \k b -> (m !# \a -> (f a !# k) b) b

instance Arrow (Mat a) where
  arr f = Mat (. f)
  first m = Mat $ \k (a,c) -> (m !# \b -> k (b,c)) a
  second m = Mat $ \k (c,a) -> (m !# \b -> k (c,b)) a
  m *** n = Mat $ \k (a,c) -> (m !# \b -> (n !# \d -> k (b,d)) c) a
  m &&& n = Mat $ \k a -> (m !# \b -> (n !# \c -> k (b,c)) a) a

instance ArrowChoice (Mat a) where
  left m = Mat $ \k -> either (m !# k . Left) (k . Right)
  right m = Mat $ \k -> either (k . Left) (m !# k . Right)
  m +++ n =  Mat $ \k -> either (m !# k . Left) (n !# k . Right)
  m ||| n = Mat $ \k -> either (m !# k) (n !# k)

instance ArrowApply (Mat a) where
  app = Mat $ \k (f,a) -> (f !# k) a


 

{-
instance Semiring a => Semigroup (Mat a b c) where
  (<>) = addMat

instance Ring a => Monoid (Mat a b c) where
  mempty = Mat $ const zero


instance Presemiring a => Semigroup (End a b) where
  (<>) = liftA2 (<<<)

instance Semiring a => Monoid ((End a b)) where
  mempty = pure C.id

instance Presemiring a => Presemiring (End a b)
instance Semiring a => Semiring (End a b)
instance Ring a => Ring (End a b)

instance Coalgebra a c => Semigroup (Mat a b c) where
  (<>) f g = Mat $ \k b -> (f !# \a -> (g !# cojoined k a) b) b
instance Counital a c => Monoid (Multiplicative (Mat a b c)) where
  mempty = pure . Mat $ \k _ -> counital k

instance Coalgebra a c => Presemiring (Mat a b c)
instance Counital a c => Semiring (Mat a b c)
instance (Ring a, Counital a c) => Ring (Mat a b c)
-}
{-
instance Counital a b => LeftSemimodule (Mat a b b) (Mat a b c) where
  -- | Left matrix multiplication
  lscale = (>>>)

instance Semiring a => LeftSemimodule a (Mat a b c) where
  lscale l (Mat m) = Mat $ \k b -> l *. m k b

instance Counital a c => RightSemimodule (Mat a c c) (Mat a b c) where
  -- | Right matrix multiplication
  rscale = (<<<)

instance (Counital a b, Counital a c) => Bisemimodule (Mat a b b) (Mat a c c) (Mat a b c)

instance Semiring a => RightSemimodule a (Mat a b m) where
  rscale r (Mat m) = Mat $ \k b -> m k b .* r

instance Bisemimodule a a a => Bisemimodule a a (Mat a b c)

instance (Additive-Group) a => Magma (Additive (Mat a b c)) where
  (<<) = liftR2 subMat

instance (Additive-Group) a => Quasigroup (Additive (Mat a b c))
instance (Additive-Group) a => Loop (Additive (Mat a b c))
instance (Additive-Group) a => Group (Additive (Mat a b c))


-}

{-
-- | An endomorphism of endomorphisms. 
--
-- @ 'Cayley' a = (a -> a) -> (a -> a) @
--
type Cayley a = Mat a a a

-- | Lift a semiring element into a 'Cayley'.
--
-- @ 'runCayley' . 'cayley' = 'id' @
--
-- >>> runCayley . cayley $ 3.4 :: Double
-- 3.4
-- >>> runCayley . cayley $ m22 1 2 3 4 :: M22 Int
-- Compose (V2 (V2 1 2) (V2 3 4))
-- 
cayley :: Semiring a => a -> Cayley a
cayley a = Mat $ \k b -> a * k zero + b

-- | Extract a semiring element from a 'Cayley'.
--
-- >>> runCayley $ two * (one + (cayley 3.4)) :: Double
-- 8.8
-- >>> runCayley $ two * (one + (cayley $ m22 1 2 3 4)) :: M22 Int
-- Compose (V2 (V2 4 4) (V2 6 10))
--
runCayley :: Semiring a => Cayley a -> a
runCayley (Mat f) = f (one +) zero

-- ring homomorphism from a -> a^b
embed :: (Multiplicative-Semigroup) a => (Multiplicative-Monoid) c => (b -> a) -> Mat a b c
embed f = Mat $ \k b -> f b * k one

-- if the characteristic of s does not divide the order of a, then s[a] is semisimple
-- and if a has a length function, we can build f ailtered algebra
-}
