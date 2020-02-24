{-# LANGUAGE CPP                        #-}
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


module Data.Semimodule.Transform (
  -- * Types
    type (**) 
  , type (++) 
  -- * Linear functionals
  , Dual(..)
  , dual
  , image'
  , (!*)
  , (*!)
  , toTran
  , fromTran 
  -- * Linear transformations 
  , Endo 
  , Tran(..)
  , arr
  , tran
  , image 
  , (!#)
  , (#!)
  , (!#!)
  , dimap
  , invmap
  -- * Common linear transformations 
  , init
  , init'
  , coinit
  , coinit'
  , braid
  , cobraid 
  , join
  , join'
  , cojoin
  , cojoin'
  -- * Other operations
  , split
  , cosplit
  , convolve
  , convolve'
  , commutator
  -- * Matrix arithmetic
  , (.#)
  , (#.)
  , (.#.)
  , outer
  , inner
  , quadrance
  , trace
  , transpose
  -- * Matrix constructors and accessors
  , diag
  , codiag
  , scalar
  , identity
  , row
  , rows
  , col
  , cols
  , projl
  , projr
  , compl
  , compr
  , complr
  -- * Representable
  , Representable(..)
) where

import safe Control.Arrow
import safe Control.Applicative
import safe Control.Category (Category, (>>>), (<<<))
import safe Data.Functor.Compose
import safe Data.Functor.Product
import safe Data.Functor.Rep hiding (Co)
import safe Data.Foldable (foldl')
import safe Data.Algebra
import safe Data.Semiring
import safe Data.Semimodule
import safe Data.Tuple (swap)
import safe Prelude hiding (Num(..), Fractional(..), init, negate, sum, product)
import safe Test.Logic hiding (join)
import safe qualified Control.Category as C
import safe qualified Control.Monad as M
import safe Control.Monad (MonadPlus(..))

infixr 2 **
infixr 1 ++

-- | A tensor product of semimodule morphisms.
--
type (f ** g) = Compose f g

-- | A direct sum of free semimodule elements.
--
type (f ++ g) = Product f g

-------------------------------------------------------------------------------
-- Linear functionals
-------------------------------------------------------------------------------

infixr 3 `runDual`
-- | Linear functionals from elements of a free semimodule to a scalar.
--
-- @ 
-- f '!*' (x '+' y) = (f '!*' x) '+' (f '!*' y)
-- f '!*' (x '.*' a) = a '*' (f '!*' x)
-- @
--
newtype Dual a c = UnsafeDual { runDual :: (c -> a) -> a }

-- | Take the dual of a vector.
--
-- >>> dual (V2 3 4) !% V2 1 2 :: Int
-- 11
--
dual :: FreeCounital a f => f a -> Dual a (Rep f)
dual f = UnsafeDual $ \k -> f `inner` tabulate k

-- | Create a 'Dual' from a linear combination of basis vectors.
--
-- >>> image' [(2, E31),(3, E32)] !* V3 1 1 1 :: Int
-- 5
--
image' :: Semiring a => Foldable f => f (a, c) -> Dual a c
image' f = UnsafeDual $ \k -> foldl' (\acc (a, c) -> acc + a * k c) zero f 

-- | Obtain a linear transfrom from a linear functional.
--
toTran :: (b -> Dual a c) -> Tran a b c
toTran f = UnsafeTran $ \k b -> f b !* k

-- | Obtain a linear functional from a linear transform.
--
fromTran :: Tran a b c -> b -> Dual a c
fromTran m b = UnsafeDual $ \k -> (m !# k) b

infixr 3 !*

-- | Apply a linear functional to a vector.
--
(!*) :: Free f => Dual a (Rep f) -> f a -> a
(!*) f x = runDual f $ index x

infixl 3 *!

-- | Apply a linear functional to a vector.
--
(*!) :: Free f => f a -> Dual a (Rep f) -> a 
(*!) = flip (!*)

-------------------------------------------------------------------------------
-- General linear transformations
-------------------------------------------------------------------------------

-- | An endomorphism over a free semimodule.
--
-- >>> one + two !# V2 1 2 :: V2 Double
-- V2 3.0 6.0
--
type Endo a b = Tran a b b

infixr 3 `runTran`

-- | A linear transformation between free semimodules indexed with bases /b/ and /c/.
--
-- > f '!#' x '+' y = (f '!#' x) + (f '!#' y)
-- > f '!#' (r '.*' x) = r '.*' (f '!#' x)
--
newtype Tran a b c = UnsafeTran { runTran :: (c -> a) -> b -> a }

-- | Lift a matrix into a linear transformation
--
-- @ ('.#') = ('!#') . 'tran' @
--
tran :: Free f => FreeCounital a g => (f**g) a -> Tran a (Rep f) (Rep g) 
tran m = UnsafeTran $ \k -> index $ m .# tabulate k

-- | Create a 'Tran' from a linear combination of basis vectors.
--
-- >>> image (e2 [(2, E31),(3, E32)] [(1, E33)]) !# V3 1 1 1 :: V2 Int
-- V2 5 1
--
image :: Semiring a => (b -> [(a, c)]) -> Tran a b c
image f = UnsafeTran $ \k b -> sum [ a * k c | (a, c) <- f b ]

infixr 2 !#

-- | Apply a transformation to a vector.
--
(!#) :: Free f => Free g => Tran a (Rep f) (Rep g) -> g a -> f a
(!#) t = tabulate . runTran t . index

infixl 2 #!

-- | Apply a transformation to a vector.
--
(#!) :: Free f => Free g => g a -> Tran a (Rep f) (Rep g) -> f a
(#!) = flip (!#)

infix 2 !#!

-- | Compose two transformations.
--
(!#!) :: Tran a c d -> Tran a b c -> Tran a b d
UnsafeTran f !#! UnsafeTran g = UnsafeTran $ g . f

-- | 'Tran' is a profunctor in the category of semimodules.
--
-- /Caution/: Arbitrary mapping functions may violate linearity.
--
-- >>> dimap id (e3 True True False) (arr id) !# 4 :+ 5 :: V3 Int
-- V3 5 5 4
--
dimap :: (b1 -> b2) -> (c1 -> c2) -> Tran a b2 c1 -> Tran a b1 c2
dimap l r f = arr r <<< f <<< arr l

-- | 'Tran' is an invariant functor.
--
-- See also < http://comonad.com/reader/2008/rotten-bananas/ >.
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Tran a1 b c -> Tran a2 b c
invmap f g (UnsafeTran t) = UnsafeTran $ \x -> t (x >>> g) >>> f

-------------------------------------------------------------------------------
-- Common linear transformations
-------------------------------------------------------------------------------

{-

prop_cojoin (~~) f = (cojoin !# f) ~~ (Compose . tabulate $ \i -> tabulate $ \j -> coappend (index f) i j)

prop_diag' (~~) f = (diag !# f) ~~ (Compose $ flip imapRep f $ \i x -> flip imapRep f $ \j _ -> bool zero x $ (i == j))

prop_diag (~~) f = (diag !# f) ~~ (flip bindRep id . getCompose $ f)

prop_codiag (~~) f = (codiag !# f) ~~ (tabulate $ append (index . index (getCompose f)))
-}

-- | TODO: Document
--
init :: Unital a b => Tran a b ()
init = UnsafeTran $ \k -> aempty $ k ()

-- | TODO: Document
--
init' :: Unital a b => b -> Dual a ()
init' b = UnsafeDual $ \k -> aempty (k ()) b

-- | TODO: Document
--
coinit :: Counital a c => Tran a () c
coinit = UnsafeTran $ \k () -> coempty k

-- | TODO: Document
--
coinit' :: Counital a c => Dual a c
coinit' = UnsafeDual coempty

-- | Swap components of a tensor product.
--
braid :: Tran a (b , c) (c , b)
braid = arr swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
cobraid :: Tran a (b + c) (c + b)
cobraid = arr eswap
{-# INLINE cobraid #-}

-- | TODO: Document
--
join :: Algebra a b => Tran a b (b,b)
join = UnsafeTran $ append . curry

-- | TODO: Document
--
join' :: Algebra a b => b -> Dual a (b,b)
join' b = UnsafeDual $ \k -> append (curry k) b

-- | TODO: Document
--
cojoin :: Coalgebra a c => Tran a (c,c) c
cojoin = UnsafeTran $ uncurry . coappend

-- | TODO: Document
--
cojoin' :: Coalgebra a c => c -> c -> Dual a c
cojoin' x y = UnsafeDual $ \k -> coappend k x y 

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

-- | TODO: Document
--
split :: (b -> (b1 , b2)) -> Tran a b1 c -> Tran a b2 c -> Tran a b c
split f x y = dimap f fst $ x *** y
{-# INLINE split #-}

-- | TODO: Document
--
cosplit :: ((c1 + c2) -> c) -> Tran a b c1 -> Tran a b c2 -> Tran a b c
cosplit f x y = dimap Left f $ x +++ y
{-# INLINE cosplit #-}

{-
λ> foo = convolve (tran $ m22 1 0 0 1) (tran $ m22 1 0 0 1)
λ> foo !# V2 1 2 :: V2 Int
V2 1 2
λ> foo = convolve (tran $ m22 1 0 0 1) (tran $ m22 1 1 1 1)
λ> foo !# V2 1 2 :: V2 Int
V2 1 2
λ> foo = convolve (tran $ m22 1 1 1 1) (tran $ m22 1 1 1 1)
λ> foo !# V2 1 2 :: V2 Int
V2 3 3
-}
-- | Convolution with an associative algebra and coassociative coalgebra
--
--
convolve :: Algebra a b => Coalgebra a c => Tran a b c -> Tran a b c -> Tran a b c
convolve f g = cojoin <<< (f *** g) <<< join

-- | TODO: Document
--
convolve' :: Algebra a b => Coalgebra a c => (b -> Dual a c) -> (b -> Dual a c) -> b -> Dual a c
convolve' f g c = do
   (c1,c2) <- join' c
   a1 <- f c1
   a2 <- g c2
   cojoin' a1 a2

-- | Commutator or Lie bracket of two semimodule endomorphisms.
--
commutator :: (Additive-Group) a => Endo a b -> Endo a b -> Endo a b
commutator x y = (x <<< y) `subTran` (y <<< x)

-------------------------------------------------------------------------------
-- Vector and matrix arithmetic
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

-- | Outer product.
--
-- >>> V2 1 1 `outer` V2 1 1
-- Compose (V2 (V2 1 1) (V2 1 1))
--
outer :: Semiring a => Free f => Free g => f a -> g a -> (f**g) a
outer x y = Compose $ fmap (\z-> fmap (*z) y) x

infix 6 `inner`

-- | Inner product.
--
-- This is a variant of 'Data.Semiring.xmult' restricted to free functors.
--
-- >>> V3 1 2 3 `inner` V3 1 2 3
-- 14
-- 
inner :: FreeCounital a f => f a -> f a -> a
inner x y = counital $ liftR2 (*) x y
{-# INLINE inner #-}

-- | Squared /l2/ norm of a vector.
--
quadrance :: FreeCounital a f => f a -> a
quadrance = M.join inner 
{-# INLINE quadrance #-}

-- | Trace of an endomorphism.
--
-- >>> trace $ m22 1.0 2.0 3.0 4.0
-- 5.0
--
trace :: FreeBialgebra a f => (f**f) a -> a
trace = counital . codiag

-- | Transpose a matrix.
--
-- >>> transpose $ m23 1 2 3 4 5 6 :: M32 Int
-- V3 (V2 1 4) (V2 2 5) (V2 3 6)
--
transpose :: Free f => Free g => (f**g) a -> (g**f) a
transpose fg = braid !# fg
{-# INLINE transpose #-}

-------------------------------------------------------------------------------
-- Matrix constructors and accessors
-------------------------------------------------------------------------------

-- | Obtain a < https://en.wikipedia.org/wiki/Diagonal_matrix diagonal matrix > from a vector.
--
-- @ 'diag' = 'flip' 'bindRep' 'id' '.' 'getCompose' @
--
diag :: FreeCoalgebra a f => f a -> (f**f) a
diag f = cojoin !# f

-- | Obtain the diagonal of a matrix as a vector.
--
-- @ 'codiag' f = 'tabulate' $ 'append' ('index' . 'index' ('getCompose' f)) @
--
-- >>> codiag $ m22 1.0 2.0 3.0 4.0
-- V2 1.0 4.0
--
codiag :: FreeAlgebra a f => (f**f) a -> f a
codiag f = join !# f

-- | Obtain a < https://en.wikipedia.org/wiki/Diagonal_matrix#Scalar_matrix scalar matrix > from a scalar.
--
-- >>> scalar 4.0 :: M22 Double
-- Compose (V2 (V2 4.0 0.0) (V2 0.0 4.0))
--
scalar :: FreeCoalgebra a f => a -> (f**f) a
scalar = diag . pureRep

-- | Obtain an identity matrix.
--
-- >>> identity :: M33 Int
-- Compose (V3 (V3 1 0 0) (V3 0 1 0) (V3 0 0 1))
--
identity :: FreeCoalgebra a f => (f**f) a
identity = scalar one
{-# INLINE identity #-}

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

-- | Project onto the left-hand component of a direct sum.
--
projl :: Free f => Free g => (f++g) a -> f a
projl fg = arr Left !# fg
{-# INLINE projl #-}

-- | Project onto the right-hand component of a direct sum.
--
projr :: Free f => Free g => (f++g) a -> g a
projr fg = arr Right !# fg
{-# INLINE projr #-}

-- | Left (post) composition with a linear transformation.
--
compl :: Free f1 => Free f2 => Free g => Tran a (Rep f1) (Rep f2) -> (f2**g) a -> (f1**g) a
compl t fg = first t !# fg

-- | Right (pre) composition with a linear transformation.
--
compr :: Free f => Free g1 => Free g2 => Tran a (Rep g1) (Rep g2) -> (f**g2) a -> (f**g1) a
compr t fg = second t !# fg

-- | Left and right composition with a linear transformation.
--
-- @ 'complr' f g = 'compl' f '>>>' 'compr' g @
--
complr :: Free f1 => Free f2 => Free g1 => Free g2 => Tran a (Rep f1) (Rep f2) -> Tran a (Rep g1) (Rep g2) -> (f2**g2) a -> (f1**g1) a
complr t1 t2 fg = t1 *** t2 !# fg

-------------------------------------------------------------------------------
-- Dual instances
-------------------------------------------------------------------------------

instance Functor (Dual a) where
  fmap f m = UnsafeDual $ \k -> m `runDual` k . f

instance Applicative (Dual a) where
  pure a = UnsafeDual $ \k -> k a
  mf <*> ma = UnsafeDual $ \k -> mf `runDual` \f -> ma `runDual` k . f

instance Monad (Dual a) where
  return a = UnsafeDual $ \k -> k a
  m >>= f = UnsafeDual $ \k -> m `runDual` \a -> f a `runDual` k

instance (Additive-Monoid) a => Alternative (Dual a) where
  UnsafeDual m <|> UnsafeDual n = UnsafeDual $ m + n
  empty = UnsafeDual zero

instance (Additive-Monoid) a => MonadPlus (Dual a) where
  UnsafeDual m `mplus` UnsafeDual n = UnsafeDual $ m + n
  mzero = UnsafeDual zero

instance (Additive-Semigroup) a => Semigroup (Additive (Dual a b)) where
  (<>) = liftA2 $ \(UnsafeDual m) (UnsafeDual n) -> UnsafeDual $ m + n

instance (Additive-Monoid) a => Monoid (Additive (Dual a b)) where
  mempty = Additive $ UnsafeDual zero

instance Coalgebra a b => Semigroup (Multiplicative (Dual a b)) where
  (<>) = liftA2 $ \(UnsafeDual f) (UnsafeDual g) -> UnsafeDual $ \k -> f (\m -> g (coappend k m))

instance Counital a b => Monoid (Multiplicative (Dual a b)) where
  mempty = Multiplicative $ UnsafeDual coempty

instance Coalgebra a b => Presemiring (Dual a b)

instance Counital a b => Semiring (Dual a b)

instance (Additive-Group) a => Magma (Additive (Dual a b)) where
  (<<) = liftA2 $ \(UnsafeDual m) (UnsafeDual n) -> UnsafeDual $ m - n

instance (Additive-Group) a => Quasigroup (Additive (Dual a b)) where
instance (Additive-Group) a => Loop (Additive (Dual a b)) where
instance (Additive-Group) a => Group (Additive (Dual a b)) where

instance (Ring a, Counital a b) => Ring (Dual a b)

instance Counital r m => LeftSemimodule (Dual r m) (Dual r m) where
  lscale = (*)

instance LeftSemimodule r s => LeftSemimodule r (Dual s m) where
  lscale s m = UnsafeDual $ \k -> s *. runDual m k

instance Counital r m => RightSemimodule (Dual r m) (Dual r m) where
  rscale = (*)

instance RightSemimodule r s => RightSemimodule r (Dual s m) where
  rscale s m = UnsafeDual $ \k -> runDual m k .* s


-------------------------------------------------------------------------------
-- Trans instances
-------------------------------------------------------------------------------

addTran :: (Additive-Semigroup) a => Tran a b c -> Tran a b c -> Tran a b c
addTran (UnsafeTran f) (UnsafeTran g) = UnsafeTran $ f + g

subTran :: (Additive-Group) a => Tran a b c -> Tran a b c -> Tran a b c
subTran (UnsafeTran f) (UnsafeTran g) = UnsafeTran $ \h -> f h - g h

-- mulTran :: (Multiplicative-Semigroup) a => Tran a b c -> Tran a b c -> Tran a b c
-- mulTran (Tran f) (Tran g) = Tran $ \h -> f h * g h

instance Functor (Tran a b) where
  fmap f m = UnsafeTran $ \k -> m !# k . f

instance Applicative (Tran a b) where
  pure a = UnsafeTran $ \k _ -> k a
  mf <*> ma = UnsafeTran $ \k b -> (mf !# \f -> (ma !# k . f) b) b

instance Monad (Tran a b) where
  return a = UnsafeTran $ \k _ -> k a
  m >>= f = UnsafeTran $ \k b -> (m !# \a -> (f a !# k) b) b

instance Category (Tran a) where
  id = UnsafeTran id
  (.) = (!#!)

instance Arrow (Tran a) where
  arr f = UnsafeTran (. f)
  first m = UnsafeTran $ \k (a,c) -> (m !# \b -> k (b,c)) a
  second m = UnsafeTran $ \k (c,a) -> (m !# \b -> k (c,b)) a
  m *** n = UnsafeTran $ \k (a,c) -> (m !# \b -> (n !# \d -> k (b,d)) c) a
  m &&& n = UnsafeTran $ \k a -> (m !# \b -> (n !# \c -> k (b,c)) a) a

instance ArrowChoice (Tran a) where
  left m = UnsafeTran $ \k -> either (m !# k . Left) (k . Right)
  right m = UnsafeTran $ \k -> either (k . Left) (m !# k . Right)
  m +++ n =  UnsafeTran $ \k -> either (m !# k . Left) (n !# k . Right)
  m ||| n = UnsafeTran $ \k -> either (m !# k) (n !# k)

instance ArrowApply (Tran a) where
  app = UnsafeTran $ \k (f,a) -> (f !# k) a

instance (Additive-Monoid) a => ArrowZero (Tran a) where
  zeroArrow = UnsafeTran zero

instance (Additive-Monoid) a => ArrowPlus (Tran a) where
  (<+>) = addTran

instance (Additive-Semigroup) a => Semigroup (Additive (Tran a b c)) where
  (<>) = liftA2 addTran

instance (Additive-Monoid) a => Monoid (Additive (Tran a b c)) where
  mempty = pure . UnsafeTran $ const zero

instance Coalgebra a c => Semigroup (Multiplicative (Tran a b c)) where
  (<>) = liftR2 $ \ f g -> UnsafeTran $ \k b -> (f !# \a -> (g !# coappend k a) b) b

instance Counital a c => Monoid (Multiplicative (Tran a b c)) where
  mempty = pure . UnsafeTran $ \k _ -> coempty k

instance Coalgebra a c => Presemiring (Tran a b c)
instance Counital a c => Semiring (Tran a b c)

instance Counital a m => LeftSemimodule (Tran a b m) (Tran a b m) where
  lscale = (*)

instance LeftSemimodule r s => LeftSemimodule r (Tran s b m) where
  lscale s (UnsafeTran m) = UnsafeTran $ \k b -> s *. m k b

instance Counital a m => RightSemimodule (Tran a b m) (Tran a b m) where
  rscale = (*)

instance RightSemimodule r s => RightSemimodule r (Tran s b m) where
  rscale s (UnsafeTran m) = UnsafeTran $ \k b -> m k b .* s

instance (Additive-Group) a => Magma (Additive (Tran a b c)) where
  (<<) = liftR2 subTran

instance (Additive-Group) a => Quasigroup (Additive (Tran a b c)) where
instance (Additive-Group) a => Loop (Additive (Tran a b c)) where
instance (Additive-Group) a => Group (Additive (Tran a b c)) where

instance (Ring a, Counital a c) => Ring (Tran a b c)




{-

-- | An endomorphism of endomorphisms. 
--
-- @ 'Cayley' a = (a -> a) -> (a -> a) @
--
type Cayley a = Tran a a a

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
cayley a = Tran $ \k b -> a * k zero + b

-- | Extract a semiring element from a 'Cayley'.
--
-- >>> runCayley $ two * (one + (cayley 3.4)) :: Double
-- 8.8
-- >>> runCayley $ two * (one + (cayley $ m22 1 2 3 4)) :: M22 Int
-- Compose (V2 (V2 4 4) (V2 6 10))
--
runCayley :: Semiring a => Cayley a -> a
runCayley (Tran f) = f (one +) zero

-- ring homomorphism from a -> a^b
--embed :: Counital a c => (b -> a) -> Tran a b c
embed f = Tran $ \k b -> f b * k one

-- if the characteristic of s does not divide the order of a, then s[a] is semisimple
-- and if a has a length function, we can build a filtered algebra

-- | The < https://en.wikipedia.org/wiki/Augmentation_(algebra) augmentation > ring homomorphism from a^b -> a
--
augment :: Semiring a => Tran a b c -> b -> a
augment m = m !# const one



-}



