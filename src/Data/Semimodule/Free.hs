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

module Data.Semimodule.Free (
  -- * Types
    type Free
  -- * Vectors
  , Vec(..)
  , vmap
  , join
  , init
  , (!*)
  , (*!)
  , (!*!)
  -- * Covectors
  , Cov(..)
  , images
  , cmap
  , cojoin
  , coinit
  , comult
  -- * Linear transformations
  , Lin(..)
  , End 
  , image
  , invmap
  , augment
  , (!#)
  , (#!)
  , (!#!)
  -- * Dimensional transforms
  , braid
  , cobraid 
  , split
  , cosplit
  , projl
  , projr
  , compl
  , compr
  , complr
  -- * Algebraic transforms
  , diagonal
  , codiagonal
  , initial
  , coinitial
  , convolve
) where

import safe Control.Applicative
import safe Control.Arrow
import safe Control.Category (Category, (<<<), (>>>))
import safe Control.Monad (MonadPlus(..))
import safe Data.Foldable (foldl')
import safe Data.Functor.Apply
import safe Data.Functor.Contravariant (Contravariant(..))
import safe Data.Functor.Rep
import safe Data.Profunctor
import safe Data.Profunctor.Sieve
import safe Data.Semimodule
import safe Data.Semiring
import safe Data.Tuple (swap)
import safe Prelude hiding (Num(..), Fractional(..), init, negate, sum, product)
import safe Test.Logic hiding (join)
import safe qualified Control.Category as C
import safe qualified Data.Profunctor.Rep as PR

-------------------------------------------------------------------------------
-- Vectors
-------------------------------------------------------------------------------

infixr 3 `runVec`

-- | A vector in a vector space or free semimodule.
--
-- Equivalent to < https://hackage.haskell.org/package/base/docs/Data-Functor-Contravariant.html#t:Op Op >.
--
-- Vectors transform contravariantly as a function of their bases.
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
newtype Vec a b = Vec { runVec :: b -> a }

infixr 7 !*

-- | Apply a covector to a vector on the right.
--
(!*) :: Vec a b -> Cov a b -> a 
(!*) = flip (*!)

infixl 7 *!

-- | Apply a covector to a vector on the left.
--
(*!) :: Cov a b -> Vec a b -> a
(*!) f = runCov f . runVec

-- | Use a linear transformation to map over a vector space.
--
-- Note that the basis transforms < https://en.wikipedia.org/wiki/Covariant_transformation#Contravariant_transformation > contravariantly.
--
vmap :: Lin a b c -> Vec a c -> Vec a b
vmap f g = Vec $ runLin f (runVec g)

-- | Obtain a vector from a vector on the tensor product space.
--
join :: Algebra a b => Vec a (b, b) -> Vec a b
join = vmap diagonal

-- | Obtain a vector from the unit of a unital algebra.
--
-- @
-- 'init' a = 'vmap' 'initial' ('Vec' $ \_ -> a)
-- @
--
init :: Unital a b => a -> Vec a b
init = Vec . unital

infixr 7 !*!

-- | Multiplication operator on an algebra over a free semimodule.
--
-- >>> flip runVec E22 $ (vec $ V2 1 2) !*! (vec $ V2 7 4)
-- 8
--
-- /Caution/ in general 'mult' needn't be commutative, nor associative.
--
(!*!) :: Algebra a b => Vec a b -> Vec a b -> Vec a b
(!*!) x y = Vec $ joined (\i j -> runVec x i * runVec y j)

-------------------------------------------------------------------------------
-- Covectors
-------------------------------------------------------------------------------


infixr 3 `runCov`

-- | Linear functionals from elements of a free semimodule to a scalar.
--
-- @ 
-- f '!*' (x '+' y) = (f '!*' x) '+' (f '!*' y)
-- f '!*' (x '.*' a) = a '*' (f '!*' x)
-- @
--
-- /Caution/: You must ensure these laws hold when using the default constructor.
--
-- Co-vectors transform covariantly as a function of their bases.
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
newtype Cov a c = Cov { runCov :: (c -> a) -> a }

-- | Obtain a covector from a linear combination of basis elements.
--
-- >>> images [(2, E31),(3, E32)] !* vec (V3 1 1 1) :: Int
-- 5
--
images :: Semiring a => Foldable f => f (a, c) -> Cov a c
images f = Cov $ \k -> foldl' (\acc (a, c) -> acc + a * k c) zero f 

-- | Use a linear transformation to map over a dual space.
--
-- Note that the basis transforms < https://en.wikipedia.org/wiki/Covariant_transformation covariantly >.
--
cmap :: Lin a b c -> Cov a b -> Cov a c
cmap f g = Cov $ runCov g . runLin f

-- | Obtain a covector from a covector on the tensor product space.
--
cojoin :: Coalgebra a c => Cov a (c, c) -> Cov a c
cojoin = cmap codiagonal

-- | Obtain a covector from the counit of a counital coalgebra.
--
-- @
-- 'coinit' = 'cmap' 'coinitial' ('Cov' $ \f -> f ())
-- @
--
coinit :: Counital a c => Cov a c
coinit = Cov counital

infixr 7 `comult`

-- | Multiplication operator on a coalgebra over a free semimodule.
--
-- >>> flip runCov (e2 1 1) $ comult (cov $ V2 1 2) (cov $ V2 7 4)
-- 11
--
-- /Caution/ in general 'comult' needn't be commutative, nor coassociative.
--
comult :: Coalgebra a c => Cov a c -> Cov a c -> Cov a c
comult (Cov f) (Cov g) = Cov $ \k -> f (\m -> g (cojoined k m))

-------------------------------------------------------------------------------
-- Linear transformations
-------------------------------------------------------------------------------

-- | A linear transformation between free semimodules indexed with bases /b/ and /c/.
--
-- @
-- f '!#' x '+' y = (f '!#' x) + (f '!#' y)
-- f '!#' (r '.*' x) = r '.*' (f '!#' x)
-- @
--
-- /Caution/: You must ensure these laws hold when using the default constructor.
--
-- Prefer 'image' or 'Data.Semimodule.Combinator.tran' where appropriate.
--
newtype Lin a b c = Lin { runLin :: (c -> a) -> b -> a }

-- | An endomorphism over a free semimodule.
--
-- >>> one + two !# V2 1 2 :: V2 Double
-- V2 3.0 6.0
--
type End a b = Lin a b b

-- | Create a 'Lin' from a linear combination of basis vectors.
--
-- >>> image (e2 [(2, E31),(3, E32)] [(1, E33)]) !# V3 1 1 1 :: V2 Int
-- V2 5 1
--
image :: Semiring a => (b -> [(a, c)]) -> Lin a b c
image f = Lin $ \k b -> sum [ a * k c | (a, c) <- f b ]

-- | 'Lin' is an invariant functor.
--
-- See also < http://comonad.com/reader/2008/rotten-bananas/ >.
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Lin a1 b c -> Lin a2 b c
invmap f g (Lin t) = Lin $ \x -> t (x >>> g) >>> f

-- | The < https://en.wikipedia.org/wiki/Augmentation_(algebra) augmentation > ring homomorphism.
--
augment :: Semiring a => Lin a b c -> b -> a
augment l = l !# const one

infixr 2 !#

-- | Apply a transformation to a vector.
--
(!#) :: Free f => Free g => Lin a (Rep f) (Rep g) -> g a -> f a
(!#) t = tabulate . runLin t . index

infixl 2 #!

-- | Apply a transformation to a vector.
--
(#!) :: Free f => Free g => g a -> Lin a (Rep f) (Rep g) -> f a
(#!) = flip (!#)

infixr 2 !#!

-- | Compose two transformations.
--
-- '!#!' = '<<<'
--
(!#!) :: Lin a c d -> Lin a b c -> Lin a b d
(!#!) = (C..)

-------------------------------------------------------------------------------
-- Common linear transformations
-------------------------------------------------------------------------------

-- | Swap components of a tensor product.
--
-- This is equivalent to a matrix transpose.
--
braid :: Lin a (b , c) (c , b)
braid = arr swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
cobraid :: Lin a (b + c) (c + b)
cobraid = arr eswap
{-# INLINE cobraid #-}

-- | TODO: Document
--
split :: (b -> (b1 , b2)) -> Lin a b1 c -> Lin a b2 c -> Lin a b c
split f x y = dimap f fst $ x *** y
{-# INLINE split #-}

-- | TODO: Document
--
cosplit :: ((c1 + c2) -> c) -> Lin a b c1 -> Lin a b c2 -> Lin a b c
cosplit f x y = dimap Left f $ x +++ y
{-# INLINE cosplit #-}

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
compl :: Free f1 => Free f2 => Free g => Lin a (Rep f1) (Rep f2) -> (f2**g) a -> (f1**g) a
compl t fg = first t !# fg

-- | Right (pre) composition with a linear transformation.
--
compr :: Free f => Free g1 => Free g2 => Lin a (Rep g1) (Rep g2) -> (f**g2) a -> (f**g1) a
compr t fg = second t !# fg

-- | Left and right composition with a linear transformation.
--
-- @ 'complr' f g = 'compl' f '>>>' 'compr' g @
--
complr :: Free f1 => Free f2 => Free g1 => Free g2 => Lin a (Rep f1) (Rep f2) -> Lin a (Rep g1) (Rep g2) -> (f2**g2) a -> (f1**g1) a
complr t1 t2 fg = t1 *** t2 !# fg

-------------------------------------------------------------------------------
-- Algebraic transformations
-------------------------------------------------------------------------------

-- |
--
-- @
-- 'rmap' (\((c1,()),(c2,())) -> (c1,c2)) '$' ('C.id' '***' 'initial') 'C..' 'diagonal' = 'C.id'
-- 'rmap' (\(((),c1),((),c2)) -> (c1,c2)) '$' ('initial' '***' 'C.id') 'C..' 'diagonal' = 'C.id'
-- @
--
diagonal :: Algebra a b => Lin a b (b,b)
diagonal = Lin $ joined . curry

{-

prop_cojoined (~~) f = (codiagonal !# f) ~~ (Compose . tabulate $ \i -> tabulate $ \j -> cojoined (index f) i j)

-- trivial coalgebra
prop_codiagonal' (~~) f = (codiagonal !# f) ~~ (Compose $ flip imapRep f $ \i x -> flip imapRep f $ \j _ -> bool zero x $ (i == j))

-- trivial coalgebra
prop_codiagonal (~~) f = (codiagonal !# f) ~~ (flip bindRep id . getCompose $ f)

prop_diagonal (~~) f = (diagonal !# f) ~~ (tabulate $ joined (index . index (getCompose f)))
-}

-- |
--
-- @
-- 'lmap' (\(c1,c2) -> ((c1,()),(c2,()))) '$' ('C.id' '***' 'coinitial') 'C..' 'codiagonal' = 'C.id'
-- 'lmap' (\(c1,c2) -> (((),c1),((),c2))) '$' ('coinitial' '***' 'C.id') 'C..' 'codiagonal' = 'C.id'
-- @
--
codiagonal :: Coalgebra a c => Lin a (c,c) c
codiagonal = Lin $ uncurry . cojoined

-- | TODO: Document
--
initial :: Unital a b => Lin a b ()
initial = Lin $ \k -> unital $ k ()

-- | TODO: Document
--
coinitial :: Counital a c => Lin a () c
coinitial = Lin $ const . counital

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
convolve :: Algebra a b => Coalgebra a c => Lin a b c -> Lin a b c -> Lin a b c
convolve f g = codiagonal <<< (f *** g) <<< diagonal

-------------------------------------------------------------------------------
-- Vec instances
-------------------------------------------------------------------------------

addVec :: (Additive-Semigroup) a => Vec a b -> Vec a b -> Vec a b
addVec (Vec f) (Vec g) = Vec $ \b -> f b + g b

subVec :: (Additive-Group) a => Vec a b -> Vec a b -> Vec a b
subVec (Vec f) (Vec g) = Vec $ \b -> f b - g b

instance Contravariant (Vec a) where
  contramap f g = Vec (runVec g . f)

instance Category Vec where
  id = Vec id
  Vec f . Vec g = Vec (g . f)

instance (Additive-Semigroup) a => Semigroup (Additive (Vec a b)) where
  (<>) = liftA2 addVec

instance (Additive-Monoid) a => Monoid (Additive (Vec a b)) where
  mempty = Additive . Vec $ const zero

instance (Additive-Group) a => Magma (Additive (Vec a b)) where
  (<<) = liftA2 subVec

instance (Additive-Group) a => Quasigroup (Additive (Vec a b))
instance (Additive-Group) a => Loop (Additive (Vec a b))
instance (Additive-Group) a => Group (Additive (Vec a b))

instance Semiring a => LeftSemimodule a (Vec a b) where
  lscale a v = Vec $ \b -> a *. runVec v b

instance Semiring a => LeftSemimodule (End a b) (Vec a b) where
  lscale = vmap

instance Semiring a => RightSemimodule a (Vec a b) where
  rscale a v = Vec $ \b -> runVec v b .* a

instance Semiring a => RightSemimodule (End a b) (Vec a b) where
  rscale = vmap

instance Semiring a => Bisemimodule (End a b) (End a b) (Vec a b)

instance Bisemimodule a a a => Bisemimodule a a (Vec a b)

-------------------------------------------------------------------------------
-- Cov instances
-------------------------------------------------------------------------------

instance Functor (Cov a) where
  fmap f m = Cov $ \k -> m `runCov` k . f

instance Applicative (Cov a) where
  pure a = Cov $ \k -> k a
  mf <*> ma = Cov $ \k -> mf `runCov` \f -> ma `runCov` k . f

instance Monad (Cov a) where
  return a = Cov $ \k -> k a
  m >>= f = Cov $ \k -> m `runCov` \a -> f a `runCov` k

instance (Additive-Monoid) a => Alternative (Cov a) where
  Cov m <|> Cov n = Cov $ m + n
  empty = Cov zero

instance (Additive-Monoid) a => MonadPlus (Cov a) where
  Cov m `mplus` Cov n = Cov $ m + n
  mzero = Cov zero
{-
newtype Vect a b = Vect (b -> a)

instance ((Additive-Semigroup) a) => Semigroup (Additive (Vect a b)) where
  Additive (Vect f) <> Additive (Vect g) = Additive . Vect $ \b -> f b + g b
  {-# INLINE (<>) #-}

instance ((Additive-Monoid) a) => Monoid (Additive (Vect a b)) where
  mempty = Additive . Vect $ const zero

instance ((Additive-Group) a) => Magma (Additive (Vect a b)) where
  Additive (Vect f) << Additive (Vect g) = Additive . Vect $ \b -> f b - g b
  {-# INLINE (<<) #-}

instance ((Additive-Group) a) => Quasigroup (Additive (Vect a b))
instance ((Additive-Group) a) => Loop (Additive (Vect a b)) where
instance ((Additive-Group) a) => Group (Additive (Vect a b))
-}

instance (Additive-Semigroup) a => Semigroup (Additive (Cov a b)) where
  (<>) = liftA2 $ \(Cov m) (Cov n) -> Cov $ m + n

instance (Additive-Monoid) a => Monoid (Additive (Cov a b)) where
  mempty = Additive $ Cov zero

instance (Additive-Group) a => Magma (Additive (Cov a b)) where
  (<<) = liftA2 $ \(Cov m) (Cov n) -> Cov $ m - n

instance (Additive-Group) a => Quasigroup (Additive (Cov a b))
instance (Additive-Group) a => Loop (Additive (Cov a b))
instance (Additive-Group) a => Group (Additive (Cov a b))

instance Semiring a => LeftSemimodule a (Cov a b) where
  lscale s m = Cov $ \k -> s *. runCov m k

instance Counital a b => LeftSemimodule (End a b) (Cov a b) where
  lscale = cmap

instance Semiring a => RightSemimodule a (Cov a b) where
  rscale s m = Cov $ \k -> runCov m k .* s

instance Counital a b => RightSemimodule (End a b) (Cov a b) where
  rscale = cmap

instance Counital a b => Bisemimodule (End a b) (End a b) (Cov a b)

instance Bisemimodule a a a => Bisemimodule a a (Cov a b)

-------------------------------------------------------------------------------
-- Lin instances
-------------------------------------------------------------------------------

addLin :: (Additive-Semigroup) a => Lin a b c -> Lin a b c -> Lin a b c
addLin (Lin f) (Lin g) = Lin $ f + g

subLin :: (Additive-Group) a => Lin a b c -> Lin a b c -> Lin a b c
subLin (Lin f) (Lin g) = Lin $ \h -> f h - g h

-- mulLin :: (Multiplicative-Semigroup) a => Lin a b c -> Lin a b c -> Lin a b c
-- mulLin (Lin f) (Lin g) = Lin $ \h -> f h * g h

instance Functor (Lin a b) where
  fmap f m = Lin $ \k -> m !# k . f

instance Category (Lin a) where
  id = Lin id
  Lin f . Lin g = Lin $ g . f

instance Apply (Lin a b) where
  mf <.> ma = Lin $ \k b -> (mf !# \f -> (ma !# k . f) b) b

instance Applicative (Lin a b) where
  pure a = Lin $ \k _ -> k a
  (<*>) = (<.>)

instance Profunctor (Lin a) where
  -- | 'Lin' is a profunctor in the category of semimodules.
  --
  -- /Caution/: Arbitrary mapping functions may violate linearity.
  --
  -- >>> dimap id (e3 True True False) (arr id) !# 4 :+ 5 :: V3 Int
  -- V3 5 5 4
  --
  dimap l r f = arr r <<< f <<< arr l

instance Strong (Lin a) where
  first' = first
  second' = second

instance Choice (Lin a) where
  left' = left
  right' = right

instance Sieve (Lin a) (Cov a) where
  sieve l b = Cov $ \k -> (l !# k) b 

instance PR.Representable (Lin a) where
  type Rep (Lin a) = Cov a
  tabulate f = Lin $ \k b -> runCov (f b) k

instance Monad (Lin a b) where
  return a = Lin $ \k _ -> k a
  m >>= f = Lin $ \k b -> (m !# \a -> (f a !# k) b) b

instance Arrow (Lin a) where
  arr f = Lin (. f)
  first m = Lin $ \k (a,c) -> (m !# \b -> k (b,c)) a
  second m = Lin $ \k (c,a) -> (m !# \b -> k (c,b)) a
  m *** n = Lin $ \k (a,c) -> (m !# \b -> (n !# \d -> k (b,d)) c) a
  m &&& n = Lin $ \k a -> (m !# \b -> (n !# \c -> k (b,c)) a) a

instance ArrowChoice (Lin a) where
  left m = Lin $ \k -> either (m !# k . Left) (k . Right)
  right m = Lin $ \k -> either (k . Left) (m !# k . Right)
  m +++ n =  Lin $ \k -> either (m !# k . Left) (n !# k . Right)
  m ||| n = Lin $ \k -> either (m !# k) (n !# k)

instance ArrowApply (Lin a) where
  app = Lin $ \k (f,a) -> (f !# k) a

instance (Additive-Semigroup) a => Semigroup (Additive (Lin a b c)) where
  (<>) = liftA2 addLin

instance (Additive-Monoid) a => Monoid (Additive (Lin a b c)) where
  mempty = pure . Lin $ const zero

instance Presemiring a => Semigroup (Multiplicative (End a b)) where
  (<>) = liftA2 (<<<)

instance Semiring a => Monoid (Multiplicative (End a b)) where
  mempty = pure C.id

instance Presemiring a => Presemiring (End a b)
instance Semiring a => Semiring (End a b)
instance Ring a => Ring (End a b)

 
{-
instance Coalgebra a c => Semigroup (Multiplicative (Lin a b c)) where
  (<>) = liftR2 $ \ f g -> Lin $ \k b -> (f !# \a -> (g !# cojoined k a) b) b

instance Counital a c => Monoid (Multiplicative (Lin a b c)) where
  mempty = pure . Lin $ \k _ -> counital k

instance Coalgebra a c => Presemiring (Lin a b c)
instance Counital a c => Semiring (Lin a b c)
instance (Ring a, Counital a c) => Ring (Lin a b c)
-}

instance Counital a b => LeftSemimodule (Lin a b b) (Lin a b c) where
  -- | Left matrix multiplication
  lscale = (>>>)

instance Semiring a => LeftSemimodule a (Lin a b c) where
  lscale l (Lin m) = Lin $ \k b -> l *. m k b

instance Counital a c => RightSemimodule (Lin a c c) (Lin a b c) where
  -- | Right matrix multiplication
  rscale = (<<<)

instance (Counital a b, Counital a c) => Bisemimodule (Lin a b b) (Lin a c c) (Lin a b c)

instance Semiring a => RightSemimodule a (Lin a b m) where
  rscale r (Lin m) = Lin $ \k b -> m k b .* r

instance Bisemimodule a a a => Bisemimodule a a (Lin a b c)

instance (Additive-Group) a => Magma (Additive (Lin a b c)) where
  (<<) = liftR2 subLin

instance (Additive-Group) a => Quasigroup (Additive (Lin a b c))
instance (Additive-Group) a => Loop (Additive (Lin a b c))
instance (Additive-Group) a => Group (Additive (Lin a b c))

{-
-- | An endomorphism of endomorphisms. 
--
-- @ 'Cayley' a = (a -> a) -> (a -> a) @
--
type Cayley a = Lin a a a

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
cayley a = Lin $ \k b -> a * k zero + b

-- | Extract a semiring element from a 'Cayley'.
--
-- >>> runCayley $ two * (one + (cayley 3.4)) :: Double
-- 8.8
-- >>> runCayley $ two * (one + (cayley $ m22 1 2 3 4)) :: M22 Int
-- Compose (V2 (V2 4 4) (V2 6 10))
--
runCayley :: Semiring a => Cayley a -> a
runCayley (Lin f) = f (one +) zero

-- ring homomorphism from a -> a^b
embed :: (Multiplicative-Semigroup) a => (Multiplicative-Monoid) c => (b -> a) -> Lin a b c
embed f = Lin $ \k b -> f b * k one

-- if the characteristic of s does not divide the order of a, then s[a] is semisimple
-- and if a has a length function, we can build a filtered algebra
-}
