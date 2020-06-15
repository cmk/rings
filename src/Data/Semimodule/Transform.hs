{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}

module Data.Semimodule.Transform (
    type Free
  , type (**)
  , type (++)
    -- * Transforms
  , Transform(..)
  , type Matrix
  , matrix
  , images
  , invmap
  , liftEndo, lowerEndo
    -- ** Column & row vectors
  , type Col
  , pattern Col
  , runCol
  , type Row
  , pattern Row
  , runRow
  , coeffs
  , augment
  , inner
    -- * Operations
  , (.#), (#.), (.#.)
  , lcomp, rcomp, dicomp 
    -- ** Algebraic operations
  , final
  , initial, coinitial
  , diagonal, codiagonal
  , join, cojoin
  , (.*.), (.+.)
  , convolve
    -- ** Arrows
  , fork, cofork
  , swap, coswap
  , ex1, ex2
  , inl, inr
  , eta, eta2
  , apply, unapply
  , braid, cobraid
  , (***), (+++)
  , (&&&), (|||)
  , divideL, divideR
  , chooseL, chooseR
) where

import safe Control.Applicative
import safe Control.Category
import safe Control.Monad hiding (join)
import safe Control.Monad.Trans.Cont
import safe Data.Finite (Finite, finites)
import safe Data.Foldable (foldl')
import safe Data.Functor.Alt
import safe Data.Functor.Compose
import safe Data.Functor.Product
import safe Data.Functor.Rep
import safe Data.Group
import safe Data.Lattice hiding (join)
--import safe Data.Lattice.Heyting
import safe Data.Monoid hiding (Alt(..), Sum(..), Product(..))
--import safe Data.Order
import safe Data.Profunctor
import safe Data.Profunctor.Composition
import safe Data.Profunctor.Sieve
import safe Data.Ring
import safe Data.Semigroup.Quantale
import safe Data.Semigroup.Additive
import safe Data.Semimodule
import safe Data.Semimodule.Algebra
import safe Data.Semiring
import safe Data.Tuple (swap)
import safe Data.Void
import safe GHC.TypeNats (KnownNat)
import safe Prelude hiding (Num(..), Fractional(..), Ord(..), Bounded, not, id, (.), (^), init, negate, sum, product)
import safe qualified Data.Profunctor.Rep as PR

type Free = Representable

-------------------------------------------------------------------------------
-- Transform
-------------------------------------------------------------------------------

-- | An unreified transformation between free semimodules indexed with bases /b/ and /c/.
--
-- When the transformation is linear we must have:
-- @
-- f '.#' (x '+' y) = (f '.#' x) + (f '.#' y)
-- f '.#' (r '.*' x) = r '.*' (f '.#' x)
-- @
--
-- Usable with a wide range of vector representations, for example via < http://hackage.haskell.org/package/vector-sized-1.4.0.0/docs/Data-Col-Sized.html#v:generate >
--
newtype Transform a b c = Transform { runTransform :: (c -> a) -> b -> a }

-- | A map between finite dimensional vector spaces with dimensions /m/ & /n/.
--
-- Useful esp. when the matrix is large and sparse.
--
type Matrix a m n = Transform a (Finite m) (Finite n)

-- | Obtain a 'Transform' from a function of row and column indices.
--
matrix :: (KnownNat n, Semiring a) => (Finite m -> Finite n -> a) -> Matrix a m n 
matrix f = images $ \i -> (id &&& f i) <$> finites

-- | Obtain a 'Transform' from the images of row basis elements.
--
images :: (Semiring a, Foldable f) => (b -> f (c, a)) -> Transform a b c
images f = Transform $ \k -> foldl' (\acc (c, a) -> acc + a * k c) zero . f

-- | 'Transform' is an invariant functor.
--
-- > invmap Data.Connection.left Data.Connection.right :: Connection a1 a2 => Transform a1 b c -> Transform a2 b c
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Transform a1 b c -> Transform a2 b c
invmap f g (Transform t) = Transform $ \x -> t (x >>> g) >>> f

-- | Lift a semiring element into an endomorphism semiring.
--
-- @ 'lowerEndo' . 'liftEndo' = 'id' @
--
-- >>> lowerEndo . liftEndo $ 3.4 :: Double
-- 3.4
-- >>> lowerEndo . liftEndo $ m22 1 2 3 4 :: M22 Int
-- Compose (V2 (V2 1 2) (V2 3 4))
-- 
liftEndo :: Semiring a => a -> Transform a a a
liftEndo a = Transform $ \k b -> a * k zero + b

-- | Extract a semiring element from an liftEndomorphism semiring.
--
-- >>> lowerEndo $ (one + one) * (one + (liftEndo 3.4)) :: Double
-- 8.8
-- >>> lowerEndo $ (one + one) * (one + (liftEndo $ m22 1 2 3 4)) :: M22 Int
-- Compose (V2 (V2 4 4) (V2 6 10))
--
lowerEndo :: Semiring a => Transform a a a -> a
lowerEndo (Transform f) = f (one +) zero

-------------------------------------------------------------------------------
-- Vectors & co-vectors
-------------------------------------------------------------------------------

-- | A (column) vector in a vector space or free semimodule, represented as an index function.
--
-- Equivalent to 'Data.Functor.Contravariant.Op'.
--
-- Vectors transform contravariantly as a function of their bases:
--
-- > (>>>) :: Transform a b c -> Col a c -> Col a b
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
type Col a b = Transform a b Void

pattern Col :: (b -> a) -> Col a b
pattern Col r <- (runCol -> r) where Col f = Transform $ \_ -> f

runCol :: Col a b -> b -> a
runCol (Transform t) = t absurd

-- | A co-vector on a free semimodule.
--
-- @ 
-- f '!*' (x '+' y) = (f '!*' x) '+' (f '!*' y)
-- f '!*' (x '.*' a) = a '*' (f '!*' x)
-- @
--
-- /Caution/: You must ensure these laws hold when using the default constructor.
--
-- Co-vectors transform co-variantly as function of their bases.
--
-- > (<<<) :: Transform a b c -> Row a b -> Row a c
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
type Row a c = Transform a () c

pattern Row :: ((c -> a) -> a) -> Row a c
pattern Row r <- (runRow -> r) where Row f = Transform $ \k _ -> f k

runRow :: Row a c -> (c -> a) -> a
runRow (Transform t) k = t k ()

-- | Obtain a co-vector from a linear combination of basis elements.
--
coeffs :: (Semiring a, Foldable f) => f (c, a) -> Row a c
coeffs f = Row $ \k -> foldl' (\acc (c, a) -> acc + a * k c) zero f 

-- | The < https://en.wikipedia.org/wiki/Augmentation_(algebra) augmentation > ring homomorphism.
--
augment :: Semiring a => Transform a b c -> Col a b
augment l = Col $ l .# const one

-- | A (typically linear) functional.
--
-- See also 'Data.Semimodule.Free.dot'.
--
inner :: Row a b -> Col a b -> a
inner (runRow -> r) (runCol -> c) = r c

{-
-- | Apply a co-vector to a vector from the left.
--
innerL :: Free f => Row a (Rep f) -> f a -> a 
innerL (runRow -> r) = r . index 

-- | Apply a co-vector to a vector from the right.
--
innerR :: Free f => f a -> Row a (Rep f) -> a
innerR = flip innerL
-}

-------------------------------------------------------------------------------
-- Operations
-------------------------------------------------------------------------------

infixr 2 .#

-- | Apply a transformation to a reified vector.
--
(.#) :: (Free f, Free g) => Transform a (Rep f) (Rep g) -> g a -> f a
(.#) (Transform t) = tabulate . t . index

infixl 2 #.

-- | Apply a transformation to a reified vector, from the right.
--
(#.) :: (Free f, Free g) => g a -> Transform a (Rep f) (Rep g) -> f a
(#.) = flip (.#)

infixr 2 .#.

-- | Compose two transformations.
--
-- Provided for convenience, this function is just a specialization 
-- of `(.)` with lower fixity.
--
-- > (.#.) = (.) = (<<<)
--
(.#.) :: Transform a c d -> Transform a b c -> Transform a b d
(.#.) = (.)

-- | Left (post) composition with a linear transformation.
--
lcomp :: (Free f1, Free f2, Free g) => Transform a (Rep f1) (Rep f2) -> (f2**g) a -> (f1**g) a
lcomp t fg = first' t .# fg

-- | Right (pre) composition with a linear transformation.
--
rcomp :: (Free f, Free g1, Free g2) => Transform a (Rep g1) (Rep g2) -> (f**g2) a -> (f**g1) a
rcomp t fg = second' t .# fg

-- | Left and right composition with a linear transformation.
--
-- @ 'dicomp' f g = ('lcomp' f '.' 'rcomp' g '!#') @
--
dicomp :: (Free f1, Free f2, Free g1, Free g2) => Transform a (Rep f1) (Rep f2) -> Transform a (Rep g1) (Rep g2) -> (f2**g2) a -> (f1**g1) a
dicomp f g x = f *** g .# x

-------------------------------------------------------------------------------
-- Algebraic operations
-------------------------------------------------------------------------------

-- | TODO: Document
--
final :: Unital a b => Transform a b ()
final = Transform $ \k -> unital $ k ()

-- | Obtain a vector from the unit of a unital coalgebra.
--
initial :: Unital a b => a -> Col a b
initial = Col . unital

-- | Obtain a covector from the counit of a counital coalgebra.
--
coinitial :: Counital a c => Row a c
coinitial = Row counital

-- | Diagonal tranform into the tensor product space.
--
-- @
-- 'eta' (\((c1,()),(c2,())) -> (c1,c2)) '<<<' ('id' '***' 'initial') '.' 'diagonal' = 'id'
-- 'eta' (\(((),c1),((),c2)) -> (c1,c2)) '<<<' ('initial' '***' 'id') '.' 'diagonal' = 'id'
-- @
--
diagonal :: Algebra a b => Transform a b (b, b)
diagonal = Transform $ joined . curry

-- | Codiagonal transform out of the tensor product space.
--
-- @
-- 'eta' (\(c1,c2) -> ((c1,()),(c2,()))) '>>>' ('id' '***' 'coinitial') '.' 'codiagonal' = 'id'
-- 'eta' (\(c1,c2) -> (((),c1),((),c2))) '>>>' ('coinitial' '***' 'id') '.' 'codiagonal' = 'id'
-- @
--
codiagonal :: Coalgebra a c => Transform a (c, c) c
codiagonal = Transform $ uncurry . cojoined

-- | Obtain a vector from a vector on the tensor product space.
--
join :: Algebra a b => Col a (b, b) -> Col a b
join = (. diagonal)

-- | Obtain a covector from a covector on the tensor product space.
--
cojoin :: Coalgebra a c => Row a (c, c) -> Row a c
cojoin = (codiagonal .)

infixl 7 .*.

-- | Binary operator on an algebra over a free semimodule.
--
-- Note that '.*.' needn't be commutative, nor associative.
--
(.*.) :: Algebra a b => Col a b -> Col a b -> Col a b
(.*.) (runCol -> f) (runCol -> g) = Col . joined $ \i j -> f i * g j

infixr 6 .+.

-- | Binary operator on a coalgebra over a free semimodule.
--
-- Note that '.+.' needn't be commutative, nor associative.
--
(.+.) :: Coalgebra a c => Row a c -> Row a c -> Row a c
(.+.) (runRow -> f) (runRow -> g) = Row $ \k -> f (\l -> g (cojoined k l))

-- | Convolution with an associative algebra and coassociative coalgebra
--
convolve :: (Algebra a b, Coalgebra a c) => Transform a b c -> Transform a b c -> Transform a b c
convolve f g = codiagonal . (f *** g) . diagonal

-------------------------------------------------------------------------------
-- Arrows
-------------------------------------------------------------------------------

fork :: a -> (a, a)
fork x = (x, x)

cofork :: Either a a -> a
cofork = either id id

coswap :: Either a b -> Either b a
coswap = either Right Left

ex1 :: (Category p, Profunctor p) => p (a , b) b
ex1 = eta snd
{-# INLINE ex1 #-}

ex2 :: (Category p, Profunctor p) => p (a , b) a
ex2 = eta fst
{-# INLINE ex2 #-}

inl :: (Category p, Profunctor p) => p a (Either a b)
inl = eta Left
{-# INLINE inl #-}

inr :: (Category p, Profunctor p) => p b (Either a b)
inr = eta Right
{-# INLINE inr #-}

eta2 :: (Category p, Strong p) => (b1 -> b2 -> b) -> p a b1 -> p a b2 -> p a b
eta2 = divideR . uncurry

apply :: (Category p, Strong p) => p a (b -> c) -> p a b -> p a c
apply = eta2 id
{-# INLINE apply #-}

-- > unapply . apply = id
-- > apply . unapply = id
--
unapply :: (Category p, Strong p, Closed p) => p a c -> p b c -> p a (b -> c)
unapply = (curry' .) . divideL id
{-# INLINE unapply #-}

-- | Swap components of a tensor product.
--
braid :: (Category p, Profunctor p) => p (a , b) (b , a)
braid = eta swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
cobraid :: (Category p, Profunctor p) => p (Either a b) (Either b a)
cobraid = eta coswap
{-# INLINE cobraid #-}

infixr 3 ***

(***) :: Category p => Strong p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
x *** y = eta swap . first' y . eta swap . first' x
{-# INLINE (***) #-}

infixr 2 +++

(+++) :: Category p => Choice p => p a1 b1 -> p a2 b2 -> p (Either a1 a2) (Either b1 b2)
x +++ y = eta coswap . left' y . eta coswap . left' x
{-# INLINE (+++) #-}

infixr 3 &&&

(&&&) :: Category p => Strong p => p a b1 -> p a b2 -> p a (b1 , b2)
x &&& y = dimap fork id $ x *** y
{-# INLINE (&&&) #-}

infixr 2 |||

(|||) :: Category p => Choice p => p a1 b -> p a2 b -> p (Either a1 a2) b
x ||| y = dimap id cofork $ x +++ y
{-# INLINE (|||) #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:divide divide >.
--
divideL :: (Category p, Strong p) => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
divideL f x y = dimap f fst $ x *** y
{-# INLINE divideL #-}

-- > divideR f x y = tabulate $ \s -> liftA2 (curry f) (sieve x s) (sieve y s)
divideR :: (Category p, Strong p) => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
divideR f p q = dimap fork f $ p *** q
{-# INLINE divideR #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:choose choose >.
--
chooseL :: (Category p, Choice p) => (a -> Either a1 a2) -> p a1 b -> p a2 b -> p a b 
chooseL f p q = dimap f cofork $ p +++ q
{-# INLINE chooseL #-}

chooseR :: (Category p, Choice p) => (Either b1 b2 -> b) -> p a b1 -> p a b2 -> p a b
chooseR f x y = dimap Left f $ x +++ y
{-# INLINE chooseR #-}

-------------------------------------------------------------------------------
-- Transform instances
-------------------------------------------------------------------------------

instance Functor (Transform a b) where
  fmap f m = Transform $ \k -> m .# k . f

instance Category (Transform a) where
  id = Transform id
  Transform f . Transform g = Transform $ g . f

instance Apply (Transform a b) where
  mf <.> ma = Transform $ \k b -> (mf .# \f -> (ma .# k . f) b) b

instance Applicative (Transform a b) where
  pure a = Transform $ \k _ -> k a
  (<*>) = (<.>)

instance Monad (Transform a b) where
  return a = Transform $ \k _ -> k a
  m >>= f = Transform $ \k b -> (m .# \a -> (f a .# k) b) b

instance Semigroup (Join a) => Semigroup (Join (Transform a b c)) where
  (<>) = liftA2 $ \(Transform f) (Transform g) -> Transform $ f \/ g

instance Monoid (Join a) => Monoid (Join (Transform a b c)) where
  mempty = pure . Transform $ \_ -> const bottom

instance Semigroup (Meet a) => Semigroup (Meet (Transform a b c)) where
  (<>) = liftA2 $ \(Transform f) (Transform g) -> Transform $ f /\ g

instance Monoid (Meet a) => Monoid (Meet (Transform a b c)) where
  mempty = pure . Transform $ \_ -> const top

--TODO: check, probably not the instance you want
instance Quantale (Meet a) => Quantale (Meet (Transform a b c)) where
  (//) = liftA2 $ \(Transform f) (Transform g) -> Transform $ f <== g
  (\\) = flip (//)

{-
type PreorderLaw a b c = (U.Finite a, U.Finite b, U.Finite c, Preorder a, Order c)

instance PreorderLaw a b c => Preorder (Transform a b c) where
  pcompare (Transform f) (Transform g) = pcompare f g

instance Lattice a => Lattice (Transform a b c)
instance Bounded a => Bounded (Transform a b c)
instance Distributive a => Distributive (Transform a b c)
instance Heyting a => Heyting (Transform a b c)
-}

instance Semigroup (Additive a) => Semigroup (Additive (Transform a b c)) where
  (<>) = liftA2 $ \(Transform f) (Transform g) -> Transform $ f + g

instance Monoid (Additive a) => Monoid (Additive (Transform a b c)) where
  mempty = pure . Transform $ \_ -> const zero

instance Group (Additive a) => Group (Additive (Transform a b c)) where
  invert = fmap $ invmap negate id

instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (Transform a b c)) where
  (<>) = liftA2 $ \(Transform f) (Transform g) -> Transform $ f * g

instance Monoid (Multiplicative a) => Monoid (Multiplicative (Transform a b c)) where
  mempty = pure . Transform $ \_ -> const one

instance Presemiring a => Presemiring (Transform a b c)
instance Semiring a => Semiring (Transform a b c)
instance Ring a => Ring (Transform a b c)

instance Semiring a => LeftSemimodule (Transform a b b) (Transform a b c) where
  -- | Left matrix multiplication
  lscale = flip (.)
instance Semiring a => LeftSemimodule a (Transform a b c) where
  lscale l (Transform m) = Transform $ \k b -> l * m k b
instance Semiring a => RightSemimodule (Transform a c c) (Transform a b c) where
  -- | Right matrix multiplication
  rscale = (.)
instance Semiring a => Bisemimodule (Transform a b b) (Transform a c c) (Transform a b c)
instance Semiring a => RightSemimodule a (Transform a b m) where
  rscale r (Transform m) = Transform $ \k b -> m k b * r
instance Semiring a => Bisemimodule a a (Transform a b c)

instance Profunctor (Transform a) where
  -- |
  --
  -- >>> dimap id (e3 True True False) C.id .# 4 :+ 5 :: V3 Int
  -- V3 5 5 4
  --
  dimap l r f = eta r . f . eta l

instance Strong (Transform a) where
  first' m = Transform $ \k (a,c) -> (m .# \b -> k (b,c)) a
  second' m = Transform $ \k (c,a) -> (m .# \b -> k (c,b)) a

instance Choice (Transform a) where
  left' m = Transform $ \k -> either (m .# k . Left) (k . Right)
  right' m = Transform $ \k -> either (k . Left) (m .# k . Right)

instance Sieve (Transform a) (Cont a) where
  sieve l b = cont $ \k -> (l .# k) b 

instance PR.Representable (Transform a) where
  type Rep (Transform a) = Cont a
  tabulate f = Transform $ \k b -> runCont (f b) k


{-
instance Arrow (Transform a) where
  arr f = Transform (. f)
  first m = Transform $ \k (a,c) -> (m .# \b -> k (b,c)) a
  second m = Transform $ \k (c,a) -> (m .# \b -> k (c,b)) a
  m *** n = Transform $ \k (a,c) -> (m .# \b -> (n .# \d -> k (b,d)) c) a
  m &&& n = Transform $ \k a -> (m .# \b -> (n .# \c -> k (b,c)) a) a

instance ArrowChoice (Transform a) where
  left m = Transform $ \k -> either (m .# k . Left) (k . Right)
  right m = Transform $ \k -> either (k . Left) (m .# k . Right)
  m +++ n =  Transform $ \k -> either (m .# k . Left) (n .# k . Right)
  m ||| n = Transform $ \k -> either (m .# k) (n .# k)

instance ArrowApply (Transform a) where
  app = Transform $ \k (f,a) -> (f .# k) a
-}

{-

-- ring homomorphism from a -> a^b
embed :: (Product-Semigroup) a => (Product-Monoid) c => (b -> a) -> Transform a b c
embed f = Transform $ \k b -> f b * k one
-- if the characteristic of s does not divide the order of a, then s[a] is semisimple
-- and if a has a length function, we can build a filtered algebra
-}

