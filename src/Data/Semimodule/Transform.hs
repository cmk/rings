{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
-- {-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE PatternSynonyms           #-}

{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Data.Semimodule.Transform where
{- (
    -- * Transforms
    Transform(..)
  , type Matrix
  , matrix
  , relation
  , images
  , invmap
    -- * Column vectors
  , type Vec, type Col
  , pattern Vec
  , runVec
  , augment
    -- * Row vectors
  , type Covec, type Row
  , pattern Covec
  , runCovec
  , coeffs
    -- ** Universal transforms
  , final
  , join, cojoin
  , diagonal, codiagonal
  , initial, coinitial
  , (!#), (#!)
  , (!*), (*!)
  , (!*!), (!%!)
  , convolve
    -- * Arrow combinators
  , fork, cofork
  , swap, coswap
  , ex1, ex2
  , inl, inr
  , arr2, apply
  , braid, cobraid
  , divideL, divideR
  , chooseL, chooseR
) where
-}

--import safe qualified Data.Functor.Contravariant.Rep as F
import safe Control.Arrow
import safe Control.Monad
import safe Control.Applicative
import safe Control.Category
import safe Data.Bool hiding (not)
import safe Data.Complex
import safe Data.Fixed
import safe Data.Functor.Alt
import safe Data.Functor.Apply
import safe Data.Functor.Compose
import safe Data.Functor.Contravariant
import safe Data.Functor.Identity
import safe Data.Functor.Product
import safe Data.Functor.Rep
import safe Data.Int
import safe Data.Monoid hiding (Alt(..), Sum(..), Product(..), Commutative(..))
import safe Data.Ring
import safe Data.Semiring
import safe Data.Semilattice
import safe Data.Semigroup.Quantale
import safe Data.Semimodule
import safe Data.Semimodule.Algebra
--import safe Data.Sequence hiding (reverse,index)
import safe Data.Tuple (swap)
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe Numeric.Natural
import safe Prelude (Ord, reverse)
import safe Prelude hiding (Num(..), Fractional(..), not, id, (.), (^), init, negate, sum, product)
import safe qualified Control.Category as C
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Sequence as Seq
import safe qualified Data.Set as Set
import safe qualified Data.Map as Map
import safe qualified Prelude as P
import safe qualified Data.Profunctor.Rep as PR
import Data.Finite (Finite, finites)
import GHC.TypeNats (KnownNat)
import Data.Functor.Contravariant (Contravariant(..))
import Data.Functor.Rep

import Data.Connection
import Data.Void
import Data.Foldable (foldl')
import Data.Group

import qualified Data.Universe.Class as U (Finite (..))
import Control.Monad.Trans.Select
import Control.Monad.Trans.Cont

{- TODO
Heyting instances for Search, Relation
MonadLogic?
fix glb, lub
clean up all your instances!
add back profunctors?

-}
type Quantifier a = Cont Bool a
type Search a = Select Bool a

{-
The only difference between this and the version with cont is that plain function application must be replaced with monadic bind; cont is just the callCC for ContT r Identity plus automatic lifting of the function into the Identity monad.

s for runtime behavior, for each element in the input list this first inserts the value True or #t, due to inner (k #t). The function is then applied to the resulting list, and the result (up to runCont or reset) becomes the input to the outer call to the continuation (k (k #t)). If (k #t) evaluates to #t then (k (k #t)) reduces to (k #t) and finally just #t, which means that input remains "stuck" at #t; otherwise the function continues with the value #f in the manner of a normal nondeterministic depth-first exhaustive search.

The function is always evaluated 2^n times; there is no short-circuit evaluation. Replacing (k (k #t)) with (or (k #t) (k #f)) gives the same result in fewer steps (unless the function only returns #t for all #f inputs) since it can immediately return #t as soon as the function produces #t for any input permutation and avoid calling the continuation again with the same input value.
-}
sat :: Int -> ([Bool] -> r) -> r
sat n = runCont $ replicateM n $ callCC $ \k -> k =<< k True

search = runSelect


-- Factory of exhaustively searchable sets:

smap :: (d -> e) -> Search d -> Search e
smap f s = select $ \q -> f( search s (q.f))

singleton :: a -> Search a
singleton = select . const

doubleton :: a -> a -> Search a
doubleton x y = select (\p -> if p x then x else y)

bigUnion :: Search(Search a) -> Search a
bigUnion xss = select (\p -> search( search xss (\xs -> runCont (exists xs) p)) p)

union :: Search a -> Search a -> Search a
xs `union` ys = bigUnion(doubleton xs ys)

unbounded :: (Monad m) => a -> m [a]
unbounded = sequence . repeat . pure

--bounded :: (Monad m) => Int -> a -> SelectT a m [a]
bounded :: Monad m => Int -> a -> m [a]
bounded n = sequence . P.replicate n . pure

query :: Monad m => Int -> ([Bool] -> m r) -> m [Bool]
query n = runSelectT (bounded n True) 

bit :: Search Int
bit = doubleton 0 1

cantor :: Search [Int]
cantor = sequence (repeat bit)


-- todo: read Conal's paper

ring :: (Eq a, Ring a) => a -> Search a
ring = select . z where
  z zero _ = P.error "ring"
  z one _ = zero
  z n p = if p (n-one) then n-one else z(n-one) p

list :: [a] -> Search a
list x = select (l x) where
  l [] _ = P.error "list"
  l [a] _ = a
  l (a:s) p = if p a then a else l s p



exists, forAll :: Search a -> Quantifier a
exists xs = cont $ \p -> p(search xs p)
forAll xs = cont $ \p -> not $ runCont (exists xs) (not . p)

data T x = B x (T x) (T x)
two :: Semiring a => a
two = one + one

code :: Ring a => (a -> x) -> T x
code f = B (f zero) (code(\n -> f(two*n+one))) 
                 (code(\n -> f(two*n+two)))

type Ring' a = (Ring a, Integral a)

decode :: Ring' a => T x -> (a -> x)
decode (B x l r) n |  n == zero    = x
                   |  odd n     = decode l ((n-one) `div` two)
                   |  otherwise = decode r ((n-two) `div` two)

id' :: Ring' b => (b -> a) -> (b -> a)
id' = decode.code


prod' :: (Ord a, Ring' a) => (a -> (p -> t) -> p) -> ((a -> p) -> t) -> a -> p
prod' e p = b
  where b = id'(\n->e n (\x->q n x(prod'(\i->e(i+n+one))(q n x))))
        q n x a = p(\i -> if i  < n then b i
                     else if i == n then x
                                    else a(i-n-one))


-- Universal and existential quantifiers:
type S d = (d -> Bool) -> d

type Q d = (d -> Bool) -> Bool
type N = Integer
type Bit = Int
type Cantor = N -> Bit


z :: N -> (N -> Bool) -> N
z 0 _ = undefined
z 1 _ = 0
z n p = if p (n-1) then n-1 else z(n-1) p

l :: [t] -> (t -> Bool) -> t
l [] _ = undefined
l [a] _ = a
l (a:s) p = if p a then a else l s p

bit'  :: S N
bit'  = \p -> if p 0 then 0 else 1

rcantor, tcantor, qcantor :: S (N -> N)
rcantor = prod' $ const bit'
tcantor = prod'(\i -> z 3)
qcantor = prod'(\i -> z 4)

factorial :: S (N -> N)
factorial = prod'(\i -> z(i+1))

-- fast:
-- [2,2,2,1,1]
w = [a(5^500),a(6^600),a(7^700),a(8^800),a(9^900)]
  where a = tcantor (\a->a(5^500)*a(6^600)*a(7^700)*a(8^800)*a(9^900) == 2^3)

-- slower:
-- [3,2,1,1,1]
w' = [a(5^500),a(6^600),a(7^700),a(8^800),a(9^900)]
  where a = qcantor (\a->a(5^500)*a(6^600)*a(7^700)*a(8^800)*a(9^900) == 2*3)

-- way too slow:
w'' = [a(5^500),a(6^600),a(7^700),a(8^800),a(9^900)]
  where a = factorial (\a->a(5^500)*a(6^600)*a(7^700)*a(8^800)*a(9^900) == 2*3*5*7)


-- But this is ok:

example = [a 2, a 3, a 4, a 5]
  where a = factorial (\a->a 2 * a 3 * a 4 * a 5== 2*2*3*4)

{-
prod :: (Ord a, Ring' a) => (a -> Search b) -> Search (a -> b)
prod f = let f' = search . f in select $ prod' f'

bit' :: Semiring a => Search a
bit' = select $ \p -> if p zero then zero else one

--rcantor, tcantor :: (Ord a, Ring' a) => Search (a -> a)
rcantor, tcantor :: Search (Integer -> Integer)
rcantor = prod $ const bit'
tcantor = prod $ \i -> ring (one + one + one)

factorial :: (Ord a, Ring' a) => Search (a -> a)
factorial = prod $ \i -> ring (i+one)

--cantorw :: S(N -> N -> Bool)
cantorw :: (Ord a, Ring' a) => Search (a -> a -> Bool)
cantorw = prod $ const bcantor


bcantor :: (Ord a, Ring' a) => Search (a -> Bool)
bcantor = prod $ const (pure True)

--forAllC :: ((a0 -> Bool) -> Bool) -> Bool
forAllC :: (Ord a, Ring' a) => Quantifier (a -> Bool)
forAllC = forAll bcantor

forAllZ :: (Eq a, Ring a) => a -> Quantifier a
forAllZ n = forAll (ring(n+one))

eq' :: (Ring t, Eq t, Eq a) => t -> (t -> a) -> (t -> a) -> Bool
eq' n a b = runCont (forAllZ n) (\i -> a i == b i)

least :: Semiring a => Search a
least = select f where
  f p = if p zero then zero else one + f (p.(one+))

-- Modulus of continuity on the Cantor space.
--modulus :: Eq y => ((N -> Bool) -> y) -> N
modulus :: (Ord a, Ring' a, Eq b) => ((a -> Bool) -> b) -> a
modulus f = search least(\n-> runCont forAllC (\a-> runCont forAllC (\b->eq' n a b <= (f a == f b))))

-- Function equality:

equal :: Eq b => Search a -> (a -> b) -> (a -> b) -> Bool
equal s f g = runCont (forAll s) (\x -> f x == g x)


-- Set equality.



--eqnat :: Ord a => a -> a -> Bool
--eqnat m n = equal bcantor (pure m) (pure n)

projset :: [a] -> Quantifier a
projset [] = cont $ const True
projset (n:l) = cont $ \p -> (p n) && (runCont (projset l) p)

eqset :: (Ord a, Ring' a) => [a] -> [a] -> Bool
eqset k l = equal bcantor (runCont $ projset k) (runCont $ projset l)

false2 :: Bool
false2 = runCont (exists rcantor) (\a->a(5^500)+a(6^600)+a(7^700)+a(8^800)+a(9^900)>= (4^400 :: Integer))

-- > [2,3,4,2]
example :: [Integer]
example = [a 2, a 3, a 4, a 5]
  where a = search factorial (\a->a 2 * a 3 * a 4 * a 5== 2*2*3*4)

-- fast:
-- [2,2,2,1,1]
example2 :: [Integer]
example2 = [a(5^5),a(6^6),a(7^7),a(8^8),a(9^9)]
  where a = search rcantor foo

foo :: (Integer -> Integer) -> Bool
foo a = a(5^5)*a(6^6)*a(7^7)*a(8^8)*a(9^9) == 2^3
-}



--simple r = r . converse r <~ id

type Relation a b = Transform Bool a b

-- some issue w/ this
relation :: Search b -> (a -> b -> Bool) -> Relation a b
relation s r = Transform $ flip r . search s

relation' :: U.Finite b => (a -> b -> Bool) -> Relation a b
relation' = relation $ list U.universeF

relation'' :: U.Finite b => (a -> b -> Bool) -> Relation a b
relation'' r = images $ \i -> (id &&& r i) <$> U.universeF

converse :: U.Finite a => Eq b => Relation a b -> Relation b a
converse = relation' . flip . related

-- > domain = range . converse
--
domain :: U.Finite a => Eq b => Relation a b -> Relation a a
domain r = id * converse r . r


-- | \( \forall a. a (range R) a \iff \exists b : a R b \)
--
-- > r = range r . r
-- > range (r . s) = range (r . range s)
--
range :: U.Finite a => Eq b => Relation a b -> Relation b b
range r = id * r . converse r
 
related :: Eq b => Relation a b -> a -> b -> Bool
related r a b = runVec (Vec (==b) . r) a

related' :: Relation Bool Bool -> Bool -> Bool
related' r a = runVec (Vec id . r) a

{-
:m -Data.Semiring
:m -Data.Semimodule

univ = list universeF

or = converse $ relation (union (singleton False) (singleton True)) (||)
related or True True
related or True False
related or False True
related or False False

or' = relation' (||)
related or' True True
related or' True False
related or' False True
related or' False False

or'' = relation'' (||)
related or'' True True
related or'' True False
related or'' False True
related or'' False False

F T
T T
λ> or !# True :+ True :: Complex Bool
True :+ True
λ> or !# True :+ False :: Complex Bool
False :+ True
λ> or !# False :+ True :: Complex Bool
True :+ True
λ> or !# False :+ False :: Complex Bool
False :+ False

λ> related (le >>> le) 4 6
True
λ> related (le >>> converse le) 4 5
True
λ> related (converse le >>> le) 5 4

λ> related (converse le * le) 5 4 -F
λ> related (converse le * le) 4 4 -T
λ> related (le * ge) 4 5
False
λ> related (le * ge) 4 4
True
λ> related (le * ge) 5 4
False
-}
le :: Relation Word8 Word8
le = relation'' (<=)

ge :: Relation Word8 Word8
ge = relation'' (>=)
{-
λ> related (lt >>> lt) 4 5
False
λ> related (lt >>> lt) 4 6 --sweet
True
-}
lt :: Relation Word8 Word8
lt = relation'' (<)
{-
λ> related (eq >>> eq) 4 4
True
λ> related (eq >>> eq) 4 5
False
-}
eq :: Relation Word8 Word8
eq = relation'' (==)


-- Kleene semiring & left-semimodule homomorphism
{-
see store comonad
copure aka 'at'

copure 0= 0
copure 1= 1
copure  (p+q) = copure p + copure q
copure (p∗q) = copure p * copure q
copure . star  = star . copure
-}
copure :: Monoid a => (a -> b) -> b
copure f = f mempty

cojoin' f u v = f (u <> v)

-- sectionn 6: decomposing f :: [a] -> b
--eff = copure . foldl' cojoin eff

scriptD :: ([a] -> b) -> a -> [a] -> b
scriptD f a as = f (a:as)

-- aka left-facing triangle
{-
zero = del zero zero
one = del one zero
(a `del` dp) + (b `del` dq) =a+b `del` dp+dq
(a `del` dp)∗q=a·q+ (0 `del` fmap(∗q)dp)
(a `del` dp)∗=qwhereq=a∗·(1 `del` fmap(∗q)dp)
s·(a `del` dp) =s∗a `del` fmap(s·)dp
w7→b=foldr(λc t→0 `del` c7→t) (b `del` 0) w
-}

del :: b -> (c -> [c] -> b) -> [c] -> b
del b _ [] = b
del _ h (c:cs) = h c cs

--del' :: b -> Cont ([a] -> b) a
del' b = cont $ del b

-------------------------------------------------------------------------------
-- Transform
-------------------------------------------------------------------------------

-- | An unreified transformation between free semimodules indexed with bases /b/ and /c/.
--
-- @
-- f '!#' x '+' y = (f '!#' x) + (f '!#' y)
-- f '!#' (r '.*' x) = r '.*' (f '!#' x)
-- @
--
-- Usable with a wide range of vector representations, for example via < http://hackage.haskell.org/package/vector-sized-1.4.0.0/docs/Data-Vec-Sized.html#v:generate >
--
-- /Caution/: You must ensure the above laws hold when using the default constructor.
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
-- > invmap Data.Connection.lower Data.Connection.upper :: Connection a1 a2 => Transform a1 b c -> Transform a2 b c
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Transform a1 b c -> Transform a2 b c
invmap f g (Transform t) = Transform $ \x -> t (x >>> g) >>> f

-------------------------------------------------------------------------------
-- Vectors & co-vectors
-------------------------------------------------------------------------------

-- | A vector in a vector space or free semimodule, represented as an index function.
--
-- Equivalent to 'Data.Functor.Contravariant.Op'.
--
-- Vecs transform contravariantly as a function of their bases:
--
-- > (>>>) :: Transform a b c -> Vec a c -> Vec a b
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
type Vec a b = Transform a b Void

type Col a m = Vec a (Finite m)

pattern Vec :: (b -> a) -> Vec a b
pattern Vec r <- (runVec -> r) where Vec f = Transform $ \_ -> f

runVec :: Vec a b -> b -> a
runVec (Transform t) = t absurd

-- | The < https://en.wikipedia.org/wiki/Augmentation_(algebra) augmentation > ring homomorphism.
--
augment :: Semiring a => Transform a b c -> Vec a b
augment l = Vec $ l !# const one

-------------------------------------------------------------------------------
-- Row (co-)vectors
-------------------------------------------------------------------------------

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
-- > (<<<) :: Transform a b c -> Covec a b -> Covec a c
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
type Covec a c = Transform a () c

type Row a n = Covec a (Finite n)

pattern Covec :: ((c -> a) -> a) -> Covec a c
pattern Covec r <- (runCovec -> r) where Covec f = Transform $ \k _ -> f k

runCovec :: Covec a c -> (c -> a) -> a
runCovec (Transform t) k = t k ()

-- | Obtain a runCovector from a linear combination of basis elements.
--
coeffs :: (Semiring a, Foldable f) => f (c, a) -> Covec a c
coeffs f = Covec $ \k -> foldl' (\acc (c, a) -> acc + a * k c) zero f 

-------------------------------------------------------------------------------
-- Universal transforms
-------------------------------------------------------------------------------

-- | TODO: Document
--
final :: Unital a b => Transform a b ()
final = Transform $ \k -> unital $ k ()

-- | Obtain a vector from the unit of a unital coalgebra.
--
initial :: Unital a b => a -> Vec a b
initial = Vec . unital

-- | Obtain a runCovector from the counit of a counital coalgebra.
--
coinitial :: Counital a c => Covec a c
coinitial = Covec counital

-- | Obtain a vector from a vector on the tensor product space.
--
join :: Algebra a b => Vec a (b, b) -> Vec a b
join = (diagonal >>>)

-- | Obtain a runCovector from a runCovector on the tensor product space.
--
cojoin :: Coalgebra a c => Covec a (c, c) -> Covec a c
cojoin = (codiagonal <<<)

-- | Diagonal tranform into the tensor product space.
--
-- @
-- 'arr' (\((c1,()),(c2,())) -> (c1,c2)) '<<<' ('C.id' '***' 'initial') 'C..' 'diagonal' = 'C.id'
-- 'arr' (\(((),c1),((),c2)) -> (c1,c2)) '<<<' ('initial' '***' 'C.id') 'C..' 'diagonal' = 'C.id'
-- @
--
diagonal :: Algebra a b => Transform a b (b, b)
diagonal = Transform $ joined . curry

-- | Co-diagonal transform out of the tensor product space.
--
-- @
-- 'arr' (\(c1,c2) -> ((c1,()),(c2,()))) '>>>' ('C.id' '***' 'coinitial') 'C..' 'codiagonal' = 'C.id'
-- 'arr' (\(c1,c2) -> (((),c1),((),c2))) '>>>' ('coinitial' '***' 'C.id') 'C..' 'codiagonal' = 'C.id'
-- @
--
codiagonal :: Coalgebra a c => Transform a (c, c) c
codiagonal = Transform $ uncurry . cojoined

infixl 7 !*!

-- | Multiplication operator on an algebra over a free semimodule.
--
-- /Caution/ in general 'mult' needn't be commutative, nor coassociative.
--
(!*!) :: Algebra a b => Vec a b -> Vec a b -> Vec a b
(!*!) (runVec -> f) (runVec -> g) = Vec . joined $ \i j -> f i * g j

infixr 7 !%!

-- | Multiplication operator on a coalgebra over a free semimodule.
--
-- /Caution/ in general 'comult' needn't be commutative, nor coassociative.
--
(!%!) :: Coalgebra a c => Covec a c -> Covec a c -> Covec a c
(!%!) (runCovec -> f) (runCovec -> g) = Covec $ \k -> f (\l -> g (cojoined k l))

{-
λ> foo = convolve (lift $ m22 1 0 0 1) (lift $ m22 1 0 0 1)
λ> foo !# V2 1 2 :: V2 Int
V2 1 2
λ> foo = convolve (lift $ m22 1 0 0 1) (lift $ m22 1 1 1 1)
λ> foo !# V2 1 2 :: V2 Int
V2 1 2
λ> foo = convolve (lift $ m22 1 1 1 1) (lift $ m22 1 1 1 1)
λ> foo !# V2 1 2 :: V2 Int
V2 3 3
-}

-- | Convolution with an associative algebra and coassociative coalgebra
--
convolve :: (Algebra a b, Coalgebra a c) => Transform a b c -> Transform a b c -> Transform a b c
convolve f g = codiagonal <<< (f *** g) <<< diagonal

infixr 2 !#

-- | Apply a transformation to a reified vector.
--
(!#) :: (Free f, Free g) => Transform a (Rep f) (Rep g) -> g a -> f a
(!#) (Transform t) = tabulate . t . index

infixl 2 #!

-- | Apply a transformation to a reified vector, from the right.
--
(#!) :: (Free f, Free g) => g a -> Transform a (Rep f) (Rep g) -> f a
(#!) = flip (!#)

infix 2 !*

-- | Apply a runCovector to a vector from the left.
--
(!*) :: Free f => Covec a (Rep f) -> f a -> a 
(!*) (runCovec -> r) = r . index 

infix 2 *!

-- | Apply a runCovector to a vector from the right.
--
(*!) :: Free f => f a -> Covec a (Rep f) -> a
(*!) = flip (!*)

-------------------------------------------------------------------------------
-- Arrows
-------------------------------------------------------------------------------

fork :: b -> (b, b)
fork x = (x, x)

cofork :: Either c c -> c
cofork = either id id

coswap :: Either a b -> Either b a
coswap = either Right Left

ex1 :: Arrow p => p (a , b) b
ex1 = arr snd
{-# INLINE ex1 #-}

ex2 :: Arrow p => p (a , b) a
ex2 = arr fst
{-# INLINE ex2 #-}

inl :: Arrow p => p a (Either a b)
inl = arr Left
{-# INLINE inl #-}

inr :: Arrow p => p b (Either a b)
inr = arr Right
{-# INLINE inr #-}

arr2 :: Arrow p => (b1 -> b2 -> b) -> p a b1 -> p a b2 -> p a b
arr2 = divideR . uncurry

apply :: Arrow p => p a (b -> c) -> p a b -> p a c
apply = arr2 id
{-# INLINE apply #-}

-- | Swap components of a tensor product.
--
braid :: Arrow p => p (a , b) (b , a)
braid = arr swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
cobraid :: Arrow p => p (Either a b) (Either b a)
cobraid = arr coswap
{-# INLINE cobraid #-}

-- > unapply . apply = id
-- > apply . unapply = id
--
--unapply :: (Category p, Profunctor p, Closed p) => p a c -> p b c -> p a (b -> c)
--unapply = (curry' .) . divideL id
--{-# INLINE unapply #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:divide divide >.
--
divideL :: Arrow p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
divideL f x y = dimap f fst $ x *** y
{-# INLINE divideL #-}

-- > divideR f x y = tabulate $ \s -> liftA2 (curry f) (sieve x s) (sieve y s)
divideR :: Arrow p => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
divideR f p q = dimap fork f $ p *** q
{-# INLINE divideR #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:choose choose >.
--
chooseL :: ArrowChoice p => (a -> Either a1 a2) -> p a1 b -> p a2 b -> p a b 
chooseL f p q = dimap f cofork $ p +++ q
{-# INLINE chooseL #-}

chooseR :: ArrowChoice p => (Either b1 b2 -> b) -> p a b1 -> p a b2 -> p a b
chooseR f x y = dimap Left f $ x +++ y
{-# INLINE chooseR #-}

dimap :: Arrow a => (b2 -> b1) -> (c1 -> c2) -> a b1 c1 -> a b2 c2
dimap l r f = arr r <<< f <<< arr l

-------------------------------------------------------------------------------
-- Transform instances
-------------------------------------------------------------------------------

instance Functor (Transform a b) where
  fmap f m = Transform $ \k -> m !# k . f

instance Category (Transform a) where
  id = Transform id
  Transform f . Transform g = Transform $ g . f

instance Apply (Transform a b) where
  mf <.> ma = Transform $ \k b -> (mf !# \f -> (ma !# k . f) b) b

instance Applicative (Transform a b) where
  pure a = Transform $ \k _ -> k a
  (<*>) = (<.>)

instance Monad (Transform a b) where
  return a = Transform $ \k _ -> k a
  m >>= f = Transform $ \k b -> (m !# \a -> (f a !# k) b) b

instance Arrow (Transform a) where
  arr f = Transform (. f)
  first m = Transform $ \k (a,c) -> (m !# \b -> k (b,c)) a
  second m = Transform $ \k (c,a) -> (m !# \b -> k (c,b)) a
  m *** n = Transform $ \k (a,c) -> (m !# \b -> (n !# \d -> k (b,d)) c) a
  m &&& n = Transform $ \k a -> (m !# \b -> (n !# \c -> k (b,c)) a) a

instance ArrowChoice (Transform a) where
  left m = Transform $ \k -> either (m !# k . Left) (k . Right)
  right m = Transform $ \k -> either (k . Left) (m !# k . Right)
  m +++ n =  Transform $ \k -> either (m !# k . Left) (n !# k . Right)
  m ||| n = Transform $ \k -> either (m !# k) (n !# k)

instance ArrowApply (Transform a) where
  app = Transform $ \k (f,a) -> (f !# k) a

instance Semigroup (Join a) => Semigroup (Join (Transform a b c)) where
  (<>) = liftA2 $ \(Transform f) (Transform g) -> Transform $ f \/ g

instance Monoid (Join a) => Monoid (Join (Transform a b c)) where
  mempty = pure . Transform $ \_ -> const bottom

instance Semigroup (Meet a) => Semigroup (Meet (Transform a b c)) where
  (<>) = liftA2 $ \(Transform f) (Transform g) -> Transform $ f /\ g

instance Monoid (Meet a) => Monoid (Meet (Transform a b c)) where
  mempty = pure . Transform $ \_ -> const top

{-
instance Quantale (Meet a) => Quantale (Meet (Transform a b c)) where
  (//) = liftA2 $ \(Transform f) (Transform g) -> Transform $ liftA2 (\x y -> getMeet $ Meet x // Meet y) f g
  (\\) = flip (//)
-}
instance Lattice a => Lattice (Transform a b c)
instance BoundedLattice a => BoundedLattice (Transform a b c)
---instance Heyting a => Heyting (Transform a b c)

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
{-
instance Semigroup (Multiplicative a) => Semigroup (Multiplicative (Transform a b b)) where
  (<>) = liftA2 (>>>)

instance Monoid (Multiplicative a) => Monoid (Multiplicative (Transform a b b)) where
  mempty = pure C.id
instance Presemiring a => Presemiring (Transform a b b)
instance Semiring a => Semiring (Transform a b b)
instance Ring a => Ring (Transform a b b)

-}

instance Semiring a => LeftSemimodule (Transform a b b) (Transform a b c) where
  -- | Left matrix multiplication
  lscale = (>>>)
instance Semiring a => LeftSemimodule a (Transform a b c) where
  lscale l (Transform m) = Transform $ \k b -> l * m k b
instance Semiring a => RightSemimodule (Transform a c c) (Transform a b c) where
  -- | Right matrix multiplication
  rscale = (<<<)
instance Semiring a => Bisemimodule (Transform a b b) (Transform a c c) (Transform a b c)
instance Semiring a => RightSemimodule a (Transform a b m) where
  rscale r (Transform m) = Transform $ \k b -> m k b * r
instance Semiring a => Bisemimodule a a (Transform a b c)

{-
-- | Lift a semiring element into a 'Cayley'.
--
-- @ 'runCayley' . 'cayley' = 'id' @
--
-- >>> runCayley . cayley $ 3.4 :: Double
-- 3.4
-- >>> runCayley . cayley $ m22 1 2 3 4 :: M22 Int
-- Compose (V2 (V2 1 2) (V2 3 4))
-- 
cayley :: Semiring a => a -> Transform a a a
cayley a = Transform $ \k b -> a * k zero + b
-- | Extract a semiring element from a 'Cayley'.
--
-- >>> runCayley $ (one + one) * (one + (cayley 3.4)) :: Double
-- 8.8
-- >>> runCayley $ (one + one) * (one + (cayley $ m22 1 2 3 4)) :: M22 Int
-- Compose (V2 (V2 4 4) (V2 6 10))
--
runCayley :: Semiring a => Transform a a a -> a
runCayley (Transform f) = f (one +) zero

-- ring homomorphism from a -> a^b
embed :: (Product-Semigroup) a => (Product-Monoid) c => (b -> a) -> Transform a b c
embed f = Transform $ \k b -> f b * k one
-- if the characteristic of s does not divide the order of a, then s[a] is semisimple
-- and if a has a length function, we can build a filtered algebra

instance Profunctor (Transform a) where
  -- |
  --
  -- >>> dimap id (e3 True True False) C.id !# 4 :+ 5 :: V3 Int
  -- V3 5 5 4
  --
  dimap l r f = eta r <<< f <<< eta l

instance Strong (Transform a) where
  first' m = Transform $ \k (a,c) -> (m !# \b -> k (b,c)) a
  second' m = Transform $ \k (c,a) -> (m !# \b -> k (c,b)) a

instance Choice (Transform a) where
  left' m = Transform $ \k -> either (m !# k . Left) (k . Right)
  right' m = Transform $ \k -> either (k . Left) (m !# k . Right)

instance Sieve (Transform a) (Covec a) where
  sieve l b = Covec $ \k -> (l !# k) b 

instance PR.Representable (Transform a) where
  type Rep (Transform a) = Covec a
  tabulate f = Transform $ \k b -> runCovec (f b) k
-}

