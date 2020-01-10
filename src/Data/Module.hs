{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE Safe                  #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE CPP #-}

module Data.Module where

import safe Data.Bool
import safe Data.Complex
import safe Data.Dioid
import safe Data.Distributive
import safe Data.Field
import safe Data.Fixed
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Functor.Compose
import safe Data.Functor.Rep
import safe Data.Group
import safe Data.Int
import safe Data.Prd
import safe Data.Ring
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Tuple
import safe Data.Word
import safe GHC.Real hiding (Fractional(..))
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe Prelude hiding (Num(..), Fractional(..), product)
import safe qualified Prelude as N

(a :+ b) /// (c :+ d) = ((a><c <> b><d) // (c><c <> d><d)) :+ ((b><c << a><d) // (c><c <> d><d))

--instance (Unital (f a), Algebra (f a), Functor f) => Semifield (f a) where
  --recip q = conj' q // norm' q
--  recip q = ((recip . norm' $ q) ><) <$> conj' q 

{-
laws:

conj is an involution
 
-}
{-
  -- fmap ((recip . norm $ x) ><) $ conj x == recip x
infixl 6 <..>
-- Composition algebra
-- Not necessarily associative algebra over /a/ together with a nondegenerate
-- quadratic product '<.>'.
class Semimodule r a => Algebra r a | a -> r where

  conj' :: a -> a

  norm' :: a -> r
  default norm' :: Field r => a -> r
  norm' a = a <..> conj' a

-- bilinear form
  (<..>) :: a -> a -> r
  default (<..>) :: Algebra r a => Field r => a -> a -> r
  x <..> y = (0.5 ><) $ norm' (x <> y) << norm' x << norm' y

-- Complex and Bicomplex numbers
instance Field a => Algebra a (Complex a) where
  conj' (a :+ b) = a :+ negate b
  norm' (a :+ b) = a >< a <> b >< b

-- Quaternions and Biquaternions
instance Field a => Algebra a (Quaternion a) where
  conj' = conj
  norm' = norm

-}

{-
-- | `Additive.(+)` default definition
addRep :: (Applicative m, Additive r) => m r -> m r -> m r
addRep = liftA2 (+)

-- | `Additive.sinnum1p` default definition
sinnum1pRep :: (Functor m, Additive r) => Natural -> m r -> m r
sinnum1pRep = fmap . sinnum1p

-- | `Monoidal.zero` default definition
zeroRep :: (Applicative m, Monoidal r) => m r 
zeroRep = pure zero

-- | `Monoidal.sinnum` default definition
sinnumRep :: (Functor m, Monoidal r) => Natural -> m r -> m r
sinnumRep = fmap . sinnum

-- | `Group.negate` default definition
negateRep :: (Functor m, Group r) => m r -> m r
negateRep = fmap negate

-- | `Group.(-)` default definition
minusRep :: (Applicative m, Group r) => m r -> m r -> m r
minusRep = liftA2 (-)

-- | `Group.subtract` default definition
subtractRep :: (Applicative m, Group r) => m r -> m r -> m r
subtractRep = liftA2 subtract

-- | `Group.times` default definition
timesRep :: (Integral n, Functor m, Group r) => n -> m r -> m r
timesRep = fmap . times



(<#>) :: (Semiring a, Free f, Free g, Free h) => f (g a) -> g (h a) -> f (h a)
(<#>) x y = getCompose $ tabulate (\(i,j) -> row i x <.> col j y)
-}

-- Data.Algebra

--class Semimodule r a => Algebra r a where
class Semiring r => Algebra r a where
  product :: (a -> a -> r) -> a -> r

-- | An algebra over a semiring, built using a free module.
--
-- Needn't be associative or unital.


-- | An semigroup with involution
-- 
-- > adjoint a * adjoint b = adjoint (b * a)
--class Semigroup r => Involutive r where adjoint :: r -> r

class Algebra r a => Involutive r a where
  involute :: (a -> r) -> a -> r

conj' :: (Involutive a (Rep f), Representable f) => f a -> f a
conj' = tabulate . involute . index

instance Ring r => Involutive r ComplexBasis where
  involute f = f' where
    afe = f False
    nfi = negate (f True)
    f' False = afe
    f' True = nfi

class Algebra r a => Composition r a where
  conjugate :: (a -> r) -> a -> r

  (<..>) :: a -> a -> r
  --default (<..>) :: Algebra r a => Field r => a -> a -> r
  --x <..> y = (0.5 ><) $ norm' (x <> y) << norm' x << norm' y
{-
  conj' :: a -> a

  norm' :: a -> r
  default norm' :: Field r => a -> r
  norm' a = a <..> conj' a

-- bilinear form

-}

foo :: (Representable f, Algebra a (Rep f)) => (Rep f -> Rep f -> a) -> f a
foo f = tabulate (product f)

-- bar (m22 1 2 3 4) (m22 1 2 3 4)
bar
  :: (Algebra a (Rep f), Foldable1 g, Eq (Rep g),
      Representable f, Representable g
     ) =>
     f (g a) -> f (g a) -> f a
bar m n = tabulate $ product (\b1 b2 -> index m b1 <.> index n b2)


infixl 7 <@>

-- | Cross product.
--
-- >>> V3 1 1 1 <@> V3 (-2) 1 1
-- V3 0 (-3) 3
--
-- The cross product satisfies the following properties:
--
-- @ 
-- a '<@>' a = mempty 
-- a '<@>' b = negate ( b '<@>' a ) , 
-- a '<@>' ( b <> c ) = ( a '<@>' b ) <> ( a '<@>' c ) , 
-- ( r a ) '<@>' b = a '<@>' ( r b ) = r ( a '<@>' b ) . 
-- a '<@>' ( b '<@>' c ) <> b '<@>' ( c '<@>' a ) <> c '<@>' ( a '<@>' b ) = mempty . 
-- @
-- < https://en.wikipedia.org/wiki/Jacobi_identity Jacobi identity >.
--(<@>) :: Ring a => V3 a -> V3 a -> V3 a
--(<@>) (V3 a b c) (V3 d e f) = V3 (b><f << c><e) (c><d << a><f) (a><e << b><d)

-- | Algebra product.
--
-- >>> prodRep (1 :+ 2) (3 :+ 4) :: Complex Int
-- (-5) :+ 10
-- >>> (1 :+ 2) >< (3 :+ 4) :: Complex Int
-- (-5) :+ 10
-- >>> prodRep qi qj :: QuatM
-- Quaternion 0.000000 (V3 0.000000 0.000000 1.000000)
-- >>> qi >< qj :: QuatM
-- Quaternion 0.000000 (V3 0.000000 0.000000 1.000000)
-- >>> prodRep (V3 1 0 0) (V3 0 1 0)
(<@>) :: (Representable f, Algebra r (Rep f)) => f r -> f r -> f r
(<@>) m n = tabulate $ product (\b1 b2 -> index m b1 >< index n b2)
{-# INLINABLE (<@>) #-}


class Algebra r a => UnitalAlgebra r a where
  unital :: r -> a -> r

instance Ring r => UnitalAlgebra r ComplexBasis where
  unital x False = x
  unital _ _ = mempty

instance Ring r => UnitalAlgebra r QuaternionBasis where
  unital x Nothing = x 
  unital _ _ = mempty


{-
instance (Unital r, UnitalAlgebra r a) => Unital (a -> r) where
  one = unit one

instance Semiring r => UnitalAlgebra r () where
  unit r () = r
-}


-- | `Unital.sunit` default definition.
--
-- >>> aunit :: Complex Int
-- 1 :+ 0
--
aunit :: (Representable f, UnitalAlgebra a (Rep f), Monoid a) => f a
aunit = tabulate $ unital sunit

-- | `Rig.fromNatural` default definition
--fromNaturalRep :: (UnitalAlgebra r (Rep m), Representable m, Rig r) => Natural -> m r
fromNaturalRep :: (Representable f, UnitalAlgebra a (Rep f), Dioid a) => Natural -> f a
fromNaturalRep n = tabulate $ unital (fromNatural n)

-- | `Ring.fromInteger` default definition
--fromIntegerRep :: (UnitalAlgebra r (Rep m), Representable m, Ring r) => Integer -> m r
fromIntegerRep :: (Representable f, UnitalAlgebra a (Rep f), Ring a) => Integer -> f a
fromIntegerRep n = tabulate $ unital (fromInteger n)

-------------------------------------------------------------------------------
-- Dimension 2
-------------------------------------------------------------------------------

type ComplexBasis = Bool

type HyperbolicBasis = I2

-- Complex basis
--instance Module r ComplexBasis => Algebra r ComplexBasis where
instance Ring r => Algebra r ComplexBasis where
  product f = f' where
    fe = f False False << f True True
    fi = f False True <> f True False
    f' False = fe
    f' True = fi

data I2 = I21 | I22 deriving (Eq, Ord, Show)

instance Prd I2 where
  (<~) = (<=)
  (>~) = (>=)
  pcompare = pcompareOrd

instance Minimal I2 where
  minimal = I21

instance Maximal I2 where
  maximal = I22



-- http://hackage.haskell.org/package/algebra-4.3.1/docs/src/Numeric-Coalgebra-Hyperbolic.html#line-25
{-


-- | the trivial diagonal algebra
instance Semiring k => Algebra k HyperBasis where
  product f = f' where
    fs = f Sinh Sinh
    fc = f Cosh Cosh
    f' Sinh = fs
    f' Cosh = fc

instance Semiring k => UnitalAlgebra k HyperBasis where
  unital = const

-- | the hyperbolic trigonometric coalgebra
instance (Commutative k, Semiring k) => Coalgebra k HyperBasis where
  coproduct f = f' where
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
-- @ (x+jy) * (u+jv) = (xu+yv) + j(xv+yu) @
-- >>> (V2 1 2) <@> (V2 1 2)
-- V2 5 4
-- https://en.wikipedia.org/wiki/Split-complex_number
instance Semiring r => Algebra r HyperbolicBasis where
  product f = f' where
    i21 = f I21 I21 <> f I22 I22
    i22 = f I21 I22 <> f I22 I21
    f' I21 = i21
    f' I22 = i22

-------------------------------------------------------------------------------
-- Dimension 3
-------------------------------------------------------------------------------


data I3 = I31 | I32 | I33 deriving (Eq, Ord, Show)

instance Prd I3 where
  (<~) = (<=)
  (>~) = (>=)
  pcompare = pcompareOrd

instance Minimal I3 where
  minimal = I31

instance Maximal I3 where
  maximal = I33

{-
(<@>) :: Ring a => V3 a -> V3 a -> V3 a
(<@>) (V3 a b c) (V3 d e f) = V3 (b><f << c><e) (c><d << a><f) (a><e << b><d)
{-# INLINABLE (<@>) #-}
-}
instance Ring r => Algebra r I3 where
  product f = f' where
    i31 = f I32 I33 << f I33 I32 --f False False << f True True
    i32 = f I33 I31 << f I31 I33 --f False True <> f True False
    i33 = f I31 I32 << f I32 I31 
    f' I31 = i31
    f' I32 = i32
    f' I33 = i33

-------------------------------------------------------------------------------
-- Dimension 4
-------------------------------------------------------------------------------

type QuaternionBasis = Maybe I3

--instance Module r QuaternionBasis => Algebra r QuaternionBasis where
instance Ring r => Algebra r QuaternionBasis where
  product f = maybe fe f' where
    e = Nothing
    i = Just I31
    j = Just I32
    k = Just I33
    fe = f e e << (f i i <> f j j <> f k k)
    fi = f e i <> f i e <> (f j k << f k j)
    fj = f e j <> f j e <> (f k i << f i k)
    fk = f e k <> f k e <> (f i j << f j i)
    f' I31 = fi
    f' I32 = fj
    f' I33 = fk

data I4 = I41 | I42 | I43 | I44 deriving (Eq, Ord, Show)

instance Prd I4 where
  (<~) = (<=)
  (>~) = (>=)
  pcompare = pcompareOrd

instance Minimal I4 where
  minimal = I41

instance Maximal I4 where
  maximal = I44




infixl 6 <.>

-- | Dot product.
--
(<.>) :: Free f => Semiring a => f a -> f a -> a
(<.>) a b = fold1 $ liftR2 (><) a b 
{-# INLINE (<.>) #-}

-- | Squared /l2/ norm of a vector.
--
quadrance :: Free f => Semiring a => f a -> a
quadrance f = f <.> f
{-# INLINE quadrance #-}

-- | Squared /l2/ norm of the difference between two vectors.
--
qd :: Free f => Module a (f a) => f a -> f a -> a
qd f g = quadrance $ f << g
{-# INLINE qd #-}

--lerp :: Ring a => Semigroup (f a) => Representable f => a -> f a -> f a -> f a
--lerp a f g = fmap (a ><) f <> fmap ((sunit << a) ><) g


-- | Dirac delta function.
--
dirac :: Eq i => Unital a => i -> i -> a
dirac i j = bool mempty sunit (i == j)
{-# INLINE dirac #-}
{-
dirac' :: (Representable f, UnitalAlgebra a1 (Rep f), Monoid a1, Monoid (f a1), Eq a2) => a2 -> a2 -> f a1
dirac' i j = bool mempty aunit (i == j)

unit'
  :: (Representable f1, Representable f2, UnitalAlgebra a1 (Rep f2),
      Monoid a1, Monoid (f2 a1), Eq (Rep f1)) =>
     Rep f1 -> f1 (f2 a1)
unit' i = tabulate $ dirac' i
-}
-- | Create a unit vector at an index.
--
-- >>> idx I21 :: V2 Int
-- V2 1 0
--
-- >>> idx I42 :: V4 Int
-- V4 0 1 0 0
--
idx :: Unital a => Free f => Rep f -> f a
idx i = tabulate $ dirac i
{-# INLINE idx #-}




{-


class Semimodule r a => Algebra r a where
  (<..>) :: a -> a -> r
-- | An associative algebra built with a free semimodule.
--
-- Use for Lie algebras, composition algebras, division algebras etc
--
class Semimodule r a => Algebra r a where
  product :: (a -> a -> r) -> a -> r

instance Rng k => Algebra k ComplexBasis where
  product f = f' where
    fe = f E E - f I I
    fi = f E I + f I E
    f' E = fe
    f' I = fi

-- λ> conj' [1,2,3]
-- [1,2,3,2,3,3]
--
-- conj
conj' :: Algebra a a => a -> a
conj' = product (flip const)


instance Semigroup a => Algebra () a where
  product _ _ = ()

instance Ring a => Semimodule (Complex a) a where
 (.#) = error "TODO"

instance Ring r => Algebra (Complex r) (Complex r) where
  product k x@(a :+ b) = k x $ a :+ negate b
  
instance Ring r => Algebra r (Complex r) where
  product k x@(a :+ b) = k x $ a :+ negate b

-- | The tensor algebra
--
-- >>> product (<>) [1..3 :: Int]
-- [1,2,3,1,2,3,1,2,3,1,2,3]
--
-- >>> product (\f g -> fold (f ++ g)) [1..3] :: Int
-- 24
--
instance Semiring r => Algebra r [a] where
  product f = go [] where
    go ls rrs@(r:rs) = f (reverse ls) rrs <> go (r:ls) rs
    go ls [] = f (reverse ls) []

prodDef :: Algebra r t => (t -> r) -> (t -> r) -> t -> r
prodDef f g = product $ \a b -> f a >< g b

-}


{-

-- https://en.wikipedia.org/wiki/Dual_number
Semiring k => Algebra k DualBasis
Semiring k => Algebra k ComplexBasis

(<.>) :: Free f => Semiring a => f a -> f a -> a
(<.>) a b = fold1 $ liftR2 (><) a b 
{-# INLINE (<.>) #-}

instance Semiring a => Algebra a (V3 a) where
  product k v = fold1 $ liftR2 k v v 

-- A coassociative coalgebra over a semiring using
class Semiring r => Coalgebra r c where
  coproduct :: (c -> r) -> c -> c -> r

-- | An associative algebra built with a free module over a semiring
class Semiring r => Algebra r a where
  mult :: (a -> a -> r) -> a -> r

instance Algebra () a where
  mult _ _ = ()

-- | The tensor algebra
instance Semiring r => Algebra r [a] where
  mult f = go [] where
    go ls rrs@(r:rs) = f (reverse ls) rrs + go (r:ls) rs
    go ls [] = f (reverse ls) []

-- | The tensor algebra
instance Semiring r => Algebra r (Seq a) where
  mult f = go Seq.empty where
    go ls s = case viewl s of
       EmptyL -> f ls s 
       r :< rs -> f ls s + go (ls |> r) rs

instance Semiring r => Algebra r () where
  mult f = f ()

-}

{-
instance (Semiring a, Free f) => Algebra (f a) where
  type K (f a) = a
  (<..>) a b = fold1 $ liftR2 (><) a b 

  conj' (a :+ b) = a :+ negate b
  norm' (a :+ b) = a >< a <> b >< b

--
(<.>) :: Semiring a => Free f => f a -> f a -> a
(<.>) a b = fold1 $ liftR2 (><) a b 
{-# INLINE (<.>) #-}


    Right distributivity: (x <> y) <@> z = x <@> z <> y <@> z
    Left distributivity: z <@> (x <> y) = z <@> x <> z <@> y
    Compatibility with scalars: (a *^ x) <@> (b *^ y) = (a >< b) *^ (x <@> y).

-- Lie algebra

class Lie f where
  (<@>) :: Ring a => f a -> f a -> f a

-------------------------------------------------------------------------------
-- Algebras
-------------------------------------------------------------------------------

outer' :: Semiring a => Functor f => Functor g => f a -> g a -> f (g a)
outer' a b = fmap (\x->fmap (><x) b) a

-}




type Module r a = (Ring r, Group a, Semimodule r a)

-- Module over a field
-- classical vector spaces
type VSpace r a = (Field r, Module r a)

-- Semimodule over a semifield
-- dioids
type DSpace r a = (Semifield r, Semimodule r a)

type Free f = (Foldable1 f, Representable f, Eq (Rep f))
-- | Free semimodule over a generating set.
--
type FreeSemimodule a f = (Free f, Semimodule a (f a))

type FreeModule a f = (Free f, Module a (f a))

type CommutativeGroup a = Module Integer a


infixl 7 .#, #.

{-
 r .# (x <> y) = r .# x <> r .# y @
 (r <> s) .# x = r .# x <> s .# x @
 (r >< s) .# x = r .# (s .# x) @
 sunit .# x = x @
-}

-- | < https://en.wikipedia.org/wiki/Semimodule Semimodule > over a commutative semiring.
--
-- All instances must satisfy the following identities:
-- 
-- @ r '.#' (x '<>' y) ≡ r '.#' x '<>' r '.#' y @
--
-- @ (r '<>' s) '.#' x ≡ r '.#' x '<>' s '.#' x @
--
-- @ (r '><' s) '.#' x ≡ r '.#' (s '.#' x) @
--
-- When the ring of coefficients /r/ is unital we must additionally have:
--
-- @ 'sunit' '.#' x ≡ x @
--
-- See the properties module for a detailed specification of the laws.
--
class (Semiring r, Semigroup a) => Semimodule r a where

  -- | Left-multiply by a scalar.
  --
  (.#) :: r -> a -> a
  (.#) = flip (#.)
  
  -- | Right-multiply by a scalar.
  --
  (#.) :: a -> r -> a
  (#.) = flip (.#)

-- | Default definition of 'negate' for a commutative group.
--
negateDef :: CommutativeGroup a => a -> a
negateDef a = (-1 :: Integer) .# a


-- | Linearly interpolate between two vectors.
--
lerp :: Module r a => r -> a -> a -> a
lerp r f g = r .# f <> (sunit << r) .# g
{-# INLINE lerp #-}

-- | Outer (tensor) product.
--
outer :: Functor f => Semimodule r a => f r -> a -> f a
outer f a = fmap (\x-> x .# a) f
{-# INLINE outer #-}



-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------


{-
instance Semiring a => Semimodule a a where
  (.#) = (><)

-- use DerivingVia instead?
instance {-# Overlappable #-} (Semiring r, r ~ a) => Semimodule r a where
  (.#) = (><)

instance (Semimodule r a, Semigroup (f a), Functor f) => Semimodule r (f a) where
  a .# f = (a .#) <$> f

instance (Semiring a, Semigroup (f a), Functor f) => Semimodule a (f a) where
  a .# f = (a ><) <$> f


u = V3 (1 :% 1) (2 :% 1) (3 :% 1) :: V3 Rational
v = V3 (2 :% 1) (4 :% 1) (6 :% 1) :: V3 Rational
r = 1 :% 2 :: Rational
lerp r u v
-- V3 (6 % 4) (12 % 4) (18 % 4)

u = V3 (1 :% 1) (2 :% 1) (3 :% 1) :: V3 Positive
v = V3 (2 :% 1) (4 :% 1) (6 :% 1) :: V3 Positive
r = 1 :% 2 :: Positive
lerp r u v

-}
{-
instance Semiring a => Semimodule a a where
  (.#) = (><)



instance Semiring r => Semimodule r () where 
  _ .# _ = ()

-}
instance Semigroup a => Semimodule () a where 
  _ .# a = a

instance Monoid a => Semimodule Natural a where
  (.#) = nreplicate

instance Group a => Semimodule Integer a where
  (.#) = iter where
    iter n a
      | n == 0 = mempty
      | n > 0 = sinnum (N.fromInteger n) a
      | otherwise = sinnum (N.fromInteger $ abs n) (negate a)


instance (Semiring a, Semimodule r a) => Semimodule r (Ratio a) where 
  a .# (x :% y) = (a .# x) :% y

instance Semimodule r a => Semimodule r (e -> a) where 
  a .# f = (a .#) <$> f

instance Semimodule r a => Semimodule r (Complex a) where 
  a .# f = (a .#) <$> f

instance (Semimodule r a, Semimodule r b) => Semimodule r (a, b) where
  n .# (a, b) = (n .# a, n .# b)

instance (Semimodule r a, Semimodule r b, Semimodule r c) => Semimodule r (a, b, c) where
  n .# (a, b, c) = (n .# a, n .# b, n .# c)

#define deriveSemimodule(ty)                      \
instance Semiring ty => Semimodule ty ty where {  \
   (.#) = (><)                                    \
;  {-# INLINE (.#) #-}                            \
}

deriveSemimodule(Bool)
deriveSemimodule(Int)
deriveSemimodule(Int8)
deriveSemimodule(Int16)
deriveSemimodule(Int32)
deriveSemimodule(Int64)
deriveSemimodule(Word)
deriveSemimodule(Word8)
deriveSemimodule(Word16)
deriveSemimodule(Word32)
deriveSemimodule(Word64)
deriveSemimodule(Uni)
deriveSemimodule(Deci)
deriveSemimodule(Centi)
deriveSemimodule(Milli)
deriveSemimodule(Micro)
deriveSemimodule(Nano)
deriveSemimodule(Pico)
deriveSemimodule(Float)
deriveSemimodule(Double)
deriveSemimodule(CFloat)
deriveSemimodule(CDouble)


{-
instance Semimodule Natural Bool where 
  n .# a | n == mempty = False
         | otherwise   = a

instance Semimodule Natural Integer where 
  n .# a = toInteger n N.* a

instance Semimodule Natural Int where
  (.#) = (N.*) . fromIntegral

instance Semimodule Natural Int8 where
  (.#) = (N.*) . fromIntegral

instance Semimodule Natural Int16 where
  (.#) = (N.*) . fromIntegral

instance Semimodule Natural Word where
  (.#) = (N.*) . fromIntegral

instance Semimodule Natural Word8 where
  (.#) = (N.*) . fromNatural

instance Semimodule Natural Word16 where
  (.#) = (N.*) . fromNatural

instance Semimodule Natural Word32 where
  (.#) = (N.*) . fromNatural

instance Semimodule Natural Word64 where
  (.#) = (N.*) . fromNatural

instance Semimodule Integer Int where
  (.#) = (N.*) . fromInteger

instance Semimodule Integer Int8 where
  (.#) = (N.*) . fromInteger

instance Semimodule Integer Int16 where
  (.#) = (N.*) . fromInteger

instance Semimodule Integer Int32 where
  (.#) = (N.*) . fromInteger

instance Semimodule Integer Int64 where
  (.#) = (N.*) . fromInteger

instance Semimodule Integer Word where
  (.#) = (N.*) . N.fromInteger

instance Semimodule Integer Word8 where
  (.#) = (N.*) . N.fromInteger

instance Semimodule Integer Word16 where
  (.#) = (N.*) . N.fromInteger

instance Semimodule Integer Word32 where
  (.#) = (N.*) . N.fromInteger

instance Semimodule Integer Word64 where
  (.#) = (N.*) . N.fromInteger
-}


