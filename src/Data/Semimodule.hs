{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Data.Semimodule where
{- (
  -- * Left modules
    type LeftModule
  , LeftSemimodule(..)
  , (*.)
  , lerp
  , lscaleDef
  , negateDef
  -- * Right modules
  , type RightModule
  , RightSemimodule(..)
  , (.*)
  , rscaleDef
  -- * Bimodules
  , type Bimodule
  , Bisemimodule(..)
) where

-}

--import safe Data.Functor.Contravariant
--import safe qualified Data.Functor.Contravariant.Rep as F
import safe Control.Applicative
import safe Control.Category (Category, (<<<), (>>>))
import safe Data.Bool
import safe Data.Complex
import safe Data.Fixed
import safe Data.Functor.Alt
import safe Data.Functor.Apply
import safe Data.Functor.Compose
import safe Data.Functor.Contravariant
import safe Data.Functor.Product
import safe Data.Functor.Rep
import safe Data.Int
import safe Data.Monoid hiding (Alt(..), Product(..), Sum(..))
import safe Data.Profunctor
import safe Data.Ring
import safe Data.Semiring
import safe Data.Sequence hiding (reverse,index)
import safe Data.Tuple (swap)
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Real hiding (Fractional(..))
import safe Numeric.Natural
import safe Prelude (Ord, reverse)
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe qualified Control.Category as C
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Sequence as Seq
import safe qualified Data.Set as Set
import safe qualified Prelude as P



-- | Lift a function into a profunctor arrow.
--
-- Usable w/ arrowow syntax w/ the /Arrows/ & /RebindableSyntax/ extensions.
--
-- @
-- (a '>>>' b) '>>>' c = a '>>>' (b '>>>' c)
-- 'arr' f '>>>' a = 'dimap' f id a
-- a '>>>' arrow f = 'dimap' id f a
-- 'arr' (g . f) = 'arr' f '>>>' 'arr' g
-- @
--
arrow :: (Category p, Profunctor p) => (a -> b) -> p a b
arrow f = rmap f C.id
{-# INLINE arrow #-}

fork :: b -> (b, b)
fork x = (x, x)

cofork :: Either c c -> c
cofork = either id id

coswap :: Either a b -> Either b a
coswap = either Right Left

pureP :: (Category p, Profunctor p) => b -> p a b
pureP = arrow . const

liftP2 :: (Category p, Strong p) => (b1 -> b2 -> b) -> p a b1 -> p a b2 -> p a b
liftP2 = divideR . uncurry

apply :: (Category p, Strong p) => p a (b -> c) -> p a b -> p a c
apply = liftP2 id
{-# INLINE apply #-}

-- > unapply . apply = id
-- > apply . unapply = id
--
unapply :: (Category p, Strong p, Closed p) => p a c -> p b c -> p a (b -> c)
unapply = (curry' .) . divideL id
{-# INLINE unapply #-}

--liftP2 :: (Category p, Strong p) => (b1 -> b2 -> b) -> p a b1 -> p a b2 -> p a b
--liftP2 f p q = 
--dimap (\x -> (x, x)) (uncurry f) $ proc p >>> proc q where
--  proc x = first' x >>> rmap swap C.id

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:divideL divideL >.
--
divideL :: (Category p, Strong p) => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
divideL f x y = dimap f fst $ x *** y
{-# INLINE divideL #-}

-- > divideR f x y = tabulate $ \s -> liftA2 (curry f) (sieve x s) (sieve y s)
divideR :: (Category p, Strong p) => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
divideR f p q = dimap fork f $ p *** q
{-# INLINE divideR #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:chooseL chooseL >.
--
chooseL :: (Category p, Choice p) => (a -> Either a1 a2) -> p a1 b -> p a2 b -> p a b 
chooseL f p q = dimap f cofork $ p +++ q
{-# INLINE chooseL #-}

chooseR :: (Category p, Choice p) => (Either b1 b2 -> b) -> p a b1 -> p a b2 -> p a b
chooseR f x y = dimap Left f $ x +++ y
{-# INLINE chooseR #-}

infixr 3 ***

(***) :: (Category p, Strong p) => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
x *** y = first' x >>> arrow swap >>> first' y >>> arrow swap
{-# INLINE (***) #-}

infixr 2 +++

(+++) :: (Category p, Choice p) => p a1 b1 -> p a2 b2 -> p (Either a1 a2) (Either b1 b2)
x +++ y = left' x >>> arrow coswap >>> left' y >>> arrow coswap
{-# INLINE (+++) #-}

infixr 3 &&&

(&&&) :: (Category p, Strong p) => p a b1 -> p a b2 -> p a (b1 , b2)
x &&& y = dimap fork id $ x *** y
{-# INLINE (&&&) #-}

infixr 2 |||

(|||) :: (Category p, Choice p) => p a1 b -> p a2 b -> p (Either a1 a2) b
x ||| y = dimap id cofork $ x +++ y
{-# INLINE (|||) #-}

ex1 :: (Category p, Profunctor p) => p (a , b) b
ex1 = arrow snd
{-# INLINE ex1 #-}

ex2 :: (Category p, Profunctor p) => p (a , b) a
ex2 = arrow fst
{-# INLINE ex2 #-}

inl :: (Category p, Profunctor p) => p a (Either a b)
inl = arrow Left
{-# INLINE inl #-}

inr :: (Category p, Profunctor p) => p b (Either a b)
inr = arrow Right
{-# INLINE inr #-}

-- | Swap components of a tensor product.
--
-- This is equivalent to a matrix transpose.
--
braid :: (Category p, Profunctor p) => p (a , b) (b , a)
braid = arrow swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
cobraid :: (Category p, Profunctor p) => p (Either a b) (Either b a)
cobraid = arrow coswap
{-# INLINE cobraid #-}

-------------------------------------------------------------------------------
-- Left modules
-------------------------------------------------------------------------------

type LeftModule l a = (Ring l, Ring a, LeftSemimodule l a)

-- | < https://en.wikipedia.org/wiki/Semimodule Left semimodule > over a commutative semiring.
--
-- All instances must satisfy the following identities:
-- 
-- @
-- 'lscale' s (x '+' y) = 'lscale' s x '+' 'lscale' s y
-- 'lscale' (s1 '+' s2) x = 'lscale' s1 x '+' 'lscale' s2 x
-- 'lscale' (s1 '*' s2) = 'lscale' s1 . 'lscale' s2
-- 'lscale' 'zero' = 'zero'
-- @
--
-- When the ring of coefficients /s/ is unital we must additionally have:
-- @
-- 'lscale' 'one' = 'id'
-- @
-- 
-- See the properties module for a detailed specification of the laws.
--
class (Semiring l, Semiring a) => LeftSemimodule l a where
  -- | Left-multiply by a scalar.
  --
  lscale :: l -> a -> a


infixr 7 *., `lscaleDef`

-- | Left-multiply a module element by a scalar.
--
(*.) :: LeftSemimodule l a => l -> a -> a
(*.) = lscale

-- | Linearly interpolate between two vectors.
--
-- >>> u = V3 (1 :% 1) (2 :% 1) (3 :% 1) :: V3 Rational
-- >>> v = V3 (2 :% 1) (4 :% 1) (6 :% 1) :: V3 Rational
-- >>> r = 1 :% 2 :: Rational
-- >>> lerp r u v
-- V3 (6 % 4) (12 % 4) (18 % 4)
--
lerp :: LeftModule r a => r -> a -> a -> a
lerp r f g = r *. f + (one - r) *. g

-- | Default definition of 'lscale' for a free module.
--
lscaleDef :: Semiring a => Functor f => a -> f a -> f a
lscaleDef a f = (a *) <$> f

-- | Default negation for a commutative group.
--
negateDef :: LeftModule Integer a => a -> a
negateDef a = negate @Integer one *. a

-------------------------------------------------------------------------------
-- Right modules
-------------------------------------------------------------------------------

type RightModule r a = (Ring r, Ring a, RightSemimodule r a)

-- | < https://en.wikipedia.org/wiki/Semimodule Right semimodule > over a commutative semiring.
--
-- The laws for right semimodules are analagous to those of left semimodules.
--
-- See the properties module for a detailed specification.
--
class (Semiring r, Semiring a) => RightSemimodule r a where

  -- | Right-multiply by a scalar.
  --
  rscale :: r -> a -> a

infixl 7 .*, `rscaleDef`

-- | Right-multiply a module element by a scalar.
--
(.*) :: RightSemimodule r a => a -> r -> a
(.*) = flip rscale

-- | Default definition of 'rscale' for a free module.
--
rscaleDef :: Semiring a => Functor f => a -> f a -> f a
rscaleDef a f = (* a) <$> f

-------------------------------------------------------------------------------
-- Bimodules
-------------------------------------------------------------------------------

type Bimodule l r a = (LeftModule l a, RightModule r a, Bisemimodule l r a)

-- | < https://en.wikipedia.org/wiki/Bimodule Bisemimodule > over a commutative semiring.
--
-- @
-- 'lscale' l . 'rscale' r = 'rscale' r . 'lscale' l
-- @
--
class (LeftSemimodule l a, RightSemimodule r a) => Bisemimodule l r a where

  -- | Left and right-multiply by two scalars.
  --
  discale :: l -> r -> a -> a
  discale l r = lscale l . rscale r

-------------------------------------------------------------------------------
-- Module Instances
-------------------------------------------------------------------------------

deriving via (A1 [] a) instance Semiring a => LeftSemimodule Natural [a] 
deriving via (Co ((->)e) a) instance LeftSemimodule l a => LeftSemimodule l (e -> a)

instance Semiring a => LeftSemimodule a a where
  lscale = (*)

{-
deriving via (Alt [] a) instance LeftSemimodule Natural [a]

instance Semiring a => LeftSemimodule a (Sum a) where
  lscale = lscaleDef

instance Alternative f => LeftSemimodule Natural (Alt f a) where
  lscale = mreplicate

instance (Representable f, LeftSemimodule l a) => LeftSemimodule l (Co f a) where
  lscale l = fmap (l *.)


instance Semiring l => LeftSemimodule l () where
  lscale _ = const ()

instance (Sum-Monoid) a => LeftSemimodule () a where 
  lscale _ = id

instance (Sum-Monoid) a => LeftSemimodule Natural a where
  lscale l a = unSum $ mreplicate l (Sum a)

instance ((Sum-Monoid) a, (Sum-Group) a) => LeftSemimodule Integer a where
  lscale l a = unSum $ greplicate l (Sum a)

instance LeftSemimodule Natural [a] where
  lscale l x = getAlt $ mreplicate l (Alt x)
  A1 x * A1 y = A1 $ liftF2 (<>) x y
  A1 x + A1 y = A1 $  x <!> y

instance LeftSemimodule Integer Centi where

-}

instance Semiring (A1 f a) => LeftSemimodule Natural (A1 f a) where
  lscale l = getSum . mreplicate l . Sum

instance (Representable f, LeftSemimodule l a) => LeftSemimodule l (Co f a) where
  lscale l = fmap (l *.)

instance LeftSemimodule l a => LeftSemimodule l (Op a e) where 
  lscale l (Op f) = Op $ fmap (l *.) f

instance LeftSemimodule Bool (Predicate a) where
  lscale b f = bool zero f b

--instance Ord a => LeftSemimodule Bool (Set.Set a) where
--  lscale b f = bool zero f b



{-

instance Semiring a => LeftSemimodule a (Op a e) where 
  lscale l (Op f) = Op $ fmap (l *) f

instance Semiring a => RightSemimodule a (Op a e) where 
  rscale r (Op f) = Op $ fmap (* r) f

instance Semiring a => Bisemimodule a a (Op a e)
-}

instance (LeftSemimodule l a, LeftSemimodule l b) => LeftSemimodule l (a, b) where
  lscale n (a, b) = (n *. a, n *. b)

instance (LeftSemimodule l a, LeftSemimodule l b, LeftSemimodule l c) => LeftSemimodule l (a, b, c) where
  lscale n (a, b, c) = (n *. a, n *. b, n *. c)

instance Semiring a => LeftSemimodule a (Ratio a) where 
  lscale l (x :% y) = (l * x) :% y

instance Ring a => LeftSemimodule a (Complex a) where 
  --lscale l (x :+ y) = (l * x) :+ (l * y)
  lscale = lscaleDef

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

-- | A generalization of 'Data.List.replicate' to an arbitrary 'Monoid'. 
--
-- Adapted from <http://augustss.blogspot.com/2008/07/lost-and-found-if-i-write-108-in.html>.
--
mreplicate :: Monoid a => Natural -> a -> a
mreplicate n a
    | n == 0 = mempty
    | otherwise = f a n
    where
        f x y 
            | even y = f (x <> x) (y `quot` 2)
            | y == 1 = x
            | otherwise = g (x <> x) ((y P.- 1) `quot` 2) x
        g x y z 
            | even y = g (x <> x) (y `quot` 2) z
            | y == 1 = x <> z
            | otherwise = g (x <> x) ((y P.- 1) `quot` 2) (x <> z)
{-# INLINE mreplicate #-}

deriving via (A1 [] a) instance Semiring a => RightSemimodule Natural [a]

deriving via (Co ((->)e) a) instance RightSemimodule r a => RightSemimodule r (e -> a)

instance Semiring a => RightSemimodule a a where
  rscale = (*)

instance LeftSemimodule l a => RightSemimodule (Dual l) a where
  rscale (Dual l) = lscale l

{-
instance Semiring r => RightSemimodule r () where 
  rscale _ = const ()

instance (Sum-Monoid) a => RightSemimodule () a where 
  rscale _ = id

-}

--instance (Alt f, Alternative f, Monoid a) => RightSemimodule Natural (A1 f a) where
--  rscale r (A1 x) = A1 . getSum $ mreplicate r (Sum x)

instance Semiring (A1 f a) => RightSemimodule Natural (A1 f a) where
  rscale l = getSum . mreplicate l . Sum

instance (Representable f, RightSemimodule r a) => RightSemimodule r (Co f a) where
  rscale r = fmap (.* r)

instance RightSemimodule r a => RightSemimodule r (Op a e) where 
  rscale r (Op f) = Op $ fmap (.* r) f

instance (RightSemimodule r a, RightSemimodule r b) => RightSemimodule r (a, b) where
  rscale n (a, b) = (a .* n, b .* n)

instance (RightSemimodule r a, RightSemimodule r b, RightSemimodule r c) => RightSemimodule r (a, b, c) where
  rscale n (a, b, c) = (a .* n, b .* n, c .* n)

instance Semiring a => RightSemimodule a (Ratio a) where 
  rscale r (x :% y) = (r * x) :% y


--instance Ring a => RightSemimodule a (Complex a) where 
--  rscale r (x :+ y) = (r * x) :+ (r * y)

--instance Ring a => RightSemimodule (Complex a) (Complex a) where 
--  rscale = (*) 


instance Semiring a => Bisemimodule a a a

instance LeftSemimodule l a => Bisemimodule l (Dual l) a where
-- instance Semiring r => Bisemimodule r r ()
instance Semiring a => Bisemimodule Natural Natural [a]

instance Bisemimodule r r a => Bisemimodule r r (e -> a)

instance Bisemimodule r r a => Bisemimodule r r (Op a e)

instance (Bisemimodule r r a, Bisemimodule r r b) => Bisemimodule r r (a, b)

instance (Bisemimodule r r a, Bisemimodule r r b, Bisemimodule r r c) => Bisemimodule r r (a, b, c)

instance Semiring a => Bisemimodule a a (Ratio a)

--instance Ring a => Bisemimodule a a (Complex a)

--instance Ring a => Bisemimodule (Complex a) (Complex a) (Complex a)




{-
#define deriveBisemimodule(ty)                     \
instance Bisemimodule ty ty ty                        \

deriveBisemimodule(Bool)
deriveBisemimodule(Int)
deriveBisemimodule(Int8)
deriveBisemimodule(Int16)
deriveBisemimodule(Int32)
deriveBisemimodule(Int64)
deriveBisemimodule(Word)
deriveBisemimodule(Word8)
deriveBisemimodule(Word16)
deriveBisemimodule(Word32)
deriveBisemimodule(Word64)
deriveBisemimodule(Uni)
deriveBisemimodule(Deci)
deriveBisemimodule(Centi)
deriveBisemimodule(Milli)
deriveBisemimodule(Micro)
deriveBisemimodule(Nano)
deriveBisemimodule(Pico)
deriveBisemimodule(Float)
deriveBisemimodule(Double)
deriveBisemimodule(CFloat)
deriveBisemimodule(CDouble)
deriveBisemimodule((Ratio Integer))
deriveBisemimodule((Ratio Natural))
-}

{-
-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semiring l => LeftSemimodule l () where 
  lscale _ = const ()

instance (Sum-Monoid) a => LeftSemimodule () a where 
  lscale _ = id

instance (Sum-Monoid) a => LeftSemimodule Natural a where
  lscale l a = unSum $ mreplicate l (Sum a)

instance ((Sum-Monoid) a, (Sum-Group) a) => LeftSemimodule Integer a where
  lscale l a = unSum $ greplicate l (Sum a)

instance LeftSemimodule l a => LeftSemimodule l (e -> a) where 
  lscale l = fmap (l *.)

instance LeftSemimodule l a => LeftSemimodule l (Op a e) where 
  lscale l (Op f) = Op $ fmap (l *.) f

instance (LeftSemimodule l a, LeftSemimodule l b) => LeftSemimodule l (a, b) where
  lscale n (a, b) = (n *. a, n *. b)

instance (LeftSemimodule l a, LeftSemimodule l b, LeftSemimodule l c) => LeftSemimodule l (a, b, c) where
  lscale n (a, b, c) = (n *. a, n *. b, n *. c)

instance Semiring a => LeftSemimodule a (Ratio a) where 
  lscale l (x :% y) = (l * x) :% y

instance Ring a => LeftSemimodule a (Complex a) where 
  lscale l (x :+ y) = (l * x) :+ (l * y)

--instance Ring a => LeftSemimodule (Complex a) (Complex a) where 
--   lscale = (*)  

#define deriveLeftSemimodule(ty)                      \
instance LeftSemimodule ty ty where {                 \
   lscale = (*)                                       \
;  {-# INLINE lscale #-}                              \
}

deriveLeftSemimodule(Bool)
deriveLeftSemimodule(Int)
deriveLeftSemimodule(Int8)
deriveLeftSemimodule(Int16)
deriveLeftSemimodule(Int32)
deriveLeftSemimodule(Int64)
deriveLeftSemimodule(Word)
deriveLeftSemimodule(Word8)
deriveLeftSemimodule(Word16)
deriveLeftSemimodule(Word32)
deriveLeftSemimodule(Word64)
deriveLeftSemimodule(Uni)
deriveLeftSemimodule(Deci)
deriveLeftSemimodule(Centi)
deriveLeftSemimodule(Milli)
deriveLeftSemimodule(Micro)
deriveLeftSemimodule(Nano)
deriveLeftSemimodule(Pico)
deriveLeftSemimodule(Float)
deriveLeftSemimodule(Double)
deriveLeftSemimodule(CFloat)
deriveLeftSemimodule(CDouble)
deriveLeftSemimodule((Ratio Integer))
deriveLeftSemimodule((Ratio Natural))

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------



instance RightSemimodule r a => RightSemimodule r (e -> a) where 
  rscale r = fmap (.* r)

instance Semiring r => RightSemimodule r () where 
  rscale _ = const ()

instance (Sum-Monoid) a => RightSemimodule () a where 
  rscale _ = id

instance (Sum-Monoid) a => RightSemimodule Natural a where
  rscale r a = unSum $ mreplicate r (Sum a)

instance ((Sum-Monoid) a, (Sum-Group) a) => RightSemimodule Integer a where
  rscale r a = unSum $ greplicate r (Sum a)

instance RightSemimodule r a => RightSemimodule r (Op a e) where 
  rscale r (Op f) = Op $ fmap (.* r) f

instance (RightSemimodule r a, RightSemimodule r b) => RightSemimodule r (a, b) where
  rscale n (a, b) = (a .* n, b .* n)

instance (RightSemimodule r a, RightSemimodule r b, RightSemimodule r c) => RightSemimodule r (a, b, c) where
  rscale n (a, b, c) = (a .* n, b .* n, c .* n)

instance Semiring a => RightSemimodule a (Ratio a) where 
  rscale r (x :% y) = (r * x) :% y

--instance Ring a => RightSemimodule a (Complex a) where 
--  rscale r (x :+ y) = (r * x) :+ (r * y)

--instance Ring a => RightSemimodule (Complex a) (Complex a) where 
--  rscale = (*) 

#define deriveRightSemimodule(ty)                     \
instance RightSemimodule ty ty where {                \
   rscale = (*)                                       \
;  {-# INLINE rscale #-}                              \
}

deriveRightSemimodule(Bool)
deriveRightSemimodule(Int)
deriveRightSemimodule(Int8)
deriveRightSemimodule(Int16)
deriveRightSemimodule(Int32)
deriveRightSemimodule(Int64)
deriveRightSemimodule(Word)
deriveRightSemimodule(Word8)
deriveRightSemimodule(Word16)
deriveRightSemimodule(Word32)
deriveRightSemimodule(Word64)
deriveRightSemimodule(Uni)
deriveRightSemimodule(Deci)
deriveRightSemimodule(Centi)
deriveRightSemimodule(Milli)
deriveRightSemimodule(Micro)
deriveRightSemimodule(Nano)
deriveRightSemimodule(Pico)
deriveRightSemimodule(Float)
deriveRightSemimodule(Double)
deriveRightSemimodule(CFloat)
deriveRightSemimodule(CDouble)
deriveRightSemimodule((Ratio Integer))
deriveRightSemimodule((Ratio Natural))

instance Semiring r => Bisemimodule r r ()

instance Bisemimodule r r a => Bisemimodule r r (e -> a)

instance Bisemimodule r r a => Bisemimodule r r (Op a e)

instance (Bisemimodule r r a, Bisemimodule r r b) => Bisemimodule r r (a, b)

instance (Bisemimodule r r a, Bisemimodule r r b, Bisemimodule r r c) => Bisemimodule r r (a, b, c)

instance Semiring a => Bisemimodule a a (Ratio a)

--instance Ring a => Bisemimodule a a (Complex a)

--instance Ring a => Bisemimodule (Complex a) (Complex a) (Complex a)


#define deriveBisemimodule(ty)                     \
instance Bisemimodule ty ty ty                        \

deriveBisemimodule(Bool)
deriveBisemimodule(Int)
deriveBisemimodule(Int8)
deriveBisemimodule(Int16)
deriveBisemimodule(Int32)
deriveBisemimodule(Int64)
deriveBisemimodule(Word)
deriveBisemimodule(Word8)
deriveBisemimodule(Word16)
deriveBisemimodule(Word32)
deriveBisemimodule(Word64)
deriveBisemimodule(Uni)
deriveBisemimodule(Deci)
deriveBisemimodule(Centi)
deriveBisemimodule(Milli)
deriveBisemimodule(Micro)
deriveBisemimodule(Nano)
deriveBisemimodule(Pico)
deriveBisemimodule(Float)
deriveBisemimodule(Double)
deriveBisemimodule(CFloat)
deriveBisemimodule(CDouble)
deriveBisemimodule((Ratio Integer))
deriveBisemimodule((Ratio Natural))

-}

{-
-------------------------------------------------------------------------------
-- Algebra instances
-------------------------------------------------------------------------------

{-
instance (Bisemimodule a a a, Algebra a b) => Semigroup (Multiplicative (Op a b)) where
  (<>) = liftA2 $ \(Op x) (Op y) -> Op $ x .*. y
-}

instance Semiring a => Algebra a () where
  joined f = f ()

instance Semiring a => Unital a () where
  unital r () = r

instance (Algebra a b1, Algebra a b2) => Algebra a (b1, b2) where
  joined f (a,b) = joined (\a1 a2 -> joined (\b1 b2 -> f (a1,b1) (a2,b2)) b) a

instance (Unital a b1, Unital a b2) => Unital a (b1, b2) where
  unital r (a,b) = unital r a * unital r b

instance (Algebra a b1, Algebra a b2, Algebra a b3) => Algebra a (b1, b2, b3) where
  joined f (a,b,c) = joined (\a1 a2 -> joined (\b1 b2 -> joined (\c1 c2 -> f (a1,b1,c1) (a2,b2,c2)) c) b) a

instance (Unital a b1, Unital a b2, Unital a b3) => Unital a (b1, b2, b3) where
  unital r (a,b,c) = unital r a * unital r b * unital r c

-- | Tensor algebra on /b/.
--
-- >>> joined (<>) [1..3 :: Int]
-- [1,2,3,1,2,3,1,2,3,1,2,3]
--
-- >>> joined (\f g -> fold (f ++ g)) [1..3] :: Int
-- 24
--
instance Semiring a => Algebra a [b] where
  joined f = go [] where
    go ls rrs@(r:rs) = f (reverse ls) rrs + go (r:ls) rs
    go ls [] = f (reverse ls) []

instance Semiring a => Unital a [b] where
  unital a [] = a
  unital _ _ = zero

instance Semiring a => Algebra a (Seq b) where
  joined f = go Seq.empty where
    go ls s = case viewl s of
       EmptyL -> f ls s 
       r :< rs -> f ls s + go (ls |> r) rs

instance Semiring a => Unital a (Seq b) where
  unital a b | Seq.null b = a
             | otherwise = zero

instance (Semiring a, Ord b) => Algebra a (Set.Set b) where
  joined f = go Set.empty where
    go ls s = case Set.minView s of
       Nothing -> f ls s
       Just (r, rs) -> f ls s + go (Set.insert r ls) rs

instance (Semiring a, Ord b) => Unital a (Set.Set b) where
  unital a b | Set.null b = a
           | otherwise = zero

instance Semiring a => Algebra a IntSet.IntSet where
  joined f = go IntSet.empty where
    go ls s = case IntSet.minView s of
       Nothing -> f ls s
       Just (r, rs) -> f ls s + go (IntSet.insert r ls) rs

instance Semiring a => Unital a IntSet.IntSet where
  unital a b | IntSet.null b = a
             | otherwise = zero

---------------------------------------------------------------------
-- Coalgebra instances
---------------------------------------------------------------------


instance Semiring a => Coalgebra a () where
  cojoined = const

instance Semiring a => Counital a () where
  counital f = f ()

instance (Coalgebra a c1, Coalgebra a c2) => Coalgebra a (c1, c2) where
  cojoined f (a1,b1) (a2,b2) = cojoined (\a -> cojoined (\b -> f (a,b)) b1 b2) a1 a2

instance (Counital a c1, Counital a c2) => Counital a (c1, c2) where
  counital k = counital $ \a -> counital $ \b -> k (a,b)

instance (Coalgebra a c1, Coalgebra a c2, Coalgebra a c3) => Coalgebra a (c1, c2, c3) where
  cojoined f (a1,b1,c1) (a2,b2,c2) = cojoined (\a -> cojoined (\b -> cojoined (\c -> f (a,b,c)) c1 c2) b1 b2) a1 a2

instance (Counital a c1, Counital a c2, Counital a c3) => Counital a (c1, c2, c3) where
  counital k = counital $ \a -> counital $ \b -> counital $ \c -> k (a,b,c)

instance Algebra a b => Coalgebra a (b -> a) where
  cojoined k f g = k (f * g)

instance Unital a b => Counital a (b -> a) where
  counital f = f one

-- | The tensor coalgebra on /c/.
--
instance Semiring a => Coalgebra a [c] where
  cojoined f as bs = f (mappend as bs)

instance Semiring a => Counital a [c] where
  counital f = f []

instance Semiring a => Coalgebra a (Seq c) where
  cojoined f as bs = f (mappend as bs)

instance Semiring a => Counital a (Seq c) where
  counital f = f Seq.empty

-- | The free commutative band coalgebra
instance (Semiring a, Ord c) => Coalgebra a (Set.Set c) where
  cojoined f as bs = f (Set.union as bs)

instance (Semiring a, Ord c) => Counital a (Set.Set c) where
  counital f = f Set.empty

-- | The free commutative band coalgebra over Int
instance Semiring a => Coalgebra a IntSet.IntSet where
  cojoined f as bs = f (IntSet.union as bs)

instance Semiring a => Counital a IntSet.IntSet where
  counital f = f IntSet.empty

{-

  joined = runLin diagonal . uncurry
  counital = flip (runLin counital) ()
  unital = runLin initial . const
  cojoined = curry . runLin codiagonal

-- | The free commutative coalgebra over a set and a given semigroup
instance (Semiring r, Ord a, Sum b) => Coalgebra r (Map a b) where
  cojoined f as bs = f (Map.unionWith (+) as bs)
  counital k = k (Map.empty)

-- | The free commutative coalgebra over a set and Int
instance (Semiring r, Sum b) => Coalgebra r (IntMap b) where
  cojoined f as bs = f (IntMap.unionWith (+) as bs)
  counital k = k (IntMap.empty)
-}

---------------------------------------------------------------------
-- Bialgebra instances
---------------------------------------------------------------------

instance Semiring a => Bialgebra a () where
instance (Bialgebra a b1, Bialgebra a b2) => Bialgebra a (b1, b2) where
instance (Bialgebra a b1, Bialgebra a b2, Bialgebra a b3) => Bialgebra a (b1, b2, b3) where

instance Semiring a => Bialgebra a [b]
instance Semiring a => Bialgebra a (Seq b)

-}
