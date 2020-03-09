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

module Data.Semimodule (
  -- * Left modules
    type LeftModule
  , LeftSemimodule(..)
  , (*.)
  , (/.)
  , (\.)
  , lerp
  , lscaleDef
  , negateDef
  -- * Right modules
  , type RightModule
  , RightSemimodule(..)
  , (.*)
  , (./)
  , (.\)
  , rscaleDef
  -- * Bimodules
  , type Bimodule
  , type FreeModule 
  , type FreeSemimodule
  , Bisemimodule(..)
  -- * Algebras 
  , type FreeAlgebra
  , Algebra(..)
  -- * Unital algebras 
  , type FreeUnital
  , Unital(..)
  -- * Coalgebras 
  , type FreeCoalgebra
  , Coalgebra(..)
  -- * Unital coalgebras 
  , type FreeCounital
  , Counital(..)
  -- * Bialgebras 
  , type FreeBialgebra
  , Bialgebra
) where

import safe Data.Complex
import safe Data.Fixed
import safe Data.Functor.Rep
import safe Data.Functor.Compose
import safe Data.Functor.Contravariant
import safe Data.Functor.Product
import safe Data.Int
import safe Data.Semifield
import safe Data.Semiring
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Real hiding (Fractional(..))
import safe Numeric.Natural
import safe Prelude (fromInteger)

import safe Control.Arrow
import safe Control.Applicative
import safe Control.Category (Category, (<<<), (>>>))
import safe Data.Bool
--import safe Data.Functor.Contravariant
--import safe qualified Data.Functor.Contravariant.Rep as F
import safe Data.Functor.Apply
import safe Data.Functor.Rep
import safe Data.Semiring
import safe Data.Tuple (swap)
import safe Prelude (Ord, reverse)
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Set as Set
import safe qualified Data.Sequence as Seq
import safe Data.Sequence hiding (reverse,index)
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe qualified Control.Category as C
import safe Test.Logic hiding (join)

-------------------------------------------------------------------------------
-- Left modules
-------------------------------------------------------------------------------

type LeftModule l a = (Ring l, (Additive-Group) a, LeftSemimodule l a)

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
class (Semiring l, (Additive-Monoid) a) => LeftSemimodule l a where
  -- | Left-multiply by a scalar.
  --
  lscale :: l -> a -> a


infixr 7 *., \., /., `lscaleDef`

-- | Left-multiply a module element by a scalar.
--
(*.) :: LeftSemimodule l a => l -> a -> a
(*.) = lscale

-- | Right-divide a vector by a scalar (on the left).
--
(/.) :: Semifield a => Functor f => a -> f a -> f a
a /. f = (/ a) <$> f

-- | Left-divide a vector by a scalar.
--
(\.) :: Semifield a => Functor f => a -> f a -> f a
a \. f = (a \\)  <$> f

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

-- | Default definition of '<<' for a commutative group.
--
negateDef :: LeftModule Integer a => a -> a
negateDef a = (-1 :: Integer) *. a

-------------------------------------------------------------------------------
-- Right modules
-------------------------------------------------------------------------------

type RightModule r a = (Ring r, (Additive-Group) a, RightSemimodule r a)

-- | < https://en.wikipedia.org/wiki/Semimodule Right semimodule > over a commutative semiring.
--
-- The laws for right semimodules are analagous to those of left semimodules.
--
-- See the properties module for a detailed specification.
--
class (Semiring r, (Additive-Monoid) a) => RightSemimodule r a where

  -- | Right-multiply by a scalar.
  --
  rscale :: r -> a -> a

infixl 7 .*, .\, ./, `rscaleDef`

-- | Right-multiply a module element by a scalar.
--
(.*) :: RightSemimodule r a => a -> r -> a
(.*) = flip rscale

-- | Right-divide a vector by a scalar.
--
(./) :: Semifield a => Functor f => f a -> a -> f a
(./) = flip (/.)

-- | Left-divide a vector by a scalar (on the right).
--
(.\) :: Semifield a => Functor f => f a -> a -> f a
(.\) = flip (\.)

-- | Default definition of 'rscale' for a free module.
--
rscaleDef :: Semiring a => Functor f => a -> f a -> f a
rscaleDef a f = (* a) <$> f

-------------------------------------------------------------------------------
-- Bimodules
-------------------------------------------------------------------------------

type Bimodule l r a = (LeftModule l a, RightModule r a, Bisemimodule l r a)

type FreeModule a f = (Free f, (Additive-Group) (f a), Bimodule a a (f a))

type FreeSemimodule a f = (Free f, Bisemimodule a a (f a))

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
-- Algebras
-------------------------------------------------------------------------------

-- | An algebra over a free module /f/.
--
-- Note that this is distinct from a < https://en.wikipedia.org/wiki/Free_algebra free algebra >.
--
type FreeAlgebra a f = (FreeSemimodule a f, Algebra a (Rep f))

-- | An < https://en.wikipedia.org/wiki/Algebra_over_a_field#Generalization:_algebra_over_a_ring algebra > over a semiring.
--
-- Note that the algebra < https://en.wikipedia.org/wiki/Non-associative_algebra needn't be associative >.
--
class Semiring a => Algebra a b where

  -- |
  --
  -- @
  -- 'joined' = 'runLin' 'diagonal' '.' 'uncurry'
  -- @
  --
  joined :: (b -> b -> a) -> b -> a

-------------------------------------------------------------------------------
-- Unital algebras
-------------------------------------------------------------------------------

-- | A unital algebra over a free semimodule /f/.
--
type FreeUnital a f = (FreeAlgebra a f, Unital a (Rep f))

-- | A < https://en.wikipedia.org/wiki/Algebra_over_a_field#Unital_algebra unital algebra > over a semiring.
--
class Algebra a b => Unital a b where

  -- |
  --
  -- @
  -- 'unital' = 'runLin' 'initial' '.' 'const'
  -- @
  --
  unital :: a -> b -> a

-------------------------------------------------------------------------------
-- Coalgebras
-------------------------------------------------------------------------------

-- | A coalgebra over a free semimodule /f/.
--
type FreeCoalgebra a f = (FreeSemimodule a f, Coalgebra a (Rep f))

-- | A coalgebra over a semiring.
--
class Semiring a => Coalgebra a c where

  -- |
  --
  -- @
  -- 'cojoined' = 'curry' '.' 'runLin' 'codiagonal'
  -- @
  --
  cojoined :: (c -> a) -> c -> c -> a
  
-------------------------------------------------------------------------------
-- Counital Coalgebras
-------------------------------------------------------------------------------

-- | A counital coalgebra over a free semimodule /f/.
--
type FreeCounital a f = (FreeCoalgebra a f, Counital a (Rep f))

-- | A counital coalgebra over a semiring.
--
class Coalgebra a c => Counital a c where

  -- @
  -- 'counital' = 'flip' ('runLin' 'counital') '()'
  -- @
  --
  counital :: (c -> a) -> a

-------------------------------------------------------------------------------
-- Bialgebras
-------------------------------------------------------------------------------

-- | A bialgebra over a free semimodule /f/.
--
type FreeBialgebra a f = (FreeAlgebra a f, FreeCoalgebra a f, Bialgebra a (Rep f))

-- | A < https://en.wikipedia.org/wiki/Bialgebra bialgebra > over a semiring.
--
class (Unital a b, Counital a b) => Bialgebra a b


-------------------------------------------------------------------------------
-- Module Instances
-------------------------------------------------------------------------------


instance Semiring a => LeftSemimodule a a where
  lscale = (*)

{-
instance Semiring l => LeftSemimodule l () where
  lscale _ = const ()

instance (Additive-Monoid) a => LeftSemimodule () a where 
  lscale _ = id

instance (Additive-Monoid) a => LeftSemimodule Natural a where
  lscale l a = unAdditive $ mreplicate l (Additive a)

instance ((Additive-Monoid) a, (Additive-Group) a) => LeftSemimodule Integer a where
  lscale l a = unAdditive $ greplicate l (Additive a)
-}

instance LeftSemimodule l a => LeftSemimodule l (e -> a) where 
  lscale l = fmap (l *.)

instance LeftSemimodule l a => LeftSemimodule l (Op a e) where 
  lscale l (Op f) = Op $ fmap (l *.) f



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
  lscale l (x :+ y) = (l * x) :+ (l * y)

{-
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
-}

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semiring a => RightSemimodule a a where
  rscale = (*)

{-
instance Semiring r => RightSemimodule r () where 
  rscale _ = const ()

instance (Additive-Monoid) a => RightSemimodule () a where 
  rscale _ = id

instance (Additive-Monoid) a => RightSemimodule Natural a where
  rscale r a = unAdditive $ mreplicate r (Additive a)

instance ((Additive-Monoid) a, (Additive-Group) a) => RightSemimodule Integer a where
  rscale r a = unAdditive $ greplicate r (Additive a)
-}

instance RightSemimodule r a => RightSemimodule r (e -> a) where 
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

{-
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
-}

instance Semiring a => Bisemimodule a a a

--instance Semiring r => Bisemimodule r r ()

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

instance (Additive-Monoid) a => LeftSemimodule () a where 
  lscale _ = id

instance (Additive-Monoid) a => LeftSemimodule Natural a where
  lscale l a = unAdditive $ mreplicate l (Additive a)

instance ((Additive-Monoid) a, (Additive-Group) a) => LeftSemimodule Integer a where
  lscale l a = unAdditive $ greplicate l (Additive a)

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

instance Semiring r => RightSemimodule r () where 
  rscale _ = const ()

instance (Additive-Monoid) a => RightSemimodule () a where 
  rscale _ = id

instance (Additive-Monoid) a => RightSemimodule Natural a where
  rscale r a = unAdditive $ mreplicate r (Additive a)

instance ((Additive-Monoid) a, (Additive-Group) a) => RightSemimodule Integer a where
  rscale r a = unAdditive $ greplicate r (Additive a)

instance RightSemimodule r a => RightSemimodule r (e -> a) where 
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
instance (Semiring r, Ord a, Additive b) => Coalgebra r (Map a b) where
  cojoined f as bs = f (Map.unionWith (+) as bs)
  counital k = k (Map.empty)

-- | The free commutative coalgebra over a set and Int
instance (Semiring r, Additive b) => Coalgebra r (IntMap b) where
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


