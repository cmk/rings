{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RankNTypes               #-}

module Data.Semimodule.Vector (
    type Basis
  , (*.)
  , (.*)
  , (.*.)
  , (><)
  , triple
  , lerp
  , quadrance
  , qd
  , dirac
  , module Data.Semimodule.Vector
) where

import safe Control.Applicative
import safe Data.Algebra
import safe Data.Bool
import safe Data.Distributive
import safe Data.Functor.Rep
import safe Data.Semifield
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Semimodule
import safe Data.Semiring
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)

-------------------------------------------------------------------------------
-- V2
-------------------------------------------------------------------------------

data V2 a = V2 !a !a deriving (Eq,Ord,Show)

-- | Vector addition.
--
-- >>> V2 1 2 <> V2 3 4
-- V2 4 6
--
instance (Additive-Semigroup) a => Semigroup (V2 a) where
  (<>) = mzipWithRep (+)

-- | Matrix addition.
--
-- >>> m23 1 2 3 4 5 6 <> m23 7 8 9 1 2 3 :: M23 Int
-- V2 (V3 8 10 12) (V3 5 7 9)
--
instance (Additive-Semigroup) a => Semigroup (Additive (V2 a)) where
  (<>) = liftA2 $ mzipWithRep (+)

instance (Additive-Monoid) a => Monoid (V2 a) where
  mempty = pureRep zero

instance (Additive-Monoid) a => Monoid (Additive (V2 a)) where
  mempty = pure $ pureRep zero

-- | Vector subtraction.
--
-- >>> V2 1 2 << V2 3 4
-- V2 (-2) (-2)
--
instance (Additive-Group) a => Magma (V2 a) where
  (<<) = mzipWithRep (-)

-- | Matrix subtraction.
--
-- >>> m23 1 2 3 4 5 6 << m23 7 8 9 1 2 3 :: M23 Int
-- V2 (V3 (-6) (-6) (-6)) (V3 3 3 3)
--
instance (Additive-Group) a => Magma (Additive (V2 a)) where
  (<<) = liftA2 $ mzipWithRep (-)

instance (Additive-Group) a => Quasigroup (V2 a)
instance (Additive-Group) a => Quasigroup (Additive (V2 a))
instance (Additive-Group) a => Loop (V2 a)
instance (Additive-Group) a => Loop (Additive (V2 a)) 
instance (Additive-Group) a => Group (V2 a)
instance (Additive-Group) a => Group (Additive (V2 a)) 

instance Semiring a => Semimodule a (V2 a) where
  (*.) = multl
  {-# INLINE (*.) #-}

instance Functor V2 where
  fmap f (V2 a b) = V2 (f a) (f b)
  {-# INLINE fmap #-}
  a <$ _ = V2 a a
  {-# INLINE (<$) #-}

instance Applicative V2 where
  pure = pureRep
  liftA2 = liftR2

instance Foldable V2 where
  foldMap f (V2 a b) = f a <> f b
  {-# INLINE foldMap #-}
  null _ = False
  length _ = two

instance Foldable1 V2 where
  foldMap1 f (V2 a b) = f a <> f b
  {-# INLINE foldMap1 #-}

instance Distributive V2 where
  distribute f = V2 (fmap (\(V2 x _) -> x) f) (fmap (\(V2 _ y) -> y) f)
  {-# INLINE distribute #-}

instance Representable V2 where
  type Rep V2 = I2
  tabulate f = V2 (f I21) (f I22)
  {-# INLINE tabulate #-}

  index (V2 x _) I21 = x
  index (V2 _ y) I22 = y
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- Standard basis on two real dimensions
-------------------------------------------------------------------------------

data I2 = I21 | I22 deriving (Eq, Ord, Show)

i2 :: a -> a -> I2 -> a
i2 x _ I21 = x
i2 _ y I22 = y

fillI2 :: Basis I2 f => a -> a -> f a
fillI2 x y = tabulate $ i2 x y

instance Semigroup (Additive I2) where
  Additive I21 <> x = x
  x <> Additive I21 = x
 
  Additive I22 <> Additive I22 = Additive I21

instance Monoid (Additive I2) where
  mempty = pure I21

-- trivial diagonal algebra
instance Semiring r => Algebra r I2 where
  multiplyWith f = f' where
    fi = f I21 I21
    fj = f I22 I22

    f' I21 = fi
    f' I22 = fj

instance Semiring r => Composition r I2 where
  conjugateWith = id

  normWith f = flip multiplyWith I21 $ \ix1 ix2 ->
                 flip multiplyWith I22 $ \jx1 jx2 ->
                   f ix1 * f ix2 + f jx1 * f jx2

-------------------------------------------------------------------------------
-- V3
-------------------------------------------------------------------------------


data V3 a = V3 !a !a !a deriving (Eq,Ord,Show)

-- | Vector addition.
--
-- >>> V3 1 2 3 <> V3 4 5 6
-- V3 5 7 9
--
instance (Additive-Semigroup) a => Semigroup (V3 a) where
  (<>) = mzipWithRep (+)

-- | Matrix addition.
--
-- >>> V2 (V3 1 2 3) (V3 4 5 6) <> V2 (V3 7 8 9) (V3 1 2 3)
-- V2 (V3 8 10 12) (V3 5 7 9)
--
instance (Additive-Semigroup) a => Semigroup (Additive (V3 a)) where
  (<>) = liftA2 $ mzipWithRep (+)

instance (Additive-Monoid) a => Monoid (V3 a) where
  mempty = pureRep zero

instance (Additive-Monoid) a => Monoid (Additive (V3 a)) where
  mempty = pure $ pureRep zero

-- | Vector subtraction.
--
-- >>> V3 1 2 3 << V3 4 5 6
-- V3 (-3) (-3) (-3)
--
instance (Additive-Group) a => Magma (V3 a) where
  (<<) = mzipWithRep (-)

-- | Matrix subtraction.
--
-- >>> V3 (V3 1 2 3) (V3 4 5 6) (V3 7 8 9) << V3 (V3 7 8 9) (V3 7 8 9) (V3 7 8 9) 
-- V3 (V3 (-6) (-6) (-6)) (V3 (-3) (-3) (-3)) (V3 0 0 0)
--
instance (Additive-Group) a => Magma (Additive (V3 a)) where
  (<<) = liftA2 $ mzipWithRep (-)

instance (Additive-Group) a => Quasigroup (V3 a)
instance (Additive-Group) a => Quasigroup (Additive (V3 a))
instance (Additive-Group) a => Loop (V3 a)
instance (Additive-Group) a => Loop (Additive (V3 a)) 
instance (Additive-Group) a => Group (V3 a)
instance (Additive-Group) a => Group (Additive (V3 a)) 

instance Semiring a => Semimodule a (V3 a) where
  (*.) = multl
  {-# INLINE (*.) #-}

instance Functor V3 where
  fmap f (V3 a b c) = V3 (f a) (f b) (f c)
  {-# INLINE fmap #-}
  a <$ _ = V3 a a a
  {-# INLINE (<$) #-}

instance Applicative V3 where
  pure = pureRep
  liftA2 = liftR2

instance Foldable V3 where
  foldMap f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap #-}
  null _ = False
  --length _ = 3

instance Foldable1 V3 where
  foldMap1 f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap1 #-}

instance Distributive V3 where
  distribute f = V3 (fmap (\(V3 x _ _) -> x) f) (fmap (\(V3 _ y _) -> y) f) (fmap (\(V3 _ _ z) -> z) f)
  {-# INLINE distribute #-}

instance Representable V3 where
  type Rep V3 = I3
  tabulate f = V3 (f I31) (f I32) (f I33)
  {-# INLINE tabulate #-}

  index (V3 x _ _) I31 = x
  index (V3 _ y _) I32 = y
  index (V3 _ _ z) I33 = z
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- Standard basis on three real dimensions 
-------------------------------------------------------------------------------

data I3 = I31 | I32 | I33 deriving (Eq, Ord, Show)

i3 :: a -> a -> a -> I3 -> a
i3 x _ _ I31 = x
i3 _ y _ I32 = y
i3 _ _ z I33 = z

fillI3 :: Basis I3 f => a -> a -> a -> f a
fillI3 x y z = tabulate $ i3 x y z

instance Semigroup (Additive I3) where
  Additive I31 <> x = x
  x <> Additive I31 = x
 
  Additive I32 <> Additive I33 = Additive I31 
  Additive I33 <> Additive I32 = Additive I31

  Additive I32 <> Additive I32 = Additive I33
  Additive I33 <> Additive I33 = Additive I32

instance Monoid (Additive I3) where
  mempty = pure I31

instance Ring r => Algebra r I3 where
  multiplyWith f = f' where
    i31 = f I32 I33 - f I33 I32
    i32 = f I33 I31 - f I31 I33
    i33 = f I31 I32 - f I32 I31 
    f' I31 = i31
    f' I32 = i32
    f' I33 = i33

instance Ring r => Composition r I3 where
  conjugateWith = id

  normWith f = flip multiplyWith' I31 $ \ix1 ix2 ->
                 flip multiplyWith' I32 $ \jx1 jx2 ->
                   flip multiplyWith' I33 $ \kx1 kx2 ->
                     f ix1 * f ix2 + f jx1 * f jx2 + f kx1 * f kx2

   where
    multiplyWith' f1 = f1' where
      i31 = f1 I31 I31
      i32 = f1 I32 I32
      i33 = f1 I33 I33
      f1' I31 = i31
      f1' I32 = i32
      f1' I33 = i33


-------------------------------------------------------------------------------
-- QuaternionBasis
-------------------------------------------------------------------------------

type QuaternionBasis = Maybe I3

instance Ring r => Algebra r QuaternionBasis where
  multiplyWith f = maybe fe f' where
    e = Nothing
    i = Just I31
    j = Just I32
    k = Just I33
    fe = f e e - (f i i + f j j + f k k)
    fi = f e i + f i e + (f j k - f k j)
    fj = f e j + f j e + (f k i - f i k)
    fk = f e k + f k e + (f i j - f j i)
    f' I31 = fi
    f' I32 = fj
    f' I33 = fk

instance Ring r => Unital r QuaternionBasis where
  unitWith x Nothing = x 
  unitWith _ _ = zero

instance Ring r => Composition r QuaternionBasis where
  conjugateWith f = maybe fe f' where
    fe = f Nothing
    f' I31 = negate . f $ Just I31
    f' I32 = negate . f $ Just I32
    f' I33 = negate . f $ Just I33

  normWith f = flip multiplyWith zero $ \ix1 ix2 -> f ix1 * conjugateWith f ix2

instance Field r => Division r QuaternionBasis where
  reciprocalWith f i = conjugateWith f i / normWith f 
{-
reciprocal'' x = divq unit x

divq (Quaternion r0 (V3 r1 r2 r3)) (Quaternion q0 (V3 q1 q2 q3)) =
 (/denom) <$> Quaternion (r0*q0 + r1*q1 + r2*q2 + r3*q3) imag
  where denom = q0*q0 + q1*q1 + q2*q2 + q3*q3
        imag = (V3 (r0*q1 + (negate r1*q0) + (negate r2*q3) + r3*q2)
                   (r0*q2 + r1*q3 + (negate r2*q0) + (negate r3*q1))
                   (r0*q3 + (negate r1*q2) + r2*q1 + (negate r3*q0)))

-}

-------------------------------------------------------------------------------
-- V4
-------------------------------------------------------------------------------

data V4 a = V4 !a !a !a !a deriving (Eq,Ord,Show)

-- | Vector addition.
--
-- >>> V4 1 2 3 4 <> V4 5 6 7 8
-- V4 6 8 10 12 
--
instance (Additive-Semigroup) a => Semigroup (V4 a) where
  (<>) = mzipWithRep (+)

-- | Matrix addition.
--
-- >>> m24 1 2 3 4 5 6 7 8 <> m24 1 2 3 4 5 6 7 8 :: M24 Int
-- V2 (V4 2 4 6 8) (V4 10 12 14 16)
--
instance (Additive-Semigroup) a => Semigroup (Additive (V4 a)) where
  (<>) = liftA2 $ mzipWithRep (+)

instance (Additive-Monoid) a => Monoid (V4 a) where
  mempty = pureRep zero

instance (Additive-Monoid) a => Monoid (Additive (V4 a)) where
  mempty = pure $ pureRep zero

-- | Vector subtraction.
--
-- >>> V4 1 2 3 << V4 4 5 6
-- V4 (-3) (-3) (-3)
--
instance (Additive-Group) a => Magma (V4 a) where
  (<<) = mzipWithRep (-)

-- | Matrix subtraction.
--
-- >>> V4 (V4 1 2 3) (V4 4 5 6) (V4 7 8 9) << V4 (V4 7 8 9) (V4 7 8 9) (V4 7 8 9) 
-- V4 (V4 (-6) (-6) (-6)) (V4 (-3) (-3) (-3)) (V4 0 0 0)
--
instance (Additive-Group) a => Magma (Additive (V4 a)) where
  (<<) = liftA2 $ mzipWithRep (-)

instance (Additive-Group) a => Quasigroup (V4 a)
instance (Additive-Group) a => Quasigroup (Additive (V4 a))
instance (Additive-Group) a => Loop (V4 a)
instance (Additive-Group) a => Loop (Additive (V4 a)) 
instance (Additive-Group) a => Group (V4 a)
instance (Additive-Group) a => Group (Additive (V4 a)) 

instance Semiring a => Semimodule a (V4 a) where
  (*.) = multl
  {-# INLINE (*.) #-}

instance Functor V4 where
  fmap f (V4 a b c d) = V4 (f a) (f b) (f c) (f d)
  {-# INLINE fmap #-}
  a <$ _ = V4 a a a a
  {-# INLINE (<$) #-}

instance Applicative V4 where
  pure = pureRep
  liftA2 = liftR2

instance Foldable V4 where
  foldMap f (V4 a b c d) = f a <> f b <> f c <> f d
  {-# INLINE foldMap #-}
  null _ = False
  length _ = two + two

instance Foldable1 V4 where
  foldMap1 f (V4 a b c d) = f a <> f b <> f c <> f d
  {-# INLINE foldMap1 #-}

instance Distributive V4 where
  distribute f = V4 (fmap (\(V4 x _ _ _) -> x) f) (fmap (\(V4 _ y _ _) -> y) f) (fmap (\(V4 _ _ z _) -> z) f) (fmap (\(V4 _ _ _ w) -> w) f)
  {-# INLINE distribute #-}

instance Representable V4 where
  type Rep V4 = I4
  tabulate f = V4 (f I41) (f I42) (f I43) (f I44)
  {-# INLINE tabulate #-}

  index (V4 x _ _ _) I41 = x
  index (V4 _ y _ _) I42 = y
  index (V4 _ _ z _) I43 = z
  index (V4 _ _ _ w) I44 = w
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- Standard basis on four real dimensions
-------------------------------------------------------------------------------

data I4 = I41 | I42 | I43 | I44 deriving (Eq, Ord, Show)

i4 :: a -> a -> a -> a -> I4 -> a
i4 x _ _ _ I41 = x
i4 _ y _ _ I42 = y
i4 _ _ z _ I43 = z
i4 _ _ _ w I44 = w

fillI4 :: Basis I4 f => a -> a -> a -> a -> f a
fillI4 x y z w = tabulate $ i4 x y z w
