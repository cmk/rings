{-# LANGUAGE Safe                       #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ConstraintKinds            #-}
module Data.Semimodule.Basis (
    type Basis
  , type Basis2
  , type Basis3
  -- * Euclidean bases
  , E1(..), e1, fillE1
  , E2(..), e2, fillE2
  , E3(..), e3, fillE3
  , E4(..), e4, fillE4
) where

import safe Data.Functor.Rep
import safe Data.Semiring
import safe Data.Semimodule
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe Control.Monad as M

type Basis b f = (Free f, Rep f ~ b, Eq b)

type Basis2 b c f g = (Basis b f, Basis c g)

type Basis3 b c d f g h = (Basis b f, Basis c g, Basis d h)

-------------------------------------------------------------------------------
-- Standard basis on one real dimension
-------------------------------------------------------------------------------

data E1 = E11 deriving (Eq, Ord, Show)

e1 :: a -> E1 -> a
e1 = const

fillE1 :: Basis E1 f => a -> f a
fillE1 x = tabulate $ e1 x

-- The squaring function /N(x) = x^2/ on the real number field forms the primordial composition algebra.
--
instance Semiring r => Algebra r E1 where
  joined = M.join

instance Semiring r => Unital r E1 where
  unital = const

instance Semiring r => Coalgebra r E1 where
  cojoined f E11 E11 = f E11

instance Semiring r => Counital r E1 where
  counital f = f E11

instance Semiring r => Bialgebra r E1

-------------------------------------------------------------------------------
-- Standard basis on two real dimensions
-------------------------------------------------------------------------------

data E2 = E21 | E22 deriving (Eq, Ord, Show)

e2 :: a -> a -> E2 -> a
e2 x _ E21 = x
e2 _ y E22 = y

fillE2 :: Basis E2 f => a -> a -> f a
fillE2 x y = tabulate $ e2 x y

instance Semiring r => Algebra r E2 where
  joined = M.join

instance Semiring r => Unital r E2 where
  unital = const

instance Semiring r => Coalgebra r E2 where
  cojoined f E21 E21 = f E21
  cojoined f E22 E22 = f E22
  cojoined _ _ _ = zero

instance Semiring r => Counital r E2 where
  counital f = f E21 + f E22

instance Semiring r => Bialgebra r E2

-------------------------------------------------------------------------------
-- Standard basis on three real dimensions 
-------------------------------------------------------------------------------

data E3 = E31 | E32 | E33 deriving (Eq, Ord, Show)

e3 :: a -> a -> a -> E3 -> a
e3 x _ _ E31 = x
e3 _ y _ E32 = y
e3 _ _ z E33 = z

fillE3 :: Basis E3 f => a -> a -> a -> f a
fillE3 x y z = tabulate $ e3 x y z

instance Semiring r => Algebra r E3 where
  joined = M.join

instance Semiring r => Unital r E3 where
  unital = const

instance Semiring r => Coalgebra r E3 where
  cojoined f E31 E31 = f E31
  cojoined f E32 E32 = f E32
  cojoined f E33 E33 = f E33
  cojoined _ _ _ = zero

instance Semiring r => Counital r E3 where
  counital f = f E31 + f E32 + f E33

instance Semiring r => Bialgebra r E3

-------------------------------------------------------------------------------
-- Standard basis on four real dimensions
-------------------------------------------------------------------------------

data E4 = E41 | E42 | E43 | E44 deriving (Eq, Ord, Show)

e4 :: a -> a -> a -> a -> E4 -> a
e4 x _ _ _ E41 = x
e4 _ y _ _ E42 = y
e4 _ _ z _ E43 = z
e4 _ _ _ w E44 = w

fillE4 :: Basis E4 f => a -> a -> a -> a -> f a
fillE4 x y z w = tabulate $ e4 x y z w

instance Semiring r => Algebra r E4 where
  joined = M.join

instance Semiring r => Unital r E4 where
  unital = const

instance Semiring r => Coalgebra r E4 where
  cojoined f E41 E41 = f E41
  cojoined f E42 E42 = f E42
  cojoined f E43 E43 = f E43
  cojoined f E44 E44 = f E44
  cojoined _ _ _ = zero

instance Semiring r => Counital r E4 where
  counital f = f E41 + f E42 + f E43 + f E44

instance Semiring r => Bialgebra r E4

{-
-------------------------------------------------------------------------------
-- Standard basis on five real dimensions
-------------------------------------------------------------------------------

data E5 = E51 | E52 | E53 | E54 | E55 deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Standard basis on six real dimensions
-------------------------------------------------------------------------------

data E6 = E61 | E62 | E63 | E64 | E65 | E66 deriving (Eq, Ord, Show)
-}
