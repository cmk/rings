{-# LANGUAGE Safe                       #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies                 #-}
module Data.Semimodule.Basis (
  -- * Euclidean bases
    E1(..), e1, fillE1
  , E2(..), e2, fillE2
  , E3(..), e3, fillE3
  , E4(..), e4, fillE4
  , E6(..)
) where

import safe Data.Functor.Rep
import safe Data.Semimodule
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)



-------------------------------------------------------------------------------
-- Standard basis on one real dimension
-------------------------------------------------------------------------------

data E1 = E1 deriving (Eq, Ord, Show)

e1 :: a -> E1 -> a
e1 = const

fillE1 :: Basis E1 f => a -> f a
fillE1 x = tabulate $ e1 x

-------------------------------------------------------------------------------
-- Standard basis on two real dimensions
-------------------------------------------------------------------------------

data E2 = E21 | E22 deriving (Eq, Ord, Show)

e2 :: a -> a -> E2 -> a
e2 x _ E21 = x
e2 _ y E22 = y

fillE2 :: Basis E2 f => a -> a -> f a
fillE2 x y = tabulate $ e2 x y

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

-------------------------------------------------------------------------------
-- Standard basis on five real dimensions
-------------------------------------------------------------------------------

data E5 = E51 | E52 | E53 | E54 | E55 deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Standard basis on six real dimensions
-------------------------------------------------------------------------------

data E6 = E61 | E62 | E63 | E64 | E65 | E66 deriving (Eq, Ord, Show)