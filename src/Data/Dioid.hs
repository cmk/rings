{-# Language ConstraintKinds #-}
module Data.Dioid where

import Data.Connection.Yoneda
import Data.Semiring

type Dioid a = (Yoneda a, Semiring a)


