{-# LANGUAGE GADTs, FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- AST Definition

data TABE where
  TNum :: TABE
  TBool :: TABE
  deriving (Show,Eq)

data ABE where
  Num :: Int -> ABE
  Plus :: ABE -> ABE -> ABE
  Minus :: ABE -> ABE -> ABE
  Mult :: ABE -> ABE -> ABE
  Div :: ABE -> ABE -> ABE
  Boolean :: Bool -> ABE
  And :: ABE -> ABE -> ABE
  Leq :: ABE -> ABE -> ABE
  IsZero :: ABE -> ABE
  If :: ABE -> ABE -> ABE -> ABE
  deriving (Show,Eq)

-- Evaluation Functions

evalM :: ABE -> (Maybe ABE)
evalM _ = Nothing -- Replace this with your interpreter

evalErr :: ABE -> (Maybe ABE)
evalErr _ = Nothing -- Replace this with your interpreter

-- Type Derivation Function

typeofM :: ABE -> Maybe TABE
typeofM _ = Nothing

-- Combined interpreter

evalTypeM :: ABE -> Maybe ABE
evalTypeM _ = Nothing

-- Optimizer

optimize :: ABE -> ABE
optimize e = e

interpOptM :: ABE -> Maybe ABE
interpOptM _ = Nothing
