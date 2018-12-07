{-# LANGUAGE DeriveGeneric #-}

module Common where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)


data Operation = Mult
               | Sub
               | Add
               deriving (Show, Generic, Typeable)
