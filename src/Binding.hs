{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language TupleSections #-}
module Binding where

import Protolude

import Data.Persist

import Name (Name)
import qualified Span

data Binding
  = Spanned !Span.Relative !Name
  | Unspanned !Name
  deriving (Eq, Show, Generic, Persist, Hashable)

toName :: Binding -> Name
toName bindings =
  case bindings of
    Spanned _ name ->
      name

    Unspanned name ->
      name

