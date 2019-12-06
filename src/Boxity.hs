{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE OverloadedStrings #-}
module Boxity where

import Protolude

import Data.Text.Prettyprint.Doc

data Boxity
  = Unboxed
  | Boxed
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Pretty Boxity where
  pretty boxity =
    case boxity of
      Unboxed ->
        "unboxed"

      Boxed ->
        "boxed"

prettyAnnotation :: Boxity -> Doc ann
prettyAnnotation boxity =
  case boxity of
    Unboxed ->
      ""

    Boxed ->
      "boxed"
