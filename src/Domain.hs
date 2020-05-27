{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
module Domain where

import Protolude hiding (Type, Seq, IntMap)

import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Flexibility (Flexibility)
import qualified Flexibility
import Index
import Literal (Literal)
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Syntax
import Var (Var)

data Value
  = Neutral !Head Spine
  | Con !Name.QualifiedConstructor (Tsil (Plicity, Value))
  | Lit !Literal
  | Glued !Head Spine !(Lazy Value)
  | Lam !Name !Type !Plicity !Closure
  | Pi !Name !Type !Plicity !Closure
  | Fun !Type !Plicity !Type

type Type = Value

data Head
  = Var !Var
  | Global !Name.Qualified
  | Meta !Meta.Index
  deriving (Show, Eq)

newtype Spine = Spine (Tsil Elimination)

pattern Empty :: Spine
pattern Empty =
  Spine Tsil.Empty

pattern (:>) :: Spine -> Elimination -> Spine
pattern spine :> elimination <- Spine ((Spine -> spine) Tsil.:> elimination)
  where
    Spine spine :> elimination =
      case (spine, elimination) of
        (spine' Tsil.:> Apps args, Apps args') ->
          Spine $ spine' Tsil.:> Apps (args <> args')

        _ ->
          Spine $ spine Tsil.:> elimination

data Elimination
  = Apps (Tsil (Plicity, Value))
  | Case !Branches

type Environment = Environment.Environment Value

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

data Branches where
  Branches :: Environment v -> Syntax.Branches v -> Maybe (Syntax.Term v) -> Branches

var :: Var -> Value
var v = Neutral (Domain.Var v) mempty

global :: Name.Qualified -> Value
global g = Neutral (Global g) mempty

con :: Name.QualifiedConstructor -> Value
con c = Con c mempty

meta :: Meta.Index -> Value
meta i = Neutral (Meta i) mempty

singleVarView :: Value -> Maybe Var
singleVarView (Neutral (Var v) Empty) = Just v
singleVarView _ = Nothing

headFlexibility :: Head -> Flexibility
headFlexibility = \case
  Var _ ->
    Flexibility.Rigid

  Global _ ->
    Flexibility.Rigid

  Meta _ ->
    Flexibility.Flexible

pattern AppsSpine :: Tsil (Plicity, Value) -> Spine
pattern AppsSpine args <- (appsView -> Just args)
  where
    AppsSpine args =
      case args of
        Tsil.Empty ->
          Empty

        _ ->
          Empty :> Apps args

appsView :: Spine -> Maybe (Tsil (Plicity, Value))
appsView spine =
  case spine of
    Empty ->
      Just Tsil.Empty

    Empty :> Apps args ->
      Just args

    _ ->
      Nothing

instance Semigroup Spine where
  Spine elims1 <> Spine elims2 =
    case elims2 of
      elims2' Tsil.:> elim ->
        (Spine elims1 <> Spine elims2') :> elim

      Tsil.Empty ->
        Spine elims1

instance Monoid Spine where
  mempty =
    Empty
