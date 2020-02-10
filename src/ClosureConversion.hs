{-# language FlexibleContexts #-}
module ClosureConversion where

import Protolude
import Rock

import qualified ClosureConverted.Syntax as ClosureConverted
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified Name
import Query (Query)
import qualified Query
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

convertDefinition
  :: MonadFetch Query m
  => LambdaLifted.Definition
  -> m ClosureConverted.Definition
convertDefinition def =
  case def of
    LambdaLifted.TypeDeclaration type_ ->
      ClosureConverted.TypeDeclaration <$> convertTerm type_

    LambdaLifted.ConstantDefinition (Telescope.Empty term) ->
      ClosureConverted.ConstantDefinition <$> convertTerm term

    LambdaLifted.ConstantDefinition tele ->
      ClosureConverted.FunctionDefinition <$> convertTelescope tele

    LambdaLifted.DataDefinition (Telescope.Empty (LambdaLifted.ConstructorDefinitions constrDefs)) ->
      ClosureConverted.DataDefinition . ClosureConverted.ConstructorDefinitions <$>
        mapM convertTerm constrDefs

    LambdaLifted.DataDefinition tele ->
      ClosureConverted.ParameterisedDataDefinition <$> convertParameterisedDataDefinition tele

convertParameterisedDataDefinition
  :: MonadFetch Query m
  => Telescope LambdaLifted.Type LambdaLifted.ConstructorDefinitions v
  -> m (Telescope ClosureConverted.Type ClosureConverted.ConstructorDefinitions v)
convertParameterisedDataDefinition tele =
  case tele of
    Telescope.Empty (LambdaLifted.ConstructorDefinitions constrDefs) ->
      Telescope.Empty . ClosureConverted.ConstructorDefinitions <$> mapM convertTerm constrDefs

    Telescope.Extend binding type_ plicity tele' ->
      Telescope.Extend binding <$>
        convertTerm type_ <*>
        pure plicity <*>
        convertParameterisedDataDefinition tele'

convertTerm
  :: MonadFetch Query m
  => LambdaLifted.Term v
  -> m (ClosureConverted.Term v)
convertTerm term =
  convertAppliedTerm term []

convertAppliedTerm
  :: MonadFetch Query m
  => LambdaLifted.Term v
  -> [ClosureConverted.Term v]
  -> m (ClosureConverted.Term v)
convertAppliedTerm term args =
  case term of
    LambdaLifted.Var var ->
      applyArgs args $
        pure $ ClosureConverted.Var var

    LambdaLifted.Global global ->
      convertGlobal global args

    LambdaLifted.Con con conParams conArgs ->
      ClosureConverted.Con con <$> mapM convertTerm conParams <*> mapM convertTerm conArgs

    LambdaLifted.Lit lit ->
      pure $ ClosureConverted.Lit lit

    LambdaLifted.Let binding term' type_ body ->
      applyArgs args $
        ClosureConverted.Let binding <$>
          convertTerm term' <*>
          convertTerm type_ <*>
          convertTerm body

    LambdaLifted.Pi binding domain target ->
      ClosureConverted.Pi binding <$>
        convertTerm domain <*>
        convertTerm target

    LambdaLifted.App fun arg -> do
      arg' <- convertTerm arg
      convertAppliedTerm fun $ arg' : args

    LambdaLifted.Case scrutinee branches defaultBranch ->
      applyArgs args $
        ClosureConverted.Case <$>
          convertTerm scrutinee <*>
          convertBranches branches <*>
          mapM convertTerm defaultBranch

convertGlobal
  :: MonadFetch Query m
  => Name.Lifted
  -> [ClosureConverted.Term v]
  -> m (ClosureConverted.Term v)
convertGlobal global args = do
  maybeDef <- fetch $ Query.LambdaLiftedDefinition global
  let
    nonFunctionCase =
      applyArgs args $ pure $ ClosureConverted.Global global

    functionCase tele =
      pure $
        case (Telescope.length tele, length args) of
          (arity, numArgs)
            | arity == numArgs ->
              ClosureConverted.Apply global args

            | arity < numArgs -> do
              let
                (preArgs, postArgs) =
                  splitAt arity args

              ClosureConverted.ApplyClosure
                (ClosureConverted.Apply global preArgs)
                postArgs

            | otherwise ->
              ClosureConverted.Closure global args

  case maybeDef of
    Just (LambdaLifted.TypeDeclaration _) ->
      nonFunctionCase

    Just (LambdaLifted.ConstantDefinition (Telescope.Empty _)) ->
      nonFunctionCase

    Just (LambdaLifted.DataDefinition (Telescope.Empty _)) ->
      nonFunctionCase

    Just (LambdaLifted.ConstantDefinition tele) ->
      functionCase tele

    Just (LambdaLifted.DataDefinition tele) ->
      functionCase tele

    Nothing ->
      nonFunctionCase

convertBranches
  :: MonadFetch Query m
  => LambdaLifted.Branches v
  -> m (ClosureConverted.Branches v)
convertBranches branches =
  case branches of
    LambdaLifted.ConstructorBranches constructorBranches ->
      ClosureConverted.ConstructorBranches <$>
        mapM convertTelescope constructorBranches

    LambdaLifted.LiteralBranches literalBranches ->
      ClosureConverted.LiteralBranches <$>
        mapM convertTerm literalBranches

convertTelescope
  :: MonadFetch Query m
  => Telescope LambdaLifted.Type LambdaLifted.Term v
  -> m (Telescope ClosureConverted.Type ClosureConverted.Term v)
convertTelescope tele =
  case tele of
    Telescope.Empty term ->
      Telescope.Empty <$> convertTerm term

    Telescope.Extend binding type_ plicity tele' ->
      Telescope.Extend binding <$>
        convertTerm type_ <*>
        pure plicity <*>
        convertTelescope tele'

applyArgs
  :: Monad m
  => [ClosureConverted.Term v]
  -> m (ClosureConverted.Term v)
  -> m (ClosureConverted.Term v)
applyArgs args mresult =
  case args of
    [] ->
      mresult

    _ -> do
      result <- mresult
      pure $ ClosureConverted.ApplyClosure result args