{-# language OverloadedStrings #-}
module TypeOf where

import Protolude

import Rock

import qualified Binding
import qualified Builtin
import Context (Context)
import qualified Context
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Tsil (Tsil)
import qualified Domain
import qualified Elaboration
import qualified Environment
import qualified Evaluation
import qualified Meta
import Monad
import Plicity
import qualified Query
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

typeOf :: Context v -> Domain.Value -> M Domain.Type
typeOf context value =
  case value of
    Domain.Neutral hd spine -> do
      headType <- typeOfHead context hd
      typeOfSpineApplication context headType spine

    Domain.Lit lit ->
      pure $ Elaboration.inferLiteral lit

    Domain.Con constr args -> do
      tele <- fetch $ Query.ConstructorType constr
      let
        type_ =
          Telescope.fold Syntax.Pi tele
      constrType <- Evaluation.evaluate (Environment.empty $ Context.scopeKey context) type_
      typeOfApplications context constrType args

    Domain.Glued hd spine _ ->
      typeOf context $ Domain.Neutral hd spine

    Domain.Lam name type_ plicity closure -> do
      (context', var) <- Context.extend context name type_
      body <- Evaluation.evaluateClosure closure (Domain.var var)
      bodyType <- typeOf context' body
      bodyType' <- Elaboration.readback context' bodyType
      pure $
        Domain.Pi name type_ plicity $
        Domain.Closure (Context.toEnvironment context) bodyType'

    Domain.Pi {} ->
      pure Builtin.Type

    Domain.Fun {} ->
      pure Builtin.Type

typeOfHead :: Context v -> Domain.Head -> M Domain.Type
typeOfHead context hd =
  case hd of
    Domain.Var var ->
      pure $ Context.lookupVarType var context

    Domain.Global global -> do
      type_ <- fetch $ Query.ElaboratedType global
      Evaluation.evaluate (Environment.empty $ Context.scopeKey context) type_

    Domain.Meta index -> do
      solution <- Context.lookupMeta index context
      let
        type_ =
          case solution of
            Meta.Unsolved type' _ ->
              type'

            Meta.Solved _ type' ->
              type'

      Evaluation.evaluate (Environment.empty $ Context.scopeKey context) type_

typeOfElimination :: Context v -> Domain.Type -> Domain.Elimination -> M Domain.Type
typeOfElimination context type_ elimination =
  case elimination of
    Domain.Apps args -> do
      typeOfApplications context type_ args

    Domain.Case (Domain.Branches env branches defaultBranch) ->
      case defaultBranch of
        Just term -> do
          value' <- Evaluation.evaluate env term
          typeOf context value'

        Nothing ->
          case branches of
            Syntax.ConstructorBranches _ constructorBranches ->
              case OrderedHashMap.elems constructorBranches of
                (_, branchTele):_ ->
                  typeOfTelescope context env branchTele

                [] ->
                  panic "TODO type of branchless case"

            Syntax.LiteralBranches literalBranches ->
              case OrderedHashMap.elems literalBranches of
                (_, body):_ -> do
                  body' <- Evaluation.evaluate env body
                  typeOf context body'

                [] ->
                  panic "TODO type of branchless case"

typeOfSpineApplication :: Context v -> Domain.Type -> Domain.Spine -> M Domain.Type
typeOfSpineApplication context type_ (Domain.Spine eliminations) =
  foldlM (typeOfElimination context) type_ eliminations

typeOfApplication :: Context v -> Domain.Type -> Plicity -> Domain.Value -> M Domain.Type
typeOfApplication context type_ plicity arg = do
  type' <- Context.forceHead context type_
  case type' of
    Domain.Fun _ plicity' target
      | plicity == plicity' ->
        pure target

    Domain.Pi _ _ plicity' targetClosure
      | plicity == plicity' ->
        Evaluation.evaluateClosure targetClosure arg

    _ ->
      panic "typeOfApplication: type or plicity mismatch"

typeOfApplications :: Context v -> Domain.Type -> Tsil (Plicity, Domain.Value) -> M Domain.Type
typeOfApplications context type_ =
  foldlM (\type' -> uncurry $ typeOfApplication context type') type_

typeOfTelescope
  :: Context v'
  -> Domain.Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> M Domain.Type
typeOfTelescope context env tele =
  case tele of
    Telescope.Empty branch -> do
      branch' <- Evaluation.evaluate env branch
      typeOf context branch'

    Telescope.Extend binding type_ _ tele' -> do
      type' <- Evaluation.evaluate env type_
      (context', var) <- Context.extend context (Binding.toName binding) type'
      typeOfTelescope context' (Environment.extendVar env var) tele'
