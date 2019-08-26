{-# language OverloadedStrings #-}
module Evaluation where

import Protolude hiding (Seq, force, evaluate)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Rock

import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Domain.Telescope as Domain (Telescope)
import qualified Domain.Telescope
import qualified Environment
import Monad
import qualified Name
import Plicity
import qualified Query
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

evaluateConstructorDefinitions
  :: Domain.Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> M (Domain.Telescope Domain.Type (HashMap Name.Constructor Domain.Type))
evaluateConstructorDefinitions env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrs) -> do
      constrs' <- forM constrs $ evaluate env
      pure $ Domain.Telescope.Empty constrs'

    Telescope.Extend name source plicity domain -> do
      source' <- evaluate env source
      pure $ Domain.Telescope.Extend name source' plicity $ \param -> do
        env' <- Environment.extendValue env param
        evaluateConstructorDefinitions env' domain

evaluate :: Domain.Environment v -> Syntax.Term v -> M Domain.Value
evaluate env term =
  case term of
    Syntax.Var index -> do
      let
        var =
          Environment.lookupIndexVar index env

      pure $
        Domain.Glued (Domain.Var var) mempty $
        eager $ fromMaybe (Domain.var var) $ Environment.lookupVarValue var env

    Syntax.Global name -> do
      definitionVisible <- fetch $ Query.IsDefinitionVisible (Environment.scopeKey env) name
      if definitionVisible then do
        maybeDefinition <- fetch $ Query.ElaboratedDefinition name
        case maybeDefinition of
          Just (Syntax.ConstantDefinition term', _) -> do
            value <- lazy $ evaluate (Environment.empty $ Environment.scopeKey env) term'
            pure $ Domain.Glued (Domain.Global name) mempty value

          _ ->
            pure $ Domain.global name

      else
        pure $ Domain.global name

    Syntax.Con c ->
      pure $ Domain.con c

    Syntax.Meta i ->
      pure $ Domain.meta i

    Syntax.Let _ t _ s -> do
      t' <- evaluate env t
      env' <- Environment.extendValue env t'
      evaluate env' s

    Syntax.Pi n t p s -> do
      t' <- evaluate env t
      pure $ Domain.Pi n t' p (Domain.Closure env s)

    Syntax.Fun t1 t2 -> do
      t1' <- evaluate env t1
      t2' <- evaluate env t2
      pure $ Domain.Fun t1' t2'

    Syntax.Lam n t p s -> do
      t' <- evaluate env t
      pure $ Domain.Lam n t' p (Domain.Closure env s)

    Syntax.App t1 p t2 -> do
      t1' <- evaluate env t1
      t2' <- evaluate env t2
      apply t1' p t2'

    Syntax.Case scrutinee branches defaultBranch -> do
      scrutineeValue <- evaluate env scrutinee
      case scrutineeValue of
        Domain.Neutral (Domain.Con constr) spine ->
          chooseBranch env constr (toList spine) branches defaultBranch

        _ ->
          pure $
            Domain.Case
              scrutineeValue
              (Domain.Branches env branches defaultBranch)

chooseBranch
  :: Domain.Environment v
  -> Name.QualifiedConstructor
  -> [(Plicity, Domain.Value)]
  -> Syntax.Branches v
  -> Maybe (Syntax.Term v)
  -> M Domain.Value
chooseBranch outerEnv constr outerArgs branches defaultBranch =
  case (HashMap.lookup constr branches, defaultBranch) of
    (Nothing, Nothing) ->
      panic "chooseBranch no branches"

    (Nothing, Just branch) ->
      evaluate outerEnv branch

    (Just tele, _) ->
      go outerEnv outerArgs tele
  where
    go
      :: Domain.Environment v
      -> [(Plicity, Domain.Value)]
      -> Telescope Syntax.Type Syntax.Term v
      -> M Domain.Value
    go env args tele =
      case (args, tele) of
        ([], Telescope.Empty branch) ->
          evaluate env branch

        ((plicity1, arg):args', Telescope.Extend _ _ plicity2 domain)
          | plicity1 == plicity2 -> do
            env' <- Environment.extendValue env arg
            go env' args' domain

        _ ->
          panic "chooseBranch mismatch"

apply :: Domain.Value -> Plicity -> Domain.Value -> M Domain.Value
apply fun plicity arg =
  case fun of
    Domain.Lam _ _  plicity' closure
      | plicity == plicity' ->
      evaluateClosure closure arg

    Domain.Neutral hd args ->
      pure $ Domain.Neutral hd (args Tsil.:> (plicity, arg))

    Domain.Glued hd args value -> do
      appliedValue <- lazy $ do
        value' <- force value
        apply value' plicity arg
      pure $ Domain.Glued hd (args Tsil.:> (plicity, arg)) appliedValue

    _ ->
      panic "applying non-function"

applySpine :: Domain.Value -> Domain.Spine -> M Domain.Value
applySpine = foldM (\val (plicity, arg) -> apply val plicity arg)

evaluateClosure :: Domain.Closure -> Domain.Value -> M Domain.Value
evaluateClosure (Domain.Closure env body) argument = do
  env' <- Environment.extendValue env argument
  evaluate env' body
