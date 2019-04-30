{-# language DeriveFunctor #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
module Elaboration where

import Protolude hiding (force, check, evaluate)

import qualified Builtin
import Context (Context)
import qualified Context
import qualified Domain
import qualified Evaluation
import Index
import Monad
import qualified Presyntax
import qualified Readback
import Readback (readback)
import qualified Syntax
import qualified Tsil

data Inferred term
  = Inferred term !(Lazy Domain.Type)
  deriving Functor

newtype Checked term
  = Checked term
  deriving Functor

data Expected f where
  Infer :: Expected Inferred
  Check :: Domain.Type -> Expected Checked

check
  :: Context v
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)
check context term typ = do
  Checked result <- elaborate context term $ Check typ
  pure result

infer
  :: Context v
  -> Presyntax.Term
  -> M (Inferred (Syntax.Term v))
infer context term =
  elaborate context term Infer

inferred
  :: Context v
  -> Expected e
  -> Syntax.Term v
  -> Lazy Domain.Type
  -> M (e (Syntax.Term v))
inferred context expected term typ =
  case expected of
    Infer ->
      pure $ Inferred term typ

    Check expectedType -> do
      typ' <- force typ
      unify (Context.toReadbackEnvironment context) typ' expectedType
      pure $ Checked term

elaborate
  :: Functor e
  => Context v
  -> Presyntax.Term
  -> Expected e
  -> M (e (Syntax.Term v))
elaborate context term expected =
  case term of
    Presyntax.Var name ->
      case Context.lookupName name context of
        Nothing -> do
          type_ <- typeOfGlobal name
          type' <- lazy $ evaluate context type_
          inferred
            context
            expected
            (Syntax.Global name)
            type'

        Just v ->
          inferred
            context
            expected
            (Syntax.Var v)
            (Context.lookupType v context)

    Presyntax.Let name term' body -> do
      Inferred term'' typ <- infer context term'
      typ' <- force typ
      typ'' <- Readback.readback (Context.toReadbackEnvironment context) typ'

      term''' <- lazy $ evaluate context term''
      context' <- Context.extendDef context name term''' typ

      body' <- elaborate context' body expected
      pure $ Syntax.Let name term'' typ'' . Scope <$> body'

    Presyntax.Pi name source domain -> do
      source' <- check context source Builtin.type_

      (context', _) <- Context.extend context name $ Lazy $ pure Builtin.type_

      domain' <- check context' domain Builtin.type_
      inferred
        context
        expected
        (Syntax.Pi name source' $ Scope domain')
        (Lazy $ pure Builtin.type_)

    Presyntax.Fun source domain -> do
      source' <- check context source Builtin.type_
      domain' <- check context domain Builtin.type_
      inferred
        context
        expected
        (Syntax.Fun source' domain')
        (Lazy $ pure Builtin.type_)

    Presyntax.Lam name body ->
      case expected of
        Infer -> do
          source <- Context.newMeta context
          source' <- evaluate context source
          source'' <- Readback.readback (Context.toReadbackEnvironment context) source'
          (context', _) <- Context.extend context name (Lazy $ pure source')
          Inferred body' domain <- infer context' body
          type_ <- lazy $ do
            domain' <- force domain
            domain'' <- readback (Context.toReadbackEnvironment context') domain'
            pure
              $ Domain.Pi name (Lazy $ pure source')
              $ Evaluation.makeClosure (Context.toEvaluationEnvironment context) (Scope domain'')

          pure $ Inferred (Syntax.Lam name source'' (Scope body')) type_

        Check (Domain.Pi _ source domainClosure) -> do
          source' <- force source
          source'' <- Readback.readback (Context.toReadbackEnvironment context) source'
          (context', var) <- Context.extend context name source

          domain <-
            Evaluation.evaluateClosure
              domainClosure
              (Lazy $ pure $ Domain.var var)
          body' <- check context' body domain
          pure $ Checked (Syntax.Lam name source'' (Scope body'))

        Check (Domain.Fun source domain) -> do
          source' <- force source
          source'' <- Readback.readback (Context.toReadbackEnvironment context) source'
          (context', _) <- Context.extend context name source

          domain' <- force domain
          body' <- check context' body domain'
          pure $ Checked (Syntax.Lam name source'' (Scope body'))

    Presyntax.App function argument -> do
      Inferred function' functionType <- infer context function
      functionType' <- force functionType

      case functionType' of
        Domain.Pi _ source domainClosure -> do
          source' <- force source
          argument' <- check context argument source'
          argument'' <- lazy $ evaluate context argument'
          domain <- lazy $ Evaluation.evaluateClosure domainClosure argument''
          inferred
            context
            expected
            (Syntax.App function' argument')
            domain

        Domain.Fun source domain -> do
          source' <- force source
          case expected of
            Check expectedType -> do
              unify (Context.toReadbackEnvironment context) expectedType functionType'
              argument' <- check context argument source'
              pure $ Checked (Syntax.App function' argument')

            Infer -> do
              argument' <- check context argument source'
              pure $ Inferred (Syntax.App function' argument') domain

evaluate
  :: Context v
  -> Syntax.Term v
  -> M Domain.Value
evaluate context =
  Evaluation.evaluate (Context.toEvaluationEnvironment context)

typeOfGlobal
  :: Text
  -> M (Syntax.Type v)
typeOfGlobal global =
  if global == "Type" then
    return $ Syntax.Global "Type"

  else
    undefined

unify :: Readback.Environment v -> Domain.Value -> Domain.Value -> M ()
unify env value1 value2 =
  case (value1, value2) of
    -- Same heads
    (Domain.Neutral head1 spine1, Domain.Neutral head2 spine2)
      | head1 == head2 ->
        Tsil.zipWithM_ (unifyForce env) spine1 spine2

    (Domain.Lam _ _ closure1, Domain.Lam _ _ closure2) -> do
      (env', var) <- Readback.extend env
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 lazyVar
      body2 <- Evaluation.evaluateClosure closure2 lazyVar
      unify env' body1 body2

    (Domain.Pi _ source1 domainClosure1, Domain.Pi _ source2 domainClosure2) -> do
      unifyForce env source2 source1

      (env', var) <- Readback.extend env
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1 <- Evaluation.evaluateClosure domainClosure1 lazyVar
      domain2 <- Evaluation.evaluateClosure domainClosure2 lazyVar
      unify env' domain1 domain2

    (Domain.Pi _ source1 domainClosure1, Domain.Fun source2 domain2) -> do
      unifyForce env source2 source1

      (env', var) <- Readback.extend env
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1 <- Evaluation.evaluateClosure domainClosure1 lazyVar
      domain2' <- force domain2
      unify env' domain1 domain2'

    (Domain.Fun source1 domain1, Domain.Pi _ source2 domainClosure2) -> do
      unifyForce env source2 source1

      (env', var) <- Readback.extend env
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1' <- force domain1
      domain2 <- Evaluation.evaluateClosure domainClosure2 lazyVar
      unify env' domain1' domain2

    (Domain.Fun source1 domain1, Domain.Fun source2 domain2) -> do
      unifyForce env source2 source1
      unifyForce env domain1 domain2

    -- Eta expand
    (Domain.Lam _ _ closure1, v2) -> do
      (env', var) <- Readback.extend env
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 lazyVar
      body2 <- Evaluation.apply v2 lazyVar

      unify env' body1 body2

    (v1, Domain.Lam _ _ closure2) -> do
      (env', var) <- Readback.extend env
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- Evaluation.apply v1 lazyVar
      body2 <- Evaluation.evaluateClosure closure2 lazyVar

      unify env' body1 body2

    _ ->
      panic "Can't unify"
  where
    unifyForce sz lazyValue1 lazyValue2 = do
      v1 <- force lazyValue1
      v2 <- force lazyValue2
      unify sz v1 v2
