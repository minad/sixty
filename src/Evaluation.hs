{-# language OverloadedStrings #-}
module Evaluation where

import Protolude hiding (force)

import qualified Bound.Scope.Simple as Bound

import qualified Domain
import Monad
import qualified Syntax
import Index
import qualified Tsil

eval :: Syntax.Env (Lazy Domain.Value) v -> Syntax.Term v -> M Domain.Value
eval env term =
  case term of
    Syntax.Var v ->
      force $ Syntax.lookupValue env v

    Syntax.Global g ->
      pure $ Domain.global g -- TODO

    Syntax.Let t (Bound.Scope s) -> do
      t' <- lazy $ eval env t
      eval (Syntax.Snoc env t') s

    Syntax.Pi t s -> do
      t' <- lazy $ eval env t
      pure $ Domain.Pi t' (Domain.Closure env s)

    Syntax.Fun t1 t2 -> do
      t1' <- lazy $ eval env t1
      t2' <- lazy $ eval env t2
      pure $ Domain.Fun t1' t2'

    Syntax.Lam s ->
      pure $ Domain.Lam (Domain.Closure env s)

    Syntax.App t1 t2 -> do
      t1' <- eval env t1
      t2' <- lazy $ eval env t2
      apply t1' t2'

apply :: Domain.Value -> Lazy Domain.Value -> M Domain.Value
apply fun arg =
  case fun of
    Domain.Lam closure ->
      evalClosure closure arg

    Domain.Neutral hd args ->
      pure $ Domain.Neutral hd (Tsil.Snoc args arg)

    _ ->
      panic "applying non-function"

evalClosure :: Domain.Closure -> Lazy Domain.Value -> M Domain.Value
evalClosure (Domain.Closure env (Bound.Scope body)) x =
  eval (Syntax.Snoc env x) body

readBack :: Domain.EnvSize v -> Domain.Value -> M (Syntax.Term v)
readBack size value =
  case value of
    Domain.Neutral hd spine ->
      readBackNeutral size hd spine

    Domain.Lam closure ->
      Syntax.Lam <$> readBackClosure size closure

    Domain.Pi typ closure -> do
      typ' <- force typ
      Syntax.Pi <$> readBack size typ' <*> readBackClosure size closure

    Domain.Fun source domain -> do
      source' <- force source
      domain' <- force domain
      Syntax.Fun <$> readBack size source' <*> readBack size domain'

readBackClosure :: Domain.EnvSize v -> Domain.Closure -> M (Bound.Scope () Syntax.Term v)
readBackClosure size closure = do
  let
    (size', v) =
      Domain.extendEnvSize size

  closure' <- evalClosure closure $ Lazy $ pure $ Domain.var v
  Bound.Scope <$> readBack size' closure'

readBackNeutral :: Domain.EnvSize v -> Domain.Head -> Domain.Spine -> M (Syntax.Term v)
readBackNeutral size hd spine =
  case spine of
    Tsil.Nil ->
      pure $ readBackHead size hd

    Tsil.Snoc spine' arg -> do
      arg' <- force arg
      Syntax.App <$> readBackNeutral size hd spine' <*> readBack size arg'

readBackHead :: Domain.EnvSize v -> Domain.Head -> Syntax.Term v
readBackHead size hd =
  case hd of
    Domain.Var v ->
      Syntax.Var $ Index.fromLevel v size

    Domain.Global g ->
      Syntax.Global g
