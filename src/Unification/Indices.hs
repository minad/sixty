{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
{-# language OverloadedStrings #-}
module Unification.Indices where

import Protolude hiding (force, IntSet)

import Control.Monad.Trans

import Context (Context)
import qualified Context
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Tsil as Tsil
import qualified Domain
import Evaluation
import Index
import qualified Index.Map
import Monad
import Plicity
import Var

data Result a
  = Nope
  | Dunno
  | Yup a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

newtype ResultT m a = ResultT { runResultT :: m (Result a) }
  deriving (Functor, Foldable, Traversable)

nope :: Applicative m => ResultT m a
nope = ResultT $ pure Nope

dunno :: Applicative m => ResultT m a
dunno = ResultT $ pure Dunno

instance Monad m => Applicative (ResultT m) where
  pure =
    ResultT . pure . Yup

  (<*>) =
    ap

instance Monad m => Monad (ResultT m) where
  ResultT m >>= f =
    ResultT $ do
      res <- m
      case res of
        Nope ->
          pure Nope

        Dunno ->
          pure Dunno

        Yup a ->
          runResultT $ f a

instance MonadTrans ResultT where
  lift =
    ResultT . fmap Yup

unify
  :: Context v
  -> IntSet Var
  -> Domain.Value
  -> Domain.Value
  -> ResultT M (Context v)
unify context untouchables value1 value2 = do
  value1' <- lift $ Context.forceHead context value1
  value2' <- lift $ Context.forceHead context value2
  case (value1', value2') of
    (Domain.Neutral head1 spine1, Domain.Neutral head2 spine2)
      | head1 == head2 ->
        foldM
          (\context' -> uncurry (unifyForce context' untouchables `on` snd))
          context
          (Tsil.zip spine1 spine2)

    (Domain.Neutral (Domain.Con con1) _, Domain.Neutral (Domain.Con con2) _)
      | con1 /= con2 ->
        nope

    (Domain.Lam name1 type1 plicity1 closure1, Domain.Lam _ type2 plicity2 closure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 type1 closure1 type2 closure2

    (Domain.Pi name1 source1 plicity1 domainClosure1, Domain.Pi _ source2 plicity2 domainClosure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 source1 domainClosure1 source2 domainClosure2

    (Domain.Pi name1 source1 Explicit domainClosure1, Domain.Fun source2 domain2) -> do
      context1 <- unifyForce context untouchables source2 source1

      (context2, var) <- lift $ Context.extendUnnamed context1 name1 source1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1 <- lift $ Evaluation.evaluateClosure domainClosure1 lazyVar
      domain2' <- lift $ force domain2
      context3 <- unify context2 (IntSet.insert var untouchables) domain1 domain2'
      pure $ unextend context3

    (Domain.Fun source1 domain1, Domain.Pi name2 source2 Explicit domainClosure2) -> do
      context1 <- unifyForce context untouchables source2 source1

      (context2, var) <- lift $ Context.extendUnnamed context1 name2 source2
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1' <- lift $ force domain1
      domain2 <- lift $ Evaluation.evaluateClosure domainClosure2 lazyVar
      context3 <- unify context2 (IntSet.insert var untouchables) domain1' domain2
      pure $ unextend context3

    (Domain.Fun source1 domain1, Domain.Fun source2 domain2) -> do
      context1 <- unifyForce context untouchables source2 source1
      unifyForce context1 untouchables domain1 domain2

    -- Eta expand
    (Domain.Lam name1 type1 plicity1 closure1, v2) -> do
      (context1, var) <- lift $ Context.extendUnnamed context name1 type1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- lift $ Evaluation.evaluateClosure closure1 lazyVar
      body2 <- lift $ Evaluation.apply v2 plicity1 lazyVar

      context2 <- unify context1 (IntSet.insert var untouchables) body1 body2
      pure $ unextend context2

    (v1, Domain.Lam name2 type2 plicity2 closure2) -> do
      (context1, var) <- lift $ Context.extendUnnamed context name2 type2
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- lift $ Evaluation.apply v1 plicity2 lazyVar
      body2 <- lift $ Evaluation.evaluateClosure closure2 lazyVar

      context2 <- unify context1 (IntSet.insert var untouchables) body1 body2
      pure $ unextend context2

    -- Vars
    (Domain.Neutral (Domain.Var var1) Tsil.Empty, _) ->
      solve var1 value2'

    (_, Domain.Neutral (Domain.Var var2) Tsil.Empty) ->
      solve var2 value1'

    _ ->
      dunno

  where
    unifyForce context' untouchables' lazyValue1 lazyValue2 = do
      v1 <- lift $ force lazyValue1
      v2 <- lift $ force lazyValue2
      unify context' untouchables' v1 v2

    unifyAbstraction name type1 closure1 type2 closure2 = do
      context1 <- unifyForce context untouchables type1 type2

      (context2, var) <- lift $ Context.extendUnnamed context1 name type1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- lift $ Evaluation.evaluateClosure closure1 lazyVar
      body2 <- lift $ Evaluation.evaluateClosure closure2 lazyVar
      context3 <- unify context2 (IntSet.insert var untouchables) body1 body2
      pure $ unextend context3

    unextend :: Context (Succ v) -> Context v
    unextend context' =
      case Context.indices context' of
        indices Index.Map.:> _ ->
          context' { Context.indices = indices }

        _ ->
          panic "Unification.Indices.unify.unextend"

    solve var value
      | IntSet.member var untouchables =
        dunno

      | otherwise = do
        Any occs <- lift $ occurs context (IntSet.insert var untouchables) value
        if occs then
          dunno

        else
          pure $ Context.define context var $ Lazy $ pure value

occurs :: Context v -> IntSet Var -> Domain.Value -> M Any
occurs context untouchables value = do
  value' <- Context.forceHead context value
  case value' of
    Domain.Neutral (Domain.Var var) _
      | IntSet.member var untouchables ->
        pure $ Any True

    Domain.Glued _ _ value'' -> do
      value''' <- force value''
      occurs context untouchables value'''

    Domain.Neutral _ spine -> do
      results <- traverse (occursForce . snd) spine
      pure $ fold results

    Domain.Lam name type_ _ closure ->
      occursAbstraction name type_ closure

    Domain.Pi name source _ domainClosure ->
      occursAbstraction name source domainClosure

    Domain.Fun source domain -> do
      sourceResult <- occursForce source
      domainResult <- occursForce domain
      pure $ sourceResult <> domainResult

    Domain.Case _ _ ->
      -- TODO actually implement this
      pure $ Any True

  where
    occursForce lazyValue = do
      value' <- force lazyValue
      occurs context untouchables value'

    occursAbstraction name type_ closure = do
      typeResult <- occursForce type_
      (context', var) <- Context.extendUnnamed context name type_
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body <- Evaluation.evaluateClosure closure lazyVar
      bodyResult <- occurs context' untouchables body
      pure $ typeResult <> bodyResult
