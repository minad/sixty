{-# language OverloadedStrings #-}
module ReferenceCounting where

import Protolude hiding (Type, IntSet, evaluate)

import qualified Binding
import qualified ClosureConverted.Syntax as Syntax
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Environment
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Index
import Literal (Literal)
import Monad
import Name (Name)
import qualified Name
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import qualified Var
import Var (Var)

data Value = Value !InnerValue Occurrences
  deriving Show

data InnerValue
  = Var !Var
  | Global !Name.Lifted
  | Con !Name.QualifiedConstructor [Value] [Value]
  | Lit !Literal
  | Let !Name !Var !Value !Type !Value
  | Function [(Name, Var, Type)] !Type
  | Apply !Name.Lifted [Value]
  | Pi !Name !Var !Type !Type
  | Closure !Name.Lifted [Value]
  | ApplyClosure !Value [Value]
  | Case !Value !Branches !(Maybe Value)
  deriving Show

type Type = Value

data Branches
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor ([(Name, Var, Type)], Value))
  | LiteralBranches (OrderedHashMap Literal Value)
  deriving Show

type Occurrences = IntSet Var

type Environment = Environment.Environment Value

extend :: Environment v -> Type -> M (Environment (Index.Succ v), Var)
extend env type_ =
  Environment.extendValue env type_

-------------------------------------------------------------------------------

occurrences :: Value -> Occurrences
occurrences (Value _ occs) =
  occs

makeVar :: Environment v -> Var -> Value
makeVar env var =
  Value (Var var) $
    IntSet.singleton var <>
    foldMap occurrences (Environment.lookupVarValue var env)

makeGlobal :: Name.Lifted -> Value
makeGlobal global =
  Value (Global global) mempty

makeCon :: Name.QualifiedConstructor -> [Value] -> [Value] -> Value
makeCon con params args =
  Value (Con con params args) $ foldMap occurrences params <> foldMap occurrences args

makeLit :: Literal -> Value
makeLit lit =
  Value (Lit lit) mempty

makeLet :: Name -> Var -> Value -> Type -> Value -> Value
makeLet name var value type_ body =
  Value (Let name var value type_ body) $
    occurrences value <>
    occurrences type_ <>
    IntSet.delete var (occurrences body)

makeFunction :: [(Name, Var, Type)] -> Type -> Type
makeFunction args target =
  Value (Function args target) mempty -- Since it's closed

makeApply :: Name.Lifted -> [Value] -> Value
makeApply name args =
  Value (Apply name args) $
    foldMap occurrences args

makePi :: Name -> Var -> Type -> Value -> Value
makePi name var domain target =
  Value (Pi name var domain target) $
    occurrences domain <>
    IntSet.delete var (occurrences target)

makeClosure :: Name.Lifted -> [Value] -> Value
makeClosure name args =
  Value (Closure name args) $
    foldMap occurrences args

makeApplyClosure :: Value -> [Value] -> Value
makeApplyClosure fun args =
  Value (ApplyClosure fun args) $
    foldMap occurrences args

makeCase :: Value -> Branches -> Maybe Value -> Value
makeCase scrutinee branches defaultBranch =
  Value (Case scrutinee branches defaultBranch) $
    occurrences scrutinee <>
    branchOccurrences branches <>
    foldMap occurrences defaultBranch

branchOccurrences :: Branches -> Occurrences
branchOccurrences branches =
  case branches of
    ConstructorBranches _constructorTypeName constructorBranches ->
      foldMap (uncurry telescopeOccurrences) constructorBranches

    LiteralBranches literalBranches ->
      foldMap occurrences literalBranches

telescopeOccurrences :: [(Name, Var, Type)] -> Value -> Occurrences
telescopeOccurrences tele body =
  case tele of
    [] ->
      occurrences body

    (_, var, type_):tele' ->
      occurrences type_ <>
      IntSet.delete var (telescopeOccurrences tele' body)

-------------------------------------------------------------------------------

evaluate :: Environment v -> Syntax.Term v -> M Value
evaluate env term =
  case term of
    Syntax.Var index ->
      pure $ makeVar env $ Environment.lookupIndexVar index env

    Syntax.Global global ->
      pure $ makeGlobal global

    Syntax.Con con params args ->
      makeCon con <$> mapM (evaluate env) params <*> mapM (evaluate env) args

    Syntax.Lit lit ->
      pure $ makeLit lit

    Syntax.Let name term' type_ body -> do
      term'' <- evaluate env term'
      type' <- evaluate env type_
      (env', var) <- extend env type'
      body' <- evaluate env' body
      pure $ makeLet name var term'' type' body'

    Syntax.Function tele ->
      uncurry makeFunction <$> evaluateTelescope (Environment.empty $ Environment.scopeKey env) tele

    Syntax.Apply global args ->
      makeApply global <$> mapM (evaluate env) args

    Syntax.Pi name domain target -> do
      domain' <- evaluate env domain
      (env', var) <- extend env domain'
      makePi name var domain' <$> evaluate env' target

    Syntax.Closure global args ->
      makeClosure global <$> mapM (evaluate env) args

    Syntax.ApplyClosure term' args ->
      makeApplyClosure <$> evaluate env term' <*> mapM (evaluate env) args

    Syntax.Case scrutinee branches defaultBranch ->
      makeCase <$>
        evaluate env scrutinee <*>
        evaluateBranches env branches <*>
        mapM (\branch -> evaluate env branch) defaultBranch

evaluateBranches
  :: Environment v
  -> Syntax.Branches v
  -> M Branches
evaluateBranches env branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      ConstructorBranches constructorTypeName <$> OrderedHashMap.mapMUnordered (evaluateTelescope env) constructorBranches

    Syntax.LiteralBranches literalBranches ->
      LiteralBranches <$> OrderedHashMap.mapMUnordered (evaluate env) literalBranches

evaluateTelescope
  :: Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> M ([(Name, Var, Type)], Value)
evaluateTelescope env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate env body
      pure ([], body')

    Telescope.Extend binding type_ _plicity tele' -> do
      type' <- evaluate env type_
      (env', var) <- extend env type'
      (names, body) <- evaluateTelescope env' tele'
      pure ((Binding.toName binding, var, type'):names, body)

-------------------------------------------------------------------------------

-- Insertion of reference count updates
--
-- * The caller of a function promises that the arguments are kept
-- alive during the call.
--
-- * Values are returned with an increased ref count.

insertOperations
  :: IntSet Var
  -> Value
  -> M Value
insertOperations varsToDecrease value@(Value innerValue _) =
  case innerValue of
    Var _ ->
      decreaseVars varsToDecrease $
        increase value value

    Global _ ->
      increase value value

    Con con args ->
      makeCon con <$> mapM (insertOperations mempty) args

    Lit lit ->
      pure $ makeLit lit

    Let name var value' type_ body ->
      makeLet name var <$>
        insertOperations mempty value' <*>
        insertOperations mempty type_ <*>
        insertOperations (IntSet.insert var varsToDecrease) body

    Function domains target ->
      pure $ makeFunction domains target

    Apply global args ->
      undefined

    Pi name var domain target ->
      pure $ makePi name var domain target

    Closure global args ->
      makeClosure global <$> mapM (insertOperations mempty) args

    ApplyClosure fun args ->
      undefined

    Case scrutinee branches defaultBranch ->
      undefined

decrease
  :: Value
  -> Value
  -> M Value
decrease valueToDecrease k = do
  var <- freshVar
  pure $
    makeLet
      "dec"
      var
      (makeApply
        (Name.Lifted "Sixten.Builtin.decreaseReferenceCount" 0)
        [valueToDecrease]
      )
      (makeGlobal $ Name.Lifted "Sixten.Builtin.Unit" 0)
      k

decreaseVars :: IntSet Var -> M Value -> M Value
decreaseVars varsToDecrease mvalue
  | IntSet.null varsToDecrease =
    mvalue

  | otherwise = do
    value <- mvalue
    var <- freshVar
    pure $
      makeLet "result" var value _ 
      foldM decrease value $ makeVar <$> IntSet.toList varsToDecrease

increase
  :: Value
  -> Value
  -> M Value
increase valueToDecrease k = do
  var <- freshVar
  pure $
    makeLet
      "inc"
      var
      (makeApply
        (Name.Lifted "Sixten.Builtin.increaseReferenceCount" 0)
        [valueToDecrease]
      )
      (makeGlobal $ Name.Lifted "Sixten.Builtin.Unit" 0)
      k
