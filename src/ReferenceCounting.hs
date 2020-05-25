{-# language OverloadedStrings #-}
{-# language TupleSections #-}
module ReferenceCounting where

import Protolude hiding (Type, IntMap, IntSet, evaluate)

import qualified Binding
import qualified Applicative.Syntax as Syntax
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List (partition)
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

data InnerValue
  = OperandValue !InnerOperand
  | Con !Name.QualifiedConstructor [Operand] [Operand]
  | Let !Name !Var !Value !TypeOperand !Value
  | Function [(Name, Var, Type)] !Type
  | Apply !Name.Lifted [Operand]
  | Pi !Name !Var !Type !Type
  | Closure !Name.Lifted [Operand]
  | ApplyClosure !Operand [Operand]
  | Case !Operand !Branches !(Maybe Value)
  deriving Show

data Value = Value !InnerValue (IntSet Var)
  deriving Show

type Type = Value

data InnerOperand
  = Var !Var
  | Global !Name.Lifted
  | Lit !Literal
  deriving Show

data Operand = Operand !InnerOperand (IntSet Var)
  deriving Show

type TypeOperand = Operand

data Branches
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor ([(Name, Var, Type)], Value))
  | LiteralBranches (OrderedHashMap Literal Value)
  deriving Show

type Occurrences = IntSet Var

type Environment = Environment.Environment Value

extend :: Environment v -> Type -> M (Environment (Index.Succ v), Var)
extend env type_ =
  Environment.extendValue env type_

extendVar :: Environment v -> Var -> Type -> Environment (Index.Succ v)
extendVar env var type_ =
  Environment.extendVarValue env var type_

lookupVarType :: Var -> Environment v -> Type
lookupVarType var env =
  fromMaybe (panic "ReferenceCounting.lookupVarType") $
  Environment.lookupVarValue var env

-------------------------------------------------------------------------------

occurrences :: Value -> Occurrences
occurrences (Value _ occs) =
  occs

operandOccurrences :: Operand -> Occurrences
operandOccurrences (Operand _ occs) =
  occs

makeVar :: Environment v -> Var -> Operand
makeVar env var =
  Operand (Var var) $
    IntSet.singleton var <>
    foldMap occurrences (Environment.lookupVarValue var env)

makeGlobal :: Name.Lifted -> Operand
makeGlobal global =
  Operand (Global global) mempty

makeLit :: Literal -> Operand
makeLit lit =
  Operand (Lit lit) mempty

makeOperand :: Operand -> Value
makeOperand (Operand operand occs) =
  Value (OperandValue operand) occs

makeCon :: Name.QualifiedConstructor -> [Operand] -> [Operand] -> Value
makeCon con params args =
  Value (Con con params args) $ foldMap operandOccurrences params <> foldMap operandOccurrences args

makeLet :: Name -> Var -> Value -> TypeOperand -> Value -> Value
makeLet name var value type_ body =
  Value (Let name var value type_ body) $
    occurrences value <>
    operandOccurrences type_ <>
    IntSet.delete var (occurrences body)

makeFunction :: [(Name, Var, Type)] -> Type -> Type
makeFunction args target =
  Value (Function args target) mempty -- Since it's closed

makeApply :: Name.Lifted -> [Operand] -> Value
makeApply name args =
  Value (Apply name args) $
    foldMap operandOccurrences args

makePi :: Name -> Var -> Type -> Value -> Value
makePi name var domain target =
  Value (Pi name var domain target) $
    occurrences domain <>
    IntSet.delete var (occurrences target)

makeClosure :: Name.Lifted -> [Operand] -> Value
makeClosure name args =
  Value (Closure name args) $
    foldMap operandOccurrences args

makeApplyClosure :: Operand -> [Operand] -> Value
makeApplyClosure fun args =
  Value (ApplyClosure fun args) $
    operandOccurrences fun <>
    foldMap operandOccurrences args

makeCase :: Operand -> Branches -> Maybe Value -> Value
makeCase scrutinee branches defaultBranch =
  Value (Case scrutinee branches defaultBranch) $
    operandOccurrences scrutinee <>
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
    Syntax.Operand operand ->
      pure $ makeOperand $ evaluateOperand env operand

    Syntax.Con con params args ->
      pure $ makeCon con (evaluateOperand env <$> params) (evaluateOperand env <$> args)

    Syntax.Let name term' type_ body -> do
      let
        type' =
          evaluateOperand env type_
      term'' <- evaluate env term'
      (env', var) <- extend env $ makeOperand type'
      body' <- evaluate env' body
      pure $ makeLet name var term'' type' body'

    Syntax.Function tele ->
      uncurry makeFunction <$> evaluateTelescope (Environment.emptyFrom env) tele

    Syntax.Apply global args ->
      pure $ makeApply global $ evaluateOperand env <$> args

    Syntax.Pi name domain target -> do
      domain' <- evaluate env domain
      (env', var) <- extend env domain'
      makePi name var domain' <$> evaluate env' target

    Syntax.Closure global args ->
      pure $ makeClosure global $ evaluateOperand env <$> args

    Syntax.ApplyClosure term' args ->
      pure $ makeApplyClosure (evaluateOperand env term') $ evaluateOperand env <$> args

    Syntax.Case scrutinee branches defaultBranch ->
      makeCase
        (evaluateOperand env scrutinee) <$>
        evaluateBranches env branches <*>
        mapM (evaluate env) defaultBranch

evaluateOperand :: Environment v -> Syntax.Operand v -> Operand
evaluateOperand env operand = 
  case operand of
    Syntax.Var index ->
      makeVar env $ Environment.lookupIndexVar index env

    Syntax.Global global ->
      makeGlobal global

    Syntax.Lit lit ->
      makeLit lit

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
  :: Environment v
  -> IntSet Var
  -> Value
  -> M Value
insertOperations env ownedVars value@(Value innerValue occs) =
  decreaseVars env predecreaseVars =<<
    case innerValue of
      OperandValue operand ->
        case operand of
          Var var
            | IntSet.member var ownedVars' ->
              pure value

            | otherwise ->
              increaseOperand env (Operand operand occs) value

          Global _ ->
            increaseOperand env (Operand operand occs) value

          Lit lit ->
            pure value

      Con con params args -> do
        let
          go (Var var) = (mempty, [var])
          go (Global glob) = ([glob], mempty)
          go (Lit _) = mempty
          (argGlobals, argVars) = foldMap (\(Operand op _) -> go op) args
          argVarDiffs = IntMap.fromListWith (+) $ (, 1 :: Int) <$> argVars
          ownedDiffs = IntMap.fromSet (const (-1)) ownedVars'
          varDiffs = IntMap.toList $ IntMap.unionWith (+) argVarDiffs ownedDiffs
          (varIncs, varDecs) = partition ((>= 0) . snd) varDiffs
          incVars =
            [ var'
            | (var, numOccs) <- varIncs
            , var' <- replicate numOccs var
            ]
          decVars =
            [ var'
            | (var, negatedOccs) <- varDecs
            , var' <- replicate (0 - negatedOccs) var
            ]

        postDecreaseVars env decVars =<<
          increaseVars env incVars =<<
          increaseGlobals argGlobals value

      Let name var value' type_ body ->
        undefined

      Function domains target ->
        pure $ makeFunction domains target

      Apply global args ->
        postDecreaseVars env (IntSet.toList ownedVars) value

      Pi name var domain target ->
        postDecreaseVars env (IntSet.toList ownedVars) value

      Closure global args ->
        undefined

      ApplyClosure fun args ->
        postDecreaseVars env (IntSet.toList ownedVars) value

      Case scrutinee branches defaultBranch ->
        undefined
  where
    predecreaseVars =
      IntSet.difference ownedVars occs

    ownedVars' =
      IntSet.intersection ownedVars occs

decreaseVars :: Environment v -> IntSet Var -> Value -> M Value
decreaseVars ownedVars value
  | IntSet.null ownedVars =
    pure value

  | otherwise = do
    var <- freshVar
    pure $
      makeLet "result" var value _
      foldM decreaseVar value makeVar <$> IntSet.toList ownedVars

postDecreaseVars :: Environment v -> [Var] -> Value -> M Value
postDecreaseVars env vars value
  | IntSet.null ownedVars =
    pure value

  | otherwise = do
    var <- freshVar
    pure $
      makeLet "result" var value _
      foldM decrease value $ makeVar <$> IntSet.toList ownedVars

increaseOperand :: Environment v -> Operand -> Value -> M Value
increaseOperand = undefined

increaseVar
  :: Environment v
  -> Var
  -> Value
  -> M Value
increaseVar env var k = do
  incVar <- freshVar
  pure $
    makeLet
      "inc"
      incVar
      (makeApply
        (Name.Lifted "Sixten.Builtin.increaseReferenceCount" 0)
        [lookupVarType var env, makeVar env var]
      )
      (makeGlobal $ Name.Lifted "Sixten.Builtin.Unit" 0)
      k

increaseVars :: Environment v -> [Var] -> Value -> M Value
increaseVars env vars k =
  foldrM (increaseVar env) k vars

increaseGlobal :: Name.Lifted -> Value -> M Value
increaseGlobal = undefined

increaseGlobals :: [Name.Lifted] -> Value -> M Value
increaseGlobals globals k =
  foldrM increaseGlobal k globals
