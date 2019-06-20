{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Protolude hiding (force)

import qualified Data.HashSet as HashSet
import Data.String
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Rock

import qualified Driver
import qualified Error
import qualified Name
import qualified Pretty
import qualified Query

main :: IO ()
main = do
  [inputModule] <- getArgs
  parseAndTypeCheck (fromString inputModule)

parseAndTypeCheck :: Name.Module -> IO ()
parseAndTypeCheck module_ = do
  ((), errs) <- Driver.runTask $ do
    defs <- fetch $ Query.ParsedModule module_
    let
      names =
        HashSet.fromList $
          Name.Qualified module_ . fst . snd <$> defs
    forM_ names $ \name -> do
      type_ <- fetch $ Query.ElaboratedType name
      liftIO $ putDoc $ pretty name <> " : " <> Pretty.prettyTerm 0 Pretty.empty type_ <> line
      maybeDef <- fetch $ Query.ElaboratedDefinition name
      liftIO $ forM_ maybeDef $ \(def, _) ->
        putDoc $ Pretty.prettyDefinition name def <> line
  forM_ errs $ \(filePath, lineColumn, lineText, err) ->
    liftIO $ putDoc $ Error.pretty filePath lineColumn lineText err <> line