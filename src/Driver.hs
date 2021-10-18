module Driver where

import Data.Foldable (find)
import HelperTypes
import LTSType
import TermType

-- term -- functions names accumulator -- functions definitions = [(funName, ([args], term))]
drive :: Term -> [String] -> [(String, ([String], Term))] -> LTS
drive term@(Free x) _ _ = doLTS1Tr term x doLTS0Tr
drive term@(Con conName expressions) funsNames funsDefs = doLTSManyTr term $ (:) (conName, doLTS0Tr) $ zip createLabels $ map (\e -> drive e funsNames funsDefs) expressions
drive term@(Lambda x expression) funsNames funsDefs = doLTS1Tr term x $ drive expression funsNames funsDefs
drive term@(Fun funName) funsNames funsDefs =
  if funName `elem` funsNames
    then doLTS1Tr term funName doLTS0Tr
    else
      let term' = find (\(funName', _) -> funName == funName') funsDefs
       in case term' of
            Just (_, (_, term'')) -> doLTS1Tr term funName $ drive term'' (funName : funsNames) funsDefs
            Nothing -> error "This function does not have definition."
drive term@(Apply e0 e1) funsNames funsDefs = doLTSManyTr term $ (:) ("@", drive e0 funsNames funsDefs) $ zip createLabels [drive e1 funsNames funsDefs]
drive term@(Case e0 branches) funsNames funsDefs =
  doLTSManyTr term $
    (:) ("case", drive e0 funsNames funsDefs) $
      map (\(branchName, _, branchResultTerm) -> (branchName, drive branchResultTerm funsNames funsDefs)) branches
drive term@(Let x e0 e1) funsNames funsDefs = 
  doLTSManyTr term [("let", drive e1 funsNames funsDefs), (x, drive e0 funsNames funsDefs)]      
drive (MultipleApply e0 eiDefinitions) funsNames funsDefs = drive e0 funsNames (funsDefs ++ eiDefinitions)  
  
