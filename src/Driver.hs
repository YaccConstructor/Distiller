module Driver where

import Data.Foldable (find)
import DistillationHelpers
import LTSType
import TermType
import Debug.Trace (trace)

-- term -- functions names accumulator -- functions definitions = [(funName, ([args], term))]
drive :: Term -> [String] -> [(String, ([String], Term))] -> LTS
drive term@(Free x) _ _ = doLTS1Tr term (X' x) doLTS0Tr
drive term@(Con conName expressions) funsNames funsDefs = doLTSManyTr term $ (:) (Con' conName, doLTS0Tr) $ zip (map ConArg' createLabels) $ map (\e -> drive e funsNames funsDefs) expressions
drive term@(Lambda x expression) funsNames funsDefs = doLTS1Tr term (Lambda' x) $ drive expression funsNames funsDefs
drive term@(Fun funName) funsNames funsDefs | trace ("in driving " ++ funName ++ ";" ++ show funsNames) False = undefined
drive term@(Fun funName) funsNames funsDefs =
  if funName `elem` funsNames
    then doLTS1Tr term (Unfold' funName) doLTS0Tr
    else
      let term' = find (\(funName', _) -> funName == funName') funsDefs
       in case term' of
            Just (_, (_, term'')) -> do doLTS1Tr term (Unfold' funName) $ drive term'' (funName : funsNames) funsDefs
            Nothing -> error $ "Function " ++ show funName ++ " does not have definition."
drive term@(Apply e0 e1) funsNames funsDefs =
    doLTSManyTr term [(Apply0', drive e0 funsNames funsDefs), (Apply1', drive e1 funsNames funsDefs)]
drive term@(Case e0 branches) funsNames funsDefs =
  doLTSManyTr term $
    (:) (Case', drive e0 funsNames funsDefs) $
      map (\(branchName, args, branchResultTerm) -> (CaseBranch' branchName args, drive branchResultTerm funsNames funsDefs)) branches
drive term@(Let x e0 e1) funsNames funsDefs = 
  doLTSManyTr term [(Let', drive e1 funsNames funsDefs), (LetX' x, drive e0 funsNames funsDefs)]
drive (MultipleApply e0 eiDefinitions) funsNames funsDefs = drive e0 funsNames (funsDefs ++ eiDefinitions)   

