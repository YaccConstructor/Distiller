module Driver where

import TermType
import LTSType
import HelperTypes
import Data.Foldable (find)

-- [(funName, ([args], term))]
drive :: Term -> [String] -> [(String, ([String], Term))] -> LTS
drive term@(Free x) _ _ = doLTS1Tr term x doLTS0Tr
drive term@(Con conName expressions) funsNames funsDefs = doLTSManyTr term $ (:) (conName, doLTS0Tr) $ zip createLabels $ map (\e -> drive e funsNames funsDefs) expressions
drive term@(Lambda x expression) funsNames funsDefs = doLTS1Tr term x $ drive expression funsNames funsDefs
drive term@(Fun funName) funsNames funsDefs = if funName `elem` funsNames  
        then doLTS1Tr term funName doLTS0Tr
        else let 
            term' = find (\(funName', _) -> funName == funName')  funsDefs
            in case term' of 
                Just (_, (_, term'')) -> doLTS1Tr term funName $ drive term'' (funName : funsNames) funsDefs
                Nothing -> error "This function does not have definition."      
                
 
createLabels :: [String]
createLabels = map ((++) "#" . show) [0,1..]