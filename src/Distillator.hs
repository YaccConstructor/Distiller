module Distillator where


dist (t,d) = let e = map (processFun d) d
                 t' = returnval (trans 2 t EmptyCtx (free t) [] d e)
                 (t'',d',e') = residualise t' d e
             in  (t'',d')
