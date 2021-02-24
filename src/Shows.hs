module Shows where

import qualified Data.List as List
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Function

import Formula
import Proof
import Sequent
import Util

showType :: Type -> String
showType = sh
    where
        sh t0 =
            case t0 of
                TNat -> "N"
                TProp -> "P"
                TFun t1 t2 -> shp t1 ++ " -> " ++ sh t2
        shp t0 = 
            case t0 of
                TNat -> sh t0
                TProp -> sh t0
                TFun _ _ -> "(" ++ sh t0 ++ ")"

showFormula :: Formula -> String
showFormula = sh
    where
        sh f0 =
            case f0 of
                FFreeVar var -> "$" ++ var
                FBoundVar var -> "@" ++ var
                FZero -> "Z"
                FSucc f1 -> "S " ++ shp0 f1
                FEq f1 f2 -> shp1 f1 ++ " = " ++ shp1 f2
                FOr f1 f2 -> shp2 f1 ++ " \\/ " ++ shp2 f2
                FAnd f1 f2 -> shp2 f1 ++ " /\\ " ++ shp2 f2
                FFun var t f1 -> "\\ @" ++ var ++ " : " ++ showType t ++ ". " ++ sh f1
                FApp f1 f2 -> shp1 f1 ++ " " ++ shp0 f2
                FMu var t f1 -> "m @" ++ var ++ " : " ++ showType t ++ ". " ++ sh f1
                FNu var t f1 -> "n @" ++ var ++ " : " ++ showType t ++ ". " ++ sh f1
        shp0 f0 = 
            case f0 of
                FFreeVar _ -> sh f0
                FBoundVar _ -> sh f0
                FZero -> sh f0
                _ -> "(" ++ sh f0 ++ ")"
        shp1 f0 = 
            case f0 of
                FSucc _ -> sh f0
                FApp _ _ -> sh f0
                _ -> shp0 f0
        shp2 f0 = 
            case f0 of
                FEq _ _ -> sh f0
                _ -> shp1 f0

showSequent :: Sequent -> String
showSequent (Sequent { sfv = fv, sleft = lfs, sright = rfs }) =
    let toStrIf (i, f) = "    " ++ show i ++ " : " ++ showFormula f ++ "\n"
        toStrFv (v, t) = "    $" ++ v ++ " : " ++ showType t ++ "\n"
        fvstr = concat $ map toStrFv $ Map.toList fv
        lfstr = concat $ map toStrIf $ Map.toAscList lfs
        rfstr = concat $ map toStrIf $ Map.toAscList rfs
    in
        fvstr ++ lfstr ++ "    |-\n" ++ rfstr

showProof :: Proof -> Maybe String
showProof p = do
    (ce, css, cseq) <- getCurrent p
    let oes = List.intercalate ", " $ map show $ Set.toAscList $ openEdges p
        s = show ce ++ ", " ++ show (length css - 1) ++ "; open: " ++ oes ++ "\n" ++ showSequent cseq
    return s
