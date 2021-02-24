module Formula where

import qualified Data.List as List
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Function

import Util

type Var = String
data Type =
    TNat
    | TProp
    | TFun Type Type
    deriving (Eq, Show, Read)
data Formula =
    FFreeVar Var
    | FBoundVar Var
    | FZero
    | FSucc Formula
    | FEq Formula Formula
    | FOr Formula Formula
    | FAnd Formula Formula
    | FFun Var Type Formula
    | FApp Formula Formula
    | FMu Var Type Formula
    | FNu Var Type Formula
    deriving (Show, Read)

instance Eq Formula where
    a == b = eq a b Map.empty
        where
            eq :: Formula -> Formula -> Map Var Var -> Bool
            eq (FFreeVar v1) (FFreeVar v2) _ = v1 == v2
            eq (FBoundVar v1) (FBoundVar v2) bvenv =
                case Map.lookup v1 bvenv of
                    Nothing -> v1 == v2
                    Just v -> v == v2
            eq FZero FZero _ = True
            eq (FSucc f1) (FSucc f2) bvenv = eq f1 f2 bvenv
            eq (FEq f11 f12) (FEq f21 f22) bvenv = eq f11 f21 bvenv && eq f12 f22 bvenv
            eq (FOr f11 f12) (FOr f21 f22) bvenv = eq f11 f21 bvenv && eq f12 f22 bvenv
            eq (FAnd f11 f12) (FAnd f21 f22) bvenv = eq f11 f21 bvenv && eq f12 f22 bvenv
            eq (FFun v1 t1 f1) (FFun v2 t2 f2) bvenv = t1 == t2 && eq f1 f2 (Map.insert v1 v2 bvenv)
            eq (FApp f11 f12) (FApp f21 f22) bvenv = eq f11 f21 bvenv && eq f12 f22 bvenv
            eq (FMu v1 t1 f1) (FMu v2 t2 f2) bvenv = t1 == t2 && eq f1 f2 (Map.insert v1 v2 bvenv)
            eq (FNu v1 t1 f1) (FNu v2 t2 f2) bvenv = t1 == t2 && eq f1 f2 (Map.insert v1 v2 bvenv)
            eq _ _ _ = False

substituteAddrInFormula :: [[Int]] -> Formula -> Formula -> Maybe Formula
substituteAddrInFormula daddrs sf df = subst daddrs df
    where
        subst :: [[Int]] -> Formula -> Maybe Formula
        subst as f =
            case f of
                FFreeVar _ -> nullary
                FBoundVar _ -> nullary
                FZero -> nullary
                FSucc f1 -> unary FSucc f1
                FEq f1 f2 -> binary FEq f1 f2
                FOr f1 f2 -> binary FOr f1 f2
                FAnd f1 f2 -> binary FAnd f1 f2
                FFun var t f1 -> unary (FFun var t) f1
                FApp f1 f2 -> binary FApp f1 f2
                FMu var t f1 -> unary (FMu var t) f1
                FNu var t f1 -> unary (FNu var t) f1
            where
                nullary =
                    let (asn, aso) = List.partition null as
                    in if not (null aso) then
                            Nothing
                        else if null asn then
                            Just f
                        else
                            Just sf
                unary ff f1 =
                    let (asn, asno) = List.partition null as
                        (as0', aso) = List.partition (List.isPrefixOf [0]) asno
                        as0 = map (drop 1) as0'
                    in if not (null aso) then
                            Nothing
                        else if null asn then do
                            f1' <- subst as0 f1
                            Just (ff f1')
                        else if null asno then
                            Just sf
                        else
                            Nothing
                binary ff f1 f2 =
                    let (asn, asno) = List.partition null as
                        (as0', aso') = List.partition (List.isPrefixOf [0]) asno
                        (as1', aso) = List.partition (List.isPrefixOf [1]) aso'
                        as0 = map (drop 1) as0'
                        as1 = map (drop 1) as1'
                    in if not (null aso) then
                            Nothing
                        else if null asn then do
                            f1' <- subst as0 f1
                            f2' <- subst as1 f2
                            Just (ff f1' f2')
                        else if null asno then
                            Just sf
                        else
                            Nothing

substituteBoundVarInFormula :: Var -> Formula -> Formula -> ([[Int]], Formula)
substituteBoundVarInFormula dvar sf df = subst df
    where
        subst :: Formula -> ([[Int]], Formula)
        subst f@(FFreeVar _) = ([], f)
        subst f@(FBoundVar var)
            | var == dvar = ([[]], sf)
            | otherwise = ([], f)
        subst f@FZero = ([], f)
        subst (FSucc f1) =
            let (as1, f1') = subst f1
            in (map (0 :) as1, FSucc f1')
        subst (FEq f1 f2) =
            let (as1, f1') = subst f1
                (as2, f2') = subst f2
            in (map (0 :) as1 ++ map (1 :) as2, FEq f1' f2')
        subst (FOr f1 f2) =
            let (as1, f1') = subst f1
                (as2, f2') = subst f2
            in (map (0 :) as1 ++ map (1 :) as2, FOr f1' f2')
        subst (FAnd f1 f2) =
            let (as1, f1') = subst f1
                (as2, f2') = subst f2
            in (map (0 :) as1 ++ map (1 :) as2, FAnd f1' f2')
        subst f@(FFun var t f1)
            | var == dvar = ([], f)
            | otherwise =
                let (as1, f1') = subst f1
                in (map (0 :) as1, FFun var t f1')
        subst (FApp f1 f2) =
            let (as1, f1') = subst f1
                (as2, f2') = subst f2
            in (map (0 :) as1 ++ map (1 :) as2, FApp f1' f2')
        subst f@(FMu var t f1)
            | var == dvar = ([], f)
            | otherwise =
                let (as1, f1') = subst f1
                in (map (0 :) as1, FMu var t f1')
        subst f@(FNu var t f1)
            | var == dvar = ([], f)
            | otherwise =
                let (as1, f1') = subst f1
                in (map (0 :) as1, FNu var t f1')

getFormulaByAddr :: [Int] -> Formula -> Maybe Formula
getFormulaByAddr [] f = Just f
getFormulaByAddr (i : addr) f =
    case f of
        FFreeVar _ -> Nothing
        FBoundVar _ -> Nothing
        FZero -> Nothing
        FSucc f1 -> unary f1
        FEq f1 f2 -> binary f1 f2
        FOr f1 f2 -> binary f1 f2
        FAnd f1 f2 -> binary f1 f2
        FFun _ _ f1 -> unary f1
        FApp f1 f2 -> binary f1 f2
        FMu _ _ f1 -> unary f1
        FNu _ _ f1 -> unary f1
    where
        unary f1 = guard (i == 0) >> getFormulaByAddr addr f1
        binary f1 f2 =
            case i of
                0 -> getFormulaByAddr addr f1
                1 -> getFormulaByAddr addr f2
                _ -> Nothing

argTypes :: Type -> [Type]
argTypes (TFun t1 t2) = t1 : argTypes t2
argTypes _ = []

returnType :: Type -> Type
returnType (TFun _ t) = returnType t
returnType t = t

-- f must be a closed, well-typed formula
calcType :: Formula -> Map Var Type -> Maybe Type
calcType f env = calcType' f env Map.empty
    where
        calcType' :: Formula -> Map Var Type -> Map Var Type -> Maybe Type
        calcType' (FFreeVar var) fvenv _ = Map.lookup var fvenv
        calcType' (FBoundVar var) _ bvenv = Map.lookup var bvenv
        calcType' FZero _ _ = Just TNat
        calcType' (FSucc _) _ _ = Just TNat
        calcType' (FEq _ _) _ _ = Just TProp
        calcType' (FOr _ _) _ _ = Just TProp
        calcType' (FAnd _ _) _ _ = Just TProp
        calcType' (FFun var t1 f) fvenv bvenv = do
            t2 <- calcType' f fvenv (Map.insert var t1 bvenv)
            return $ TFun t1 t2
        calcType' (FApp f _) fvenv bvenv = do
            TFun _ t <- calcType' f fvenv bvenv
            return t
        calcType' (FMu _ t _) _ _ = Just t
        calcType' (FNu _ t _) _ _ = Just t

getFreeVar :: Formula -> Set Var
getFreeVar (FFreeVar var) = Set.singleton var
getFreeVar (FBoundVar _) = Set.empty
getFreeVar (FZero) = Set.empty
getFreeVar (FSucc f1) = getFreeVar f1
getFreeVar (FEq f1 f2) = Set.union (getFreeVar f1) (getFreeVar f2)
getFreeVar (FOr f1 f2) = Set.union (getFreeVar f1) (getFreeVar f2)
getFreeVar (FAnd f1 f2) = Set.union (getFreeVar f1) (getFreeVar f2)
getFreeVar (FFun _ _ f1) = getFreeVar f1
getFreeVar (FApp f1 f2) = Set.union (getFreeVar f1) (getFreeVar f2)
getFreeVar (FMu _ _ f1) = getFreeVar f1
getFreeVar (FNu _ _ f1) = getFreeVar f1

decomposeApp :: Formula -> [Formula]
decomposeApp f = reverse $ decomposeApp' f
    where
        decomposeApp' (FApp f1 f2) = f2 : decomposeApp' f1
        decomposeApp' f1 = [f1]

appArgs :: Formula -> [Formula] -> Formula
appArgs fun [] = fun
appArgs fun (arg : args) = appArgs (FApp fun arg) args

-- f must be a closed formula
isWellTyped :: Formula -> Map Var Type -> Bool
isWellTyped f env =
    case calcType' f env Map.empty of
        Just _ -> True
        Nothing -> False
    where
        calcType' :: Formula -> Map Var Type -> Map Var Type -> Maybe Type
        calcType' (FFreeVar var) fvenv _ = Map.lookup var fvenv
        calcType' (FBoundVar var) _ bvenv = Map.lookup var bvenv
        calcType' FZero _ _ = Just TNat
        calcType' (FSucc f1) fvenv bvenv = do
            guard (calcType' f1 fvenv bvenv == Just TNat)
            return TNat
        calcType' (FEq f1 f2) fvenv bvenv = do
            guard (calcType' f1 fvenv bvenv == Just TNat)
            guard (calcType' f2 fvenv bvenv == Just TNat)
            return TProp
        calcType' (FOr f1 f2) fvenv bvenv = do
            guard (calcType' f1 fvenv bvenv == Just TProp)
            guard (calcType' f2 fvenv bvenv == Just TProp)
            return TProp
        calcType' (FAnd f1 f2) fvenv bvenv = do
            guard (calcType' f1 fvenv bvenv == Just TProp)
            guard (calcType' f2 fvenv bvenv == Just TProp)
            return TProp
        calcType' (FFun var t1 f) fvenv bvenv = do
            t2 <- calcType' f fvenv (Map.insert var t1 bvenv)
            return $ TFun t1 t2
        calcType' (FApp f1 f2) fvenv bvenv = do
            TFun t11 t12 <- calcType' f1 fvenv bvenv
            t2 <- calcType' f2 fvenv bvenv
            guard (t11 == t2)
            return t12
        calcType' (FMu var t1 f) fvenv bvenv = do
            t2 <- calcType' f fvenv (Map.insert var t1 bvenv)
            guard (t1 == t2)
            return t1
        calcType' (FNu var t1 f) fvenv bvenv = do
            t2 <- calcType' f fvenv (Map.insert var t1 bvenv)
            guard (t1 == t2)
            return t1

isClosedFormula :: Formula -> Bool
isClosedFormula f = isClosedFormula' f Set.empty
    where
        isClosedFormula' :: Formula -> Set Var -> Bool
        isClosedFormula' (FFreeVar var) bvs = True
        isClosedFormula' (FBoundVar var) bvs = Set.member var bvs
        isClosedFormula' FZero _ = True
        isClosedFormula' (FSucc f1) bvs = isClosedFormula' f1 bvs
        isClosedFormula' (FEq f1 f2) bvs = isClosedFormula' f1 bvs && isClosedFormula' f2 bvs
        isClosedFormula' (FOr f1 f2) bvs = isClosedFormula' f1 bvs && isClosedFormula' f2 bvs
        isClosedFormula' (FAnd f1 f2) bvs = isClosedFormula' f1 bvs && isClosedFormula' f2 bvs
        isClosedFormula' (FFun var _ f) bvs = isClosedFormula' f (Set.insert var bvs)
        isClosedFormula' (FApp f1 f2) bvs = isClosedFormula' f1 bvs && isClosedFormula' f2 bvs
        isClosedFormula' (FMu var _ f) bvs = isClosedFormula' f (Set.insert var bvs)
        isClosedFormula' (FNu var _ f) bvs = isClosedFormula' f (Set.insert var bvs)

getMuAddr :: Formula -> [[Int]]
getMuAddr f =
    case f of
        FFreeVar _ -> []
        FBoundVar _ -> []
        FZero -> []
        FSucc f1 -> map (0 :) (getMuAddr f1)
        FEq f1 f2 -> map (0 :) (getMuAddr f1) ++ map (1 :) (getMuAddr f2)
        FOr f1 f2 -> map (0 :) (getMuAddr f1) ++ map (1 :) (getMuAddr f2)
        FAnd f1 f2 -> map (0 :) (getMuAddr f1) ++ map (1 :) (getMuAddr f2)
        FFun _ _ f1 -> map (0 :) (getMuAddr f1)
        FApp f1 f2 -> map (0 :) (getMuAddr f1) ++ map (1 :) (getMuAddr f2)
        FMu _ _ f1 -> [] : map (0 :) (getMuAddr f1)
        FNu _ _ f1 -> map (0 :) (getMuAddr f1)

getNuAddr :: Formula -> [[Int]]
getNuAddr f =
    case f of
        FFreeVar _ -> []
        FBoundVar _ -> []
        FZero -> []
        FSucc f1 -> map (0 :) (getNuAddr f1)
        FEq f1 f2 -> map (0 :) (getNuAddr f1) ++ map (1 :) (getNuAddr f2)
        FOr f1 f2 -> map (0 :) (getNuAddr f1) ++ map (1 :) (getNuAddr f2)
        FAnd f1 f2 -> map (0 :) (getNuAddr f1) ++ map (1 :) (getNuAddr f2)
        FFun _ _ f1 -> map (0 :) (getNuAddr f1)
        FApp f1 f2 -> map (0 :) (getNuAddr f1) ++ map (1 :) (getNuAddr f2)
        FMu _ _ f1 -> map (0 :) (getNuAddr f1)
        FNu _ _ f1 -> [] : map (0 :) (getNuAddr f1)
