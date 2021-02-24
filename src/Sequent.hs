module Sequent where

import qualified Data.List as List
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Function

import Formula
import Util

data Side = SLeft | SRight
    deriving (Eq, Ord, Show, Read)

data Sequent =
    Sequent {
        sfv :: Map Var Type,
        sleft :: Map Int Formula,
        sright :: Map Int Formula,
        sleftId :: Int,
        srightId :: Int,
        smunu :: Map (Side, Int) [[Int]]
        }
    deriving (Show)

getFormula :: Sequent -> (Side, [Int]) -> Maybe Formula
getFormula sq (side, i : addr) = do
    let fs =
            case side of
                SLeft -> sleft sq
                SRight -> sright sq
    basef <- Map.lookup i fs
    getFormulaByAddr addr basef
getFormula _ _ = Nothing

-- smunuも更新, sfvは更新しない
addFormula :: Side -> Formula -> Sequent -> (Int, Sequent)
addFormula side f sq =
    case side of
        SLeft -> (sleftId sq,
            sq {
                sleft = Map.insert (sleftId sq) f (sleft sq),
                sleftId = sleftId sq + 1,
                smunu = Map.insert (SLeft, sleftId sq) (getMuAddr f) (smunu sq)
                })
        SRight -> (srightId sq,
            sq {
                sright = Map.insert (srightId sq) f (sright sq),
                srightId = srightId sq + 1,
                smunu = Map.insert (SRight, srightId sq) (getNuAddr f) (smunu sq)
                })

removeFormula :: Side -> Int -> Sequent -> Maybe Sequent
removeFormula side i sq =
    if Map.member (side, i) (smunu sq) then
        Just $ case side of
            SLeft ->
                sq {
                    sleft = Map.delete i (sleft sq),
                    smunu = Map.delete (SLeft, i) (smunu sq)
                    }
            SRight ->
                sq {
                    sright = Map.delete i (sright sq),
                    smunu = Map.delete (SRight, i) (smunu sq)
                    }
    else
        Nothing

replaceFormula :: Side -> Int -> Formula -> Sequent -> Maybe Sequent
replaceFormula side i f sq =
    if Map.member (side, i) (smunu sq) then
        Just $ case side of
            SLeft ->
                sq {
                    sleft = Map.insert i f (sleft sq),
                    smunu = Map.insert (SLeft, i) (getMuAddr f) (smunu sq)
                    }
            SRight ->
                sq {
                    sright = Map.insert i f (sright sq),
                    smunu = Map.insert (SRight, i) (getNuAddr f) (smunu sq)
                    }
    else
        Nothing

substituteAddrInSeq :: [(Side, [Int])] -> Formula -> Sequent -> Maybe Sequent
substituteAddrInSeq addrs sf sq = do
    kvs <- mapM (\ (side, addr) ->
            case addr of
                [] -> Nothing
                i : addr' -> Just ((side, i), addr')
            ) addrs :: Maybe [((Side, Int), [Int])]
    let alterf v mvs = Just $
            case mvs of
                Nothing -> [v]
                Just vs -> v : vs
        addrMap = foldr (\ (k, v) m -> Map.alter (alterf v) k m) Map.empty kvs
        addrList = Map.toList addrMap
        subst sq0 ((side, i), addr) =
            case side of
                SLeft -> do
                    df <- Map.lookup i (sleft sq0)
                    f <- substituteAddrInFormula addr sf df
                    return $ sq0 {
                        sleft = Map.insert i f (sleft sq0),
                        smunu = Map.insert (side, i) (getMuAddr f) (smunu sq0)
                        }
                SRight -> do
                    df <- Map.lookup i (sright sq0)
                    f <- substituteAddrInFormula addr sf df
                    return $ sq0 {
                        sright = Map.insert i f (sright sq0),
                        smunu = Map.insert (side, i) (getNuAddr f) (smunu sq0)
                        }
    foldM subst sq addrList
--

isFresh :: Sequent -> Var -> Bool
isFresh sq var = Map.notMember var (sfv sq)

declFreeVar :: Var -> Type -> Sequent -> Sequent
declFreeVar var t sq = sq {
    sfv = Map.insert var t (sfv sq)
    }

pruneFreeVar :: Sequent -> Sequent
pruneFreeVar sq = sq {
    sfv = newsfv
    }
    where
        lfs = map getFreeVar (Map.elems (sleft sq))
        rfs = map getFreeVar (Map.elems (sright sq))
        nfvs = Set.unions (lfs ++ rfs)
        cfvs = Map.keysSet (sfv sq)
        unusedfvs = Set.difference cfvs nfvs
        newsfv = foldr Map.delete (sfv sq) unusedfvs

getMunuAddrsFromBase :: Sequent -> (Side, [Int]) -> [[Int]]
getMunuAddrsFromBase _ (_, []) = []
getMunuAddrsFromBase sq (side, i : addr) =
    case mmunus of
        Just mn -> mn
        Nothing -> []
    where
        mmunus = do
            munus <- Map.lookup (side, i) (smunu sq)
            let filteredMunus = filter (List.isPrefixOf addr) munus
                len = length addr
                relMunus = map (drop len) filteredMunus
            return relMunus

initSequent :: Sequent
initSequent = Sequent {
    sfv = Map.empty,
    sleft = Map.empty,
    sright = Map.empty,
    sleftId = 0,
    srightId = 0,
    smunu = Map.empty
    }
