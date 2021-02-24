module Graph where

import qualified Data.List as List
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Function

import Sequent
import Util

type Graph = [((Side, [Int]), (Side, [Int]), SctSizeRel)]

data SctSizeRel = SsDec | SsDeq
    deriving (Eq, Show)

composeGraphs :: [Graph] -> Graph
composeGraphs gs =
    case gs of
        [] -> []
        g0 : gos -> toGlist $ List.foldl' compose (toGmap g0) (map toGmap gos)
    where
        toGmap :: Graph -> Map (Side, [Int]) [((Side, [Int]), SctSizeRel)]
        toGmap g = toMultiMap $ map (\ (a1, a2, r) -> (a1, (a2, r))) g
        toGlist :: Map (Side, [Int]) [((Side, [Int]), SctSizeRel)] -> Graph
        toGlist gm = map (\ (a1, (a2, r)) -> (a1, a2, r)) $ multiMapToList gm
        prune :: [((Side, [Int]), SctSizeRel)] -> [((Side, [Int]), SctSizeRel)]
        prune ars =
            let f (a, r) m =
                    case r of
                        SsDec -> Map.insert a SsDec m
                        SsDeq -> Map.alter (\ mr ->
                            case mr of
                                Nothing -> Just SsDeq
                                Just r' -> Just r'
                            ) a m
                arm = foldr f Map.empty ars
            in Map.toList arm
        mapf :: Map (Side, [Int]) [((Side, [Int]), SctSizeRel)]
            -> [((Side, [Int]), SctSizeRel)]
            -> Maybe [((Side, [Int]), SctSizeRel)]
        mapf g2 ars1 =
            let f (a2, r1) =
                    case Map.lookup a2 g2 of
                        Nothing -> []
                        Just ars2 -> case r1 of
                            SsDec -> map (\ (a3, _) -> (a3, SsDec)) ars2
                            SsDeq -> ars2
                ars = concat $ map f ars1
            in
                case prune ars of
                    [] -> Nothing
                    pars -> Just pars
        compose :: Map (Side, [Int]) [((Side, [Int]), SctSizeRel)]
            -> Map (Side, [Int]) [((Side, [Int]), SctSizeRel)]
            -> Map (Side, [Int]) [((Side, [Int]), SctSizeRel)]
        compose g1 g2 = Map.mapMaybe (mapf g2) g1

makeIdGraph :: Sequent -> Graph
makeIdGraph sq = makeIdGraphExceptFormulas sq []

makeIdGraphExceptFormulas :: Sequent -> [(Side, [Int])] -> Graph
makeIdGraphExceptFormulas sq addrs = g
    where
        makeMunus :: [(Side, [Int])] -> Map (Side, Int) [[Int]]
        makeMunus [] = smunu sq
        makeMunus ((s, []) : sas) = makeMunus sas
        makeMunus ((s, a : as) : sas) =
            Map.adjust (filter (not . List.isPrefixOf as)) (s, a) (makeMunus sas)
        munus = makeMunus addrs
        munus1 = map (\ ((s, a), as) -> (s, a : as)) (multiMapToList munus)
        g = map (\ mn -> (mn, mn, SsDeq)) munus1

makeDeqGraphWithPrefix  :: [[Int]] -> (Side, [Int]) -> (Side, [Int]) -> Graph
makeDeqGraphWithPrefix addrs (s1, a1) (s2, a2) = map (\ addr ->
    ((s1, a1 ++ addr), (s2, a2 ++ addr), SsDeq)) addrs

makeDecGraph :: (Side, [Int]) -> (Side, [Int]) -> Graph
makeDecGraph addr1 addr2 = [(addr1, addr2, SsDec)]
