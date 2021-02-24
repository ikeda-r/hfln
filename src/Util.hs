module Util where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type Set = Set.Set
type Map = Map.Map

allEqual :: Eq a => [a] -> Bool
allEqual [] = True
allEqual [_] = True
allEqual (x1 : x2 : xs) =
    if x1 == x2 then
        allEqual (x2 : xs)
    else
        False

maybeAt :: [a] -> Int -> Maybe a
maybeAt list index
    | index < 0 = Nothing
    | otherwise = maybeAt' list index
        where
            maybeAt' :: [a] -> Int -> Maybe a
            maybeAt' [] _ = Nothing
            maybeAt' (l : _) 0 = Just l
            maybeAt' (_ : ls) n = maybeAt' ls (n - 1)

isUniqueList :: Ord a => [a] -> Bool
isUniqueList xs = length xs == Set.size (Set.fromList xs)

untilM :: Monad m => (a -> Bool) -> (a -> m a) -> a -> m a
untilM p f = go
    where
        go x
            | p x = return x
            | otherwise = do
                x' <- f x
                go x'

toMultiMap :: Ord a => [(a, b)] -> Map a [b]
toMultiMap [] = Map.empty
toMultiMap ((k, v) : kvs) =
    Map.alter (\ mvs ->
        case mvs of
            Nothing -> Just [v]
            Just vs -> Just (v : vs)
        ) k (toMultiMap kvs)

multiMapToList :: Ord a => Map a [b] -> [(a, b)]
multiMapToList m =
    concat $ map (\ (k, vs) -> map (\ v -> (k, v)) vs) (Map.toList m)
