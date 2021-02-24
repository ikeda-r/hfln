module Main where

import System.Process
import System.Exit
import System.Environment
import System.IO
import qualified Data.List as List
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Function

import Formula
import Proof
import Shows
import Util
import Parser

makeInitProof :: ([Formula], [Formula], [(Var, Type)]) -> Maybe Proof
makeInitProof (lfs, rfs, fvs) =
    initProof $ ProofInit {
        piLeft = lfs,
        piRight = rfs,
        piFv = fvs
        }

isProofEnd :: Proof -> Bool
isProofEnd p = curEdge p == Nothing

appRuler :: Rule -> Proof -> IO (Maybe Proof)
appRuler r p = do
    case appRule r p of
        Nothing -> do
            hPutStrLn stderr "App rule failure"
            return Nothing
        Just (Nothing, p') -> return $ Just p'
        Just (Just input, p') -> do
            output <- readProcess "./sct/sct" ["--ptime"] input
            case output !! 1 of
                'T' -> return $ Just p'
                'F' -> do
                    output' <- readProcess "./sct/sct" [] input
                    case output' !! 1 of
                        'T' -> return $ Just p'
                        'F' -> do
                            hPutStrLn stderr "Gtc unsatisfied"
                            return Nothing
                        _ -> die "Unknown sct output"
                _ -> die "Unknown sct output"

appRules :: [Rule] -> Proof -> IO Proof
appRules rs prf = foldM (\ p r -> do
    mp <- appRuler r p
    case mp of
        Nothing -> return p
        Just p' -> return p') prf rs

appRuleIO :: Proof -> IO (Proof, Maybe String)
appRuleIO p = do
    Just output <- return $ showProof p
    putStr output
    putStr "> "
    hFlush stdout
    rstr <- getLine
    case parseRule rstr of
        Nothing -> do
            hPutStrLn stderr "Parse error"
            return (p, Nothing)
        Just r -> do
            mp <- appRuler r p
            case mp of
                Nothing -> return (p, Nothing)
                Just p' -> return (p', Just rstr)

mainp :: Proof -> IO [String]
mainp prf = do
    let f p = 
            if isProofEnd p then
                return []
            else do
                (p', mstr) <- appRuleIO p
                strs <- f p'
                case mstr of
                    Nothing -> return strs
                    Just str -> return (str : strs)
    rstr <- f prf
    hPutStrLn stderr "Proof completed"
    return rstr

main :: IO ()
main = do
    putStr "> "
    hFlush stdout
    initstr <- getLine
    case parseInit initstr of
        Nothing -> hPutStrLn stderr "Parse error"
        Just init ->
            case makeInitProof init of
                Nothing -> hPutStrLn stderr "Invalid init"
                Just p0 -> do
                    rstr <- mainp p0
                    args <- getArgs
                    case args of
                        path : _ -> writeFile path (unlines (initstr : rstr))
                        _ -> return ()
