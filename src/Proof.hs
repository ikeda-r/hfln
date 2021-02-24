module Proof where

import qualified Data.List as List
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Function

import Formula
import Graph
import Sequent
import Util

data Rule =
    RAxiom Int Int
    | RCut Formula [(Var, Type)]
    | RWk Side Int
    | RCtr Side Int
    | RSubst [(Side, [Int])] Var
    | RMono Int Int [[Int]] [Var]
    | REqL Int [(Side, [Int])] [(Side, [Int])]
    | REqR Int
    | ROr Side Int
    | RAnd Side Int
    | RFun Side Int
    | RMu Side Int
    | RNu Side Int
    | RNat Var
    | RP1 Int
    | RP2 Int
    | RBackEdge Int Int [(Int, Int)] [(Int, Int)]
    | RSwitch Int
    deriving (Eq, Show, Read)

data SequentLink =
    SlOpen
    | SlEnd
    | SlBranch Int Int
    | SlBackEdge Int Int
    deriving (Eq, Show)

data SequentEdge =
    SequentEdge SequentLink [(Sequent, Graph)]
    deriving (Show)

data Proof =
    Proof {
        sequentEdges :: Map Int SequentEdge,
        openEdges :: Set Int,
        curEdge :: Maybe Int,
        backEdges :: Map Int (Map Int Graph), -- Map toEdge (Map fromEdge graph)
        sequentEdgesFrom :: Map Int Int,
        graphs :: Map (Int, Int) Graph
        }
    deriving (Show)

data ProofInit =
    ProofInit {
        piLeft :: [Formula],
        piRight :: [Formula],
        piFv :: [(Var, Type)]
    }
    deriving (Show)

getCurrent :: Proof -> Maybe (Int, [(Sequent, Graph)], Sequent)
getCurrent p = do
    ce <- curEdge p
    SequentEdge _ css@((cseq, _) : _) <- Map.lookup ce (sequentEdges p)
    return (ce, css, cseq)

appRule' :: Rule -> Proof -> Maybe Proof
appRule' (RAxiom l r) p = do
    (ce, css, cseq) <- getCurrent p
    lf <- getFormula cseq (SLeft, [l])
    rf <- getFormula cseq (SRight, [r])
    guard (lf == rf)
    let noes = Set.delete ce (openEdges p)
        nses = Map.insert ce (SequentEdge SlEnd css) (sequentEdges p)
    return $ p {
        sequentEdges = nses,
        openEdges = noes,
        curEdge = Set.lookupMin noes
        }

appRule' (RCut f vts) p = do
    (ce, css, cseq) <- getCurrent p
    guard (isClosedFormula f)
    guard (isUniqueList (map fst vts))
    let cseq1 = foldr (uncurry declFreeVar) cseq vts
    guard (isWellTyped f (sfv cseq1))
    ft <- calcType f (sfv cseq1)
    guard (ft == TProp)
    let ne = Map.size (sequentEdges p) + 1
        (_, lseq) = addFormula SLeft f cseq1
        (_, rseq) = addFormula SRight f cseq1
        ngraph = makeIdGraph cseq
        nses = sequentEdges p
            & Map.insert ce (SequentEdge (SlBranch ne (ne + 1)) css)
            & Map.insert ne (SequentEdge SlOpen [(lseq, ngraph)])
            & Map.insert (ne + 1) (SequentEdge SlOpen [(rseq, ngraph)])
        noes = openEdges p
            & Set.delete ce
            & Set.insert ne
            & Set.insert (ne + 1)
    return $ p {
        sequentEdges = nses,
        openEdges = noes,
        curEdge = Just ne
        }

appRule' (RWk side i) p = do
    (ce, css, cseq) <- getCurrent p
    nseq <- removeFormula side i cseq
    let nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, makeIdGraph nseq) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RCtr side i) p = do
    (ce, css, cseq) <- getCurrent p
    f <- getFormula cseq (side, [i])
    let (j, nseq) = addFormula side f cseq
        bgraph = makeIdGraph cseq
        addr = getMunuAddrsFromBase cseq (side, [i])
        cgraph1 = makeDeqGraphWithPrefix addr (side, [i]) (side, [j])
        ngraph = cgraph1 ++ bgraph
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RSubst phis var) p = do
    (ce, css, cseq) <- getCurrent p
    phifs <- mapM (getFormula cseq) phis
    guard (allEqual phifs)
    guard (isFresh cseq var)
    nseq <- case phifs of
        [] -> return cseq
        f : _ -> do
            guard (isClosedFormula f)
            t <- calcType f (sfv cseq)
            let cseq1 = declFreeVar var t cseq
            cseq2 <- substituteAddrInSeq phis (FFreeVar var) cseq1
            let cseq3 = pruneFreeVar cseq2
            return cseq3
    let ngraph = makeIdGraph nseq
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RMono phipsi phichi xs vars) p = do
    (ce, css, cseq) <- getCurrent p
    phipsif <- getFormula cseq (SLeft, [phipsi])
    phichif <- getFormula cseq (SRight, [phichi])
    let psis = map (\ x -> (SLeft, phipsi : x)) xs
        chis = map (\ x -> (SRight, phichi : x)) xs
    psifs <- mapM (getFormula cseq) psis
    chifs <- mapM (getFormula cseq) chis
    guard (allEqual psifs)
    guard (allEqual chifs)
    guard (isUniqueList vars)
    guard (all (isFresh cseq) vars)
    phi1 <- substituteAddrInFormula xs (FFreeVar "") phipsif
    phi2 <- substituteAddrInFormula xs (FFreeVar "") phichif
    guard (phi1 == phi2)
    psif : _ <- Just psifs
    chif : _ <- Just chifs
    guard (isClosedFormula psif)
    guard (isClosedFormula chif)
    psit <- calcType psif (sfv cseq)
    chit <- calcType chif (sfv cseq)
    guard (psit == chit)
    guard (returnType psit == TProp)
    let ts = argTypes psit
        psiyf = appArgs psif (map FFreeVar vars) 
        chiyf = appArgs chif (map FFreeVar vars)
        addr = replicate (length vars) 0
        psi = (SLeft, phipsi : addr)
        chi = (SRight, phichi : addr)
    cseq1 <- Just cseq
        >>= replaceFormula SLeft phipsi psiyf
        >>= replaceFormula SRight phichi chiyf
    let cseq2 = pruneFreeVar cseq1
        nseq = foldr (uncurry declFreeVar) cseq2 (zip vars ts)
        bgraph = makeIdGraphExceptFormulas nseq [(SLeft, [phipsi]), (SRight, [phichi])]
        psimus = getMunuAddrsFromBase nseq psi
        chinus = getMunuAddrsFromBase nseq chi
        cgraphs1 = map (\ x -> makeDeqGraphWithPrefix psimus x psi) psis
        cgraphs2 = map (\ x -> makeDeqGraphWithPrefix chinus x chi) chis
        ngraph = concat (cgraphs1 ++ cgraphs2) ++ bgraph
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (REqL eq xs ys) p = do
    (ce, css, cseq) <- getCurrent p
    FEq sf tf <- getFormula cseq (SLeft, [eq])
    sfs <- mapM (getFormula cseq) xs
    tfs <- mapM (getFormula cseq) ys
    guard (allEqual (sf : sfs))
    guard (allEqual (tf : tfs))
    cseq1 <- Just cseq
        >>= removeFormula SLeft eq
        >>= substituteAddrInSeq xs tf
        >>= substituteAddrInSeq ys sf
    let nseq = pruneFreeVar cseq1
        ngraph = makeIdGraph nseq
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (REqR i) p = do
    (ce, css, cseq) <- getCurrent p
    FEq tf1 tf2 <- getFormula cseq (SRight, [i])
    guard (tf1 == tf2)
    let noes = Set.delete ce (openEdges p)
        nses = Map.insert ce (SequentEdge SlEnd css) (sequentEdges p)
    return $ p {
        sequentEdges = nses,
        openEdges = noes,
        curEdge = Set.lookupMin noes
        }

appRule' (ROr SLeft i) p = do
    (ce, css, cseq) <- getCurrent p
    FOr phif psif <- getFormula cseq (SLeft, [i])
    lseq <- replaceFormula SLeft i phif cseq
    rseq <- replaceFormula SLeft i psif cseq
    let ne = Map.size (sequentEdges p) + 1
        bgraph = makeIdGraphExceptFormulas cseq [(SLeft, [i])]
        laddr = getMunuAddrsFromBase lseq (SLeft, [i])
        raddr = getMunuAddrsFromBase rseq (SLeft, [i])
        lgraph1 = makeDeqGraphWithPrefix laddr (SLeft, [i, 0]) (SLeft, [i])
        rgraph1 = makeDeqGraphWithPrefix raddr (SLeft, [i, 1]) (SLeft, [i])
        nses = sequentEdges p
            & Map.insert ce (SequentEdge (SlBranch ne (ne + 1)) css)
            & Map.insert ne (SequentEdge SlOpen [(lseq, lgraph1 ++ bgraph)])
            & Map.insert (ne + 1) (SequentEdge SlOpen [(rseq, rgraph1 ++ bgraph)])
        noes = openEdges p
            & Set.delete ce
            & Set.insert ne
            & Set.insert (ne + 1)
    return $ p {
        sequentEdges = nses,
        openEdges = noes,
        curEdge = Just ne
        }

appRule' (ROr SRight i) p = do
    (ce, css, cseq) <- getCurrent p
    FOr phif psif <- getFormula cseq (SRight, [i])
    cseq1 <- removeFormula SRight i cseq
    let (j, cseq2) = addFormula SRight phif cseq1
        (k, nseq) = addFormula SRight psif cseq2
        phiaddr = getMunuAddrsFromBase nseq (SRight, [j])
        psiaddr = getMunuAddrsFromBase nseq (SRight, [k])
        bgraph = makeIdGraphExceptFormulas cseq [(SRight, [i])]
        cgraph1 = makeDeqGraphWithPrefix phiaddr (SRight, [i, 0]) (SRight, [j])
        cgraph2 = makeDeqGraphWithPrefix psiaddr (SRight, [i, 1]) (SRight, [k])
        ngraph = cgraph1 ++ cgraph2 ++ bgraph
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RAnd SLeft i) p = do
    (ce, css, cseq) <- getCurrent p
    FAnd phif psif <- getFormula cseq (SLeft, [i])
    cseq1 <- removeFormula SLeft i cseq
    let (j, cseq2) = addFormula SLeft phif cseq1
        (k, nseq) = addFormula SLeft psif cseq2
        phiaddr = getMunuAddrsFromBase nseq (SLeft, [j])
        psiaddr = getMunuAddrsFromBase nseq (SLeft, [k])
        bgraph = makeIdGraphExceptFormulas cseq [(SLeft, [i])]
        cgraph1 = makeDeqGraphWithPrefix phiaddr (SLeft, [i, 0]) (SLeft, [j])
        cgraph2 = makeDeqGraphWithPrefix psiaddr (SLeft, [i, 1]) (SLeft, [k])
        ngraph = cgraph1 ++ cgraph2 ++ bgraph
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RAnd SRight i) p = do
    (ce, css, cseq) <- getCurrent p
    FAnd phif psif <- getFormula cseq (SRight, [i])
    lseq <- replaceFormula SRight i phif cseq
    rseq <- replaceFormula SRight i psif cseq
    let ne = Map.size (sequentEdges p) + 1
        bgraph = makeIdGraphExceptFormulas cseq [(SRight, [i])]
        laddr = getMunuAddrsFromBase lseq (SRight, [i])
        raddr = getMunuAddrsFromBase rseq (SRight, [i])
        lgraph1 = makeDeqGraphWithPrefix laddr (SRight, [i, 0]) (SRight, [i])
        rgraph1 = makeDeqGraphWithPrefix raddr (SRight, [i, 1]) (SRight, [i])
        nses = sequentEdges p
            & Map.insert ce (SequentEdge (SlBranch ne (ne + 1)) css)
            & Map.insert ne (SequentEdge SlOpen [(lseq, lgraph1 ++ bgraph)])
            & Map.insert (ne + 1) (SequentEdge SlOpen [(rseq, rgraph1 ++ bgraph)])
        noes = openEdges p
            & Set.delete ce
            & Set.insert ne
            & Set.insert (ne + 1)
    return $ p {
        sequentEdges = nses,
        openEdges = noes,
        curEdge = Just ne
        }

appRule' (RFun side i) p = do
    (ce, css, cseq) <- getCurrent p
    cf <- getFormula cseq (side, [i])
    (FFun var _ phi) : psi : psis <- Just $ decomposeApp cf
    let (xs, phipsi) = substituteBoundVarInFormula var psi phi
        nf = appArgs phipsi psis
    nseq <- replaceFormula side i nf cseq
    let psiNum = length psis
        phipsiAddr = (side, i : replicate psiNum 0)
        phiAddr = (side, i : 0 : 0 : replicate psiNum 0)
        psiAddr = (side, i : replicate psiNum 0 ++ [1])
        xAddrs = map (\ x -> (side, snd phipsiAddr ++ x)) xs
        phiMunus = getMunuAddrsFromBase cseq phiAddr
        psiMunus = getMunuAddrsFromBase cseq psiAddr
        bgraph = makeIdGraphExceptFormulas nseq [phipsiAddr]
        phigraph = makeDeqGraphWithPrefix phiMunus phiAddr phipsiAddr
        psigraphs = map (makeDeqGraphWithPrefix psiMunus psiAddr) xAddrs
        ngraph = concat psigraphs ++ phigraph ++ bgraph
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RMu side i) p = do
    (ce, css, cseq) <- getCurrent p
    cf <- getFormula cseq (side, [i])
    muphi@(FMu var _ phi) : psis <- Just $ decomposeApp cf
    let (xs, phimuphi) = substituteBoundVarInFormula var muphi phi
        nf = appArgs phimuphi psis
    nseq <- replaceFormula side i nf cseq
    let psiNum = length psis
        phimuphiAddr = (side, i : replicate psiNum 0)
        phiAddr = (side, i : 0 : replicate psiNum 0)
        muAddr = (side, i : replicate psiNum 0)
        xAddrs = map (\ x -> (side, snd phimuphiAddr ++ x)) xs
        xphiAddrs = map (\ x -> (side, i : replicate psiNum 0 ++ x ++ [0])) xs
        phiMus = getMunuAddrsFromBase cseq phiAddr
        bgraph = makeIdGraphExceptFormulas nseq [phimuphiAddr]
        phioutergraph = makeDeqGraphWithPrefix phiMus phiAddr phimuphiAddr
        phiinnergraphs = map (makeDeqGraphWithPrefix phiMus phiAddr) xphiAddrs
        mugraphs =
            case side of
                SLeft -> map (makeDecGraph muAddr) xAddrs
                SRight -> []
        ngraph = concat mugraphs ++ concat phiinnergraphs ++ phioutergraph ++ bgraph
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RNu side i) p = do
    (ce, css, cseq) <- getCurrent p
    cf <- getFormula cseq (side, [i])
    nuphi@(FNu var _ phi) : psis <- Just $ decomposeApp cf
    let (xs, phinuphi) = substituteBoundVarInFormula var nuphi phi
        nf = appArgs phinuphi psis
    nseq <- replaceFormula side i nf cseq
    let psiNum = length psis
        phinuphiAddr = (side, i : replicate psiNum 0)
        phiAddr = (side, i : 0 : replicate psiNum 0)
        nuAddr = (side, i : replicate psiNum 0)
        xAddrs = map (\ x -> (side, snd phinuphiAddr ++ x)) xs
        xphiAddrs = map (\ x -> (side, i : replicate psiNum 0 ++ x ++ [0])) xs
        phiNus = getMunuAddrsFromBase cseq phiAddr
        bgraph = makeIdGraphExceptFormulas nseq [phinuphiAddr]
        phioutergraph = makeDeqGraphWithPrefix phiNus phiAddr phinuphiAddr
        phiinnergraphs = map (makeDeqGraphWithPrefix phiNus phiAddr) xphiAddrs
        nugraphs =
            case side of
                SLeft -> []
                SRight -> map (makeDecGraph nuAddr) xAddrs
        ngraph = concat nugraphs ++ concat phiinnergraphs ++ phioutergraph ++ bgraph
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RNat var) p = do
    (ce, css, cseq) <- getCurrent p
    let existn x f =
            FApp
                (FMu "Y" (TFun TNat TProp)
                    (FFun x TNat
                        (FOr
                            f
                            (FApp (FBoundVar "Y") (FSucc (FBoundVar x)))
                            )))
                FZero
        nat =
            FMu "X" (TFun TNat TProp)
                (FFun "x" TNat
                    (FOr
                        (FEq (FBoundVar "x") FZero)
                        (existn "x'"
                            (FAnd
                                (FEq (FBoundVar "x") (FSucc (FBoundVar "x'")))
                                (FApp (FBoundVar "X") (FBoundVar "x'"))
                                ))))
    let (_, cseq1) = addFormula SLeft (FApp nat (FFreeVar var)) cseq
    nseq <- case Map.lookup var (sfv cseq) of
        Nothing -> return $ declFreeVar var TNat cseq1
        Just TNat -> return $ cseq1
        Just _ -> Nothing
    let ngraph = makeIdGraph cseq
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RP1 i) p = do
    (ce, css, cseq) <- getCurrent p
    FEq (FSucc _) FZero <- getFormula cseq (SLeft, [i])
    let noes = Set.delete ce (openEdges p)
        nses = Map.insert ce (SequentEdge SlEnd css) (sequentEdges p)
    return $ p {
        sequentEdges = nses,
        openEdges = noes,
        curEdge = Set.lookupMin noes
        }

appRule' (RP2 i) p = do
    (ce, css, cseq) <- getCurrent p
    FEq (FSucc sf) (FSucc tf) <- getFormula cseq (SLeft, [i])
    nseq <- replaceFormula SLeft i (FEq sf tf) cseq
    let ngraph = makeIdGraph cseq
        nses = sequentEdges p
            & Map.insert ce (SequentEdge SlOpen ((nseq, ngraph) : css))
    return $ p {
        sequentEdges = nses
        }

appRule' (RBackEdge edge index lpairs rpairs) p = do
    (ce, css, cseq) <- getCurrent p
    SequentEdge _ nss <- Map.lookup edge (sequentEdges p)
    (nseq, _) <- maybeAt nss (length nss - index - 1)
    let ls1 = Set.fromList $ map snd lpairs
        rs1 = Set.fromList $ map snd rpairs
        ls2 = Set.fromList $ Map.keys $ sleft nseq
        rs2 = Set.fromList $ Map.keys $ sright nseq
    guard (length lpairs == Set.size ls1)
    guard (length rpairs == Set.size rs1)
    guard (ls1 == ls2)
    guard (rs1 == rs2)
    let getFormulaPair s (c, n) = do
            cf <- getFormula cseq (s, [c])
            nf <- getFormula nseq (s, [n])
            return (cf, nf)
    lfpairs <- mapM (getFormulaPair SLeft) lpairs
    rfpairs <- mapM (getFormulaPair SRight) rpairs
    guard (all (uncurry (==)) lfpairs)
    guard (all (uncurry (==)) rfpairs)
    let lgraphs = map (\ (c, n) -> makeDeqGraphWithPrefix (getMunuAddrsFromBase nseq (SLeft, [n])) (SLeft, [c]) (SLeft, [n])) lpairs
        rgraphs = map (\ (c, n) -> makeDeqGraphWithPrefix (getMunuAddrsFromBase nseq (SRight, [n])) (SRight, [c]) (SRight, [n])) rpairs
        ngraph = concat lgraphs ++ concat rgraphs :: Graph
        nses = sequentEdges p
            & Map.insert ce (SequentEdge (SlBackEdge edge index) css)
        noes = Set.delete ce (openEdges p)
        nbes = Map.alter (\ mm -> Just $
                case mm of
                    Nothing -> Map.singleton ce ngraph
                    Just m -> Map.insert ce ngraph m
            ) edge (backEdges p)
    return $ p {
        sequentEdges = nses,
        openEdges = noes,
        curEdge = Set.lookupMin noes,
        backEdges = nbes
        }

appRule' (RSwitch i) p = do
    guard (Set.member i (openEdges p))
    return $ p {
        curEdge = Just i
        }

filterGraphs :: Int -> Map (Int, Int) Graph -> Map (Int, Int) Graph
filterGraphs edge grs =
    Map.filterWithKey (\ (i1, i2) _ -> Set.member i1 edges && Set.member i2 edges) grs
    where
        clsst :: (Int -> Set Int) -> (Set Int, Set Int) -> (Set Int, Set Int)
        clsst f (isdone, isnot) =
            let isdone' = Set.union isdone isnot
                is1 = Set.unions (Set.map f isnot)
                isnot' = Set.difference is1 isdone'
            in (isdone', isnot')
        cls :: (Int -> Set Int) -> Int -> Set Int
        cls f i = fst $ until (Set.null . snd) (clsst f) (Set.empty, Set.singleton i)
        stog :: Map Int (Set Int)
        stog = Map.map Set.fromList (toMultiMap (Map.keys grs))
        gtos :: Map Int (Set Int)
        gtos = Map.map Set.fromList (toMultiMap (map (\ (a, b) -> (b, a)) (Map.keys grs)))
        makef :: Map Int (Set Int) -> Int -> Set Int
        makef to i =
            case Map.lookup i to of
                Nothing -> Set.empty
                Just s -> s
        edges :: Set Int
        edges = Set.intersection (cls (makef stog) edge) (cls (makef gtos) edge)

makeSctInput :: Map (Int, Int) Graph -> String
makeSctInput gs =
    "{" ++ concat (map graphToStr (Map.toList gs)) ++ "}"
    where
        addrToStr :: (Side, [Int]) -> String
        addrToStr (side, is) =
            case side of
                SLeft -> 'l' : concat (map show is)
                SRight -> 'r' : concat (map show is)
        edgeToStr :: ((Side, [Int]), (Side, [Int]), SctSizeRel) -> String
        edgeToStr (a1, a2, r) =
            let rs = case r of
                    SsDec -> "dec"
                    SsDeq -> "deq"
            in "(" ++ addrToStr a1 ++ " " ++ addrToStr a2 ++ " " ++ rs ++ ")"
        graphToStr :: ((Int, Int), Graph) -> String
        graphToStr ((i, j), g) =
            "(" ++ show i ++ " " ++ show j ++ " {" ++ concat (map edgeToStr g) ++ "})"

appRule :: Rule -> Proof -> Maybe (Maybe String, Proof)
appRule r p = do
    ce <- curEdge p
    p1 <- appRule' r p
    SequentEdge sl sgs <- Map.lookup ce (sequentEdges p1)
    let p2 = case sl of
            SlBranch e1 e2 -> p1 {
                sequentEdgesFrom = (sequentEdgesFrom p1)
                    & Map.insert e1 ce
                    & Map.insert e2 ce
                }
            _ -> p1
    p3 <-
        if sl == SlOpen || sl == SlEnd then
            return p2
        else do
            from <- Map.lookup ce (sequentEdgesFrom p2)
            let edgeGraph = composeGraphs $ reverse $ map snd sgs
                bes =
                    case Map.lookup ce (backEdges p2) of
                        Nothing -> []
                        Just m -> Map.toList m
                makeGraphKvs (befrom, begraph) = do
                    SequentEdge (SlBackEdge _ index) _ <- Map.lookup befrom (sequentEdges p2)
                    let elemGraphs = reverse $ map snd $ take (length sgs - index - 1) sgs
                    return ((befrom, ce), composeGraphs (begraph : elemGraphs))
                cgraphs = graphs p2
            insertedKeyGraphs1 <- mapM makeGraphKvs bes
            let insertedKeyGraphs2 = ((from, ce), edgeGraph) : insertedKeyGraphs1
            insertedKeyGraphs <-
                case sl of
                    SlBackEdge to index -> do
                        begraphs <- Map.lookup to (backEdges p2)
                        begraph <- Map.lookup ce begraphs
                        SequentEdge tosl tosgs <- Map.lookup to (sequentEdges p2)
                        if tosl == SlOpen || tosl == SlEnd then
                            Just insertedKeyGraphs2
                        else
                            let elemGraphs = reverse $ map snd $ take (length tosgs - index - 1) tosgs
                                graph = composeGraphs (begraph : elemGraphs)
                            in Just (((ce, to), graph) : insertedKeyGraphs2)
                    _ -> Just insertedKeyGraphs2
            let ngraphs = foldr (uncurry Map.insert) cgraphs insertedKeyGraphs
            return $ p2 {
                graphs = ngraphs
                }
    let sctInput =
            case sl of
                SlBackEdge _ _ ->
                    let gs = filterGraphs ce (graphs p3)
                    in
                        if Map.null gs then
                            Nothing
                        else
                            Just (makeSctInput gs)
                _ -> Nothing
    return (sctInput, p3)

initProof :: ProofInit -> Maybe Proof
initProof pinit = do
    guard $ isUniqueList (map fst (piFv pinit))
    let sq0 = List.foldr (uncurry declFreeVar) initSequent (piFv pinit)
    guard $ all (\ f -> isWellTyped f (sfv sq0)) (piLeft pinit)
    guard $ all (\ f -> isWellTyped f (sfv sq0)) (piRight pinit)
    guard $ all (\ f -> calcType f (sfv sq0) == Just TProp) (piLeft pinit)
    guard $ all (\ f -> calcType f (sfv sq0) == Just TProp) (piRight pinit)
    let (_, sq1) = List.foldl' (\ (_, sq) f -> addFormula SLeft f sq) (0, sq0) (piLeft pinit)
        (_, sq2) = List.foldl' (\ (_, sq) f -> addFormula SRight f sq) (0, sq1) (piRight pinit)
        nsq = pruneFreeVar sq2
    return $ Proof {
        sequentEdges = Map.singleton 1 (SequentEdge SlOpen [(nsq, makeIdGraph nsq)]),
        openEdges = Set.singleton 1,
        curEdge = Just 1,
        backEdges = Map.empty,
        sequentEdgesFrom = Map.singleton 1 0,
        graphs = Map.empty
        }
