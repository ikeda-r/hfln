{
module Lexer (lexer, Token(..)) where

import Sequent (Side(..))
}

%wrapper "basic"

@int = [0-9]+
@ident = [a-zA-Z][a-zA-Z0-9']*
@partaddr = \#[01]+
@fulladdr = [lr][0-9]+\#[01]+

tokens :-

    $white+                         ;
    "{"                             { \ _ -> Just TokrLbrace }
    "}"                             { \ _ -> Just TokrRbrace }
    ","                             { \ _ -> Just TokrComma }
    init                            { \ _ -> Just TokrInit }
    axiom                           { \ _ -> Just TokrAxiom }
    cut                             { \ _ -> Just TokrCut }
    wkl                             { \ _ -> Just TokrWkl }
    wkr                             { \ _ -> Just TokrWkr }
    ctrl                            { \ _ -> Just TokrCtrl }
    ctrr                            { \ _ -> Just TokrCtrr }
    subst                           { \ _ -> Just TokrSubst }
    mono                            { \ _ -> Just TokrMono }
    eql                             { \ _ -> Just TokrEql }
    eqr                             { \ _ -> Just TokrEqr }
    orl                             { \ _ -> Just TokrOrl }
    orr                             { \ _ -> Just TokrOrr }
    andl                            { \ _ -> Just TokrAndl }
    andr                            { \ _ -> Just TokrAndr }
    funl                            { \ _ -> Just TokrFunl }
    funr                            { \ _ -> Just TokrFunr }
    mul                             { \ _ -> Just TokrMul }
    mur                             { \ _ -> Just TokrMur }
    nul                             { \ _ -> Just TokrNul }
    nur                             { \ _ -> Just TokrNur }
    nat                             { \ _ -> Just TokrNat }
    p1                              { \ _ -> Just TokrP1 }
    p2                              { \ _ -> Just TokrP2 }
    backlink                        { \ _ -> Just TokrBackedge }
    switch                          { \ _ -> Just TokrSwitch }
    @partaddr                       { \ s -> Just (TokrPartAddr (parsePartAddr s)) }
    @fulladdr                       { \ s -> Just (TokrFullAddr (parseFullAddr s)) }
    @int                            { \ s -> Just (TokrInt (read s)) }
    ":"                             { \ _ -> Just TokfColon }
    "("                             { \ _ -> Just TokfLpar }
    ")"                             { \ _ -> Just TokfRpar }
    "="                             { \ _ -> Just TokfEq }
    "\/"                            { \ _ -> Just TokfOr }
    "/\"                            { \ _ -> Just TokfAnd }
    "\"                             { \ _ -> Just TokfLambda }
    "."                             { \ _ -> Just TokfDot }
    "->"                            { \ _ -> Just TokfArrow }
    N                               { \ _ -> Just TokfTNat }
    P                               { \ _ -> Just TokfTProp }
    Z                               { \ _ -> Just TokfZero }
    S                               { \ _ -> Just TokfSucc }
    m                               { \ _ -> Just TokfMu }
    n                               { \ _ -> Just TokfNu }
    \$@ident                        { \ (_ : s) -> Just (TokfFreeVar s) }
    \@@ident                        { \ (_ : s) -> Just (TokfBoundVar s) }
    .                               { \ _ -> Nothing}

{
data Token =
    TokrLbrace
    | TokrRbrace
    | TokrComma
    | TokrInit
    | TokrAxiom
    | TokrCut
    | TokrWkl
    | TokrWkr
    | TokrCtrl
    | TokrCtrr
    | TokrSubst
    | TokrMono
    | TokrEql
    | TokrEqr
    | TokrOrl
    | TokrOrr
    | TokrAndl
    | TokrAndr
    | TokrFunl
    | TokrFunr
    | TokrMul
    | TokrMur
    | TokrNul
    | TokrNur
    | TokrNat
    | TokrP1
    | TokrP2
    | TokrBackedge
    | TokrSwitch
    | TokrPartAddr [Int]
    | TokrFullAddr (Side, [Int])
    | TokrInt Int
    | TokfColon
    | TokfLpar
    | TokfRpar
    | TokfEq
    | TokfOr
    | TokfAnd
    | TokfLambda
    | TokfDot
    | TokfArrow
    | TokfTNat
    | TokfTProp
    | TokfZero
    | TokfSucc
    | TokfMu
    | TokfNu
    | TokfFreeVar String
    | TokfBoundVar String
    deriving (Show)

parsePartAddr :: String -> [Int]
parsePartAddr = map (\ c ->
    case c of
        '0' -> 0
        '1' -> 1
        _ -> error "Lexer.parsePartAddr"
    )

parseFullAddr :: String -> (Side, [Int])
parseFullAddr (sc : str) =
    let side =
            case sc of
                'l' -> SLeft
                'r' -> SRight
                _ -> error "parseFullAddr"
        (istr, _ : pastr) = break (== '#') str
        i = read istr
        pa = parsePartAddr pastr
    in (side, i : pa)

lexer :: String -> Maybe [Token]
lexer s = sequence (alexScanTokens s)
}
