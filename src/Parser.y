{
module Parser (parseInit, parseRule, parseFormula) where

import Control.Monad
import Lexer
import Proof
import Sequent
import Formula
}

%name iparseInit Init
%name iparseRule Rule
%name iparseFormula Formula
%tokentype { Token }
%monad { Maybe }
%error { parseError }

%token
    "{"                                 { TokrLbrace }
    "}"                                 { TokrRbrace }
    ","                                 { TokrComma }
    init                                { TokrInit }
    axiom                               { TokrAxiom }
    cut                                 { TokrCut }
    wkl                                 { TokrWkl }
    wkr                                 { TokrWkr }
    ctrl                                { TokrCtrl }
    ctrr                                { TokrCtrr }
    subst                               { TokrSubst }
    mono                                { TokrMono }
    eql                                 { TokrEql }
    eqr                                 { TokrEqr }
    orl                                 { TokrOrl }
    orr                                 { TokrOrr }
    andl                                { TokrAndl }
    andr                                { TokrAndr }
    funl                                { TokrFunl }
    funr                                { TokrFunr }
    mul                                 { TokrMul }
    mur                                 { TokrMur }
    nul                                 { TokrNul }
    nur                                 { TokrNur }
    nat                                 { TokrNat }
    p1                                  { TokrP1 }
    p2                                  { TokrP2 }
    backedge                            { TokrBackedge }
    switch                              { TokrSwitch }
    paddr                               { TokrPartAddr $$ }
    faddr                               { TokrFullAddr $$ }
    int                                 { TokrInt $$ }
    ":"                                 { TokfColon }
    "("                                 { TokfLpar }
    ")"                                 { TokfRpar }
    "="                                 { TokfEq }
    "\\/"                               { TokfOr }
    "/\\"                               { TokfAnd }
    "\\"                                { TokfLambda }
    "."                                 { TokfDot }
    "->"                                { TokfArrow }
    N                                   { TokfTNat }
    P                                   { TokfTProp }
    Z                                   { TokfZero }
    S                                   { TokfSucc }
    m                                   { TokfMu }
    n                                   { TokfNu }
    fvar                                { TokfFreeVar $$ }
    bvar                                { TokfBoundVar $$ }

%left PREC_FUN
%left "\\/"
%left "/\\"
%left "="

%%

Init
    : init "{" Formulas "}" "{" Formulas "}" "{" VarTypes "}"   { ($3, $6, $9) }

Rule
    : axiom int int                                             { RAxiom $2 $3 }
    | cut "{" Formula "}" "{" VarTypes "}"                      { RCut $3 $6 }
    | wkl int                                                   { RWk SLeft $2}
    | wkr int                                                   { RWk SRight $2 }
    | ctrl int                                                  { RCtr SLeft $2 }
    | ctrr int                                                  { RCtr SRight $2 }
    | subst "{" FullAddrs "}" fvar                              { RSubst $3 $5 }
    | mono int int "{" PartAddrs "}" "{" Vars "}"               { RMono $2 $3 $5 $8 }
    | eql int "{" FullAddrs "}" "{" FullAddrs "}"               { REqL $2 $4 $7 }
    | eqr int                                                   { REqR $2 }
    | orl int                                                   { ROr SLeft $2 }
    | orr int                                                   { ROr SRight $2 }
    | andl int                                                  { RAnd SLeft $2 }
    | andr int                                                  { RAnd SRight $2 }
    | funl int                                                  { RFun SLeft $2 }
    | funr int                                                  { RFun SRight $2 }
    | mul int                                                   { RMu SLeft $2 }
    | mur int                                                   { RMu SRight $2 }
    | nul int                                                   { RNu SLeft $2 }
    | nur int                                                   { RNu SRight $2 }
    | nat fvar                                                  { RNat $2 }
    | p1 int                                                    { RP1 $2 }
    | p2 int                                                    { RP2 $2 }
    | backedge int int "{" IntPairs "}" "{" IntPairs "}"        { RBackEdge $2 $3 $5 $8 }
    | switch int                                                { RSwitch $2 }

Formulas
    : {- empty -}                       { [] }
    | Formula                           { [$1] }
    | Formula "," Formulas              { $1 : $3 }

Vars
    : {- empty -}                       { [] }
    | fvar                              { [$1] }
    | fvar "," Vars                     { $1 : $3 }

VarTypes
    : {- empty -}                       { [] }
    | fvar ":" Type                     { [($1, $3)] }
    | fvar ":" Type "," VarTypes        { ($1, $3) : $5 }

FullAddrs
    : {- empty -}                       { [] }
    | faddr                             { [$1] }
    | faddr "," FullAddrs               { $1 : $3 }

PartAddrs
    : {- empty -}                       { [] }
    | paddr                             { [$1] }
    | paddr "," PartAddrs               { $1 : $3 }

IntPairs
    : {- empty -}                       { [] }
    | int int                           { [($1, $2)] }
    | int int "," IntPairs              { ($1, $2) : $4 }

Formula
    : Formula1                          { $1 }
    | Formula "=" Formula               { FEq $1 $3 }
    | Formula "\\/" Formula             { FOr $1 $3 }
    | Formula "/\\" Formula             { FAnd $1 $3 }
    | "\\" bvar ":" Type "." Formula
        %prec PREC_FUN                  { FFun $2 $4 $6 }
    | m bvar ":" Type "." Formula
        %prec PREC_FUN                  { FMu $2 $4 $6 }
    | n bvar ":" Type "." Formula
        %prec PREC_FUN                  { FNu $2 $4 $6 }

Formula1
    : Formula2                          { $1 }
    | S Formula2                        { FSucc $2 }
    | Formula1 Formula2                 { FApp $1 $2 }

Formula2
    : fvar                              { FFreeVar $1 }
    | bvar                              { FBoundVar $1 }
    | Z                                 { FZero }
    | "(" Formula ")"                   { $2 }

Type
    : Type1                             { $1 }
    | Type1 "->" Type                   { TFun $1 $3 }

Type1
    : N                                 { TNat }
    | P                                 { TProp }
    | "(" Type ")"                      { $2 }

{
parseError :: [Token] -> Maybe a
parseError tokens = Nothing

parseInit :: String -> Maybe ([Formula], [Formula], [(Var, Type)])
parseInit = lexer >=> iparseInit

parseRule :: String -> Maybe Rule
parseRule = lexer >=> iparseRule

parseFormula :: String -> Maybe Formula
parseFormula = lexer >=> iparseFormula
}
