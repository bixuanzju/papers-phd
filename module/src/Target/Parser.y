{
module Target.Parser (parseExpr) where
import Data.Char (isDigit, isSpace, isAlpha)
import Data.List (stripPrefix)
import Target.Syntax
import Tokens
import Common
}


%name parser
%tokentype { Token }
%error { parseError }


%token
    castup   { TokenUp }
    castdown { TokenDown }
    pi       { TokenPi }
    let      { TokenLet }
    in       { TokenIn }
    mu       { TokenMu }
    nat      { TokenNat }
    id       { TokenSym $$ }
    digits   { TokenInt $$ }
    ':'      { TokenColon }
    '='      { TokenEq }
    '#'      { TokenSharp }
    '.'      { TokenDot }
    ','      { TokenComma }
    '['      { TokenLB }
    ']'      { TokenRB }
    '{'      { TokenLC }
    '}'      { TokenRC }
    '->'     { TokenArr }
    '('      { TokenLParen }
    ')'      { TokenRParen }
    '*'      { TokenTimes }
    '\\'     { TokenLam }
    '+'      { TokenPlus }
    '-'      { TokenMinus }


%right in
%right '.'
%right '->'
%right ']'
%right '|'
%left '+' '-'


%monad { Either String }

%%

expr : '\\' id '.' expr             { elam $2 $4 }
     | pi tele '.' expr             { epi $2 $4  }
     | mu id '.' expr               { emu $2 $4 }
     | expr ':' expr                { Anno $1 $3 }
     | expr '.' digits              { Proj $3 $1 }

     | castup '[' expr ']'          { CastUp $3 }
     | castdown '[' expr ']'        { CastDown $3 }

     -- add-on
     | expr '+' expr                  { PrimOp Add $1 $3 }
     | expr '-' expr                  { PrimOp Sub $1 $3 }
     | expr '->' expr                 { earr $1 $3 }
     | aexp                           { $1 }

aexp : aexp term                      { App $1 $2 }
     | term                           { $1 }

term : nat                            { Nat }
     | id                             { evar $1 }
     | digits                         { Lit $1 }
     | '*'                            { Star }
     | '(' expr ')'                   { $2 }
     | '(' expr ',' expr ')'          { Pair $2 $4 }
     | '(' expr '#' expr ')'          { PairTy $2 $4 }

tele : '(' id ':' expr ')'            { ($2, $4) }

{

parseError _ = Left "Parse error!"

parseExpr = parser . scanTokens

}
