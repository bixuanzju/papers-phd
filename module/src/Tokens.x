{
module Tokens where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+                       ;
  "--".*                        ;
  let                           { \s -> TokenLet }
  in                            { \s -> TokenIn }
  castup                        { \s -> TokenUp }
  castdown                      { \s -> TokenDown }
  \/\\                          { \s -> TokenPi }
  mu                            { \s -> TokenMu }
  nat                           { \s -> TokenNat }
  $digit+                       { \s -> TokenInt (read s) }
  \=                            { \s -> TokenEq }
  \:                            { \s -> TokenColon }
  \,                            { \s -> TokenComma }
  \.                            { \s -> TokenDot }
  \#                            { \s -> TokenSharp }
  \\                            { \s -> TokenLam }
  \-\>                          { \s -> TokenArr }
  \+                            { \s -> TokenPlus }
  \-                            { \s -> TokenMinus }
  \*                            { \s -> TokenTimes }
  \/                            { \s -> TokenDiv }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  \[                            { \s -> TokenLB }
  \]                            { \s -> TokenRB }
  \{                            { \s -> TokenLC }
  \}                            { \s -> TokenRC }
  \mod                          { \s -> TokenMod }
  \sig                          { \s -> TokenSig }
  \&                            { \s -> TokenAnd }
  \,\,                          { \s -> TokenMerge }
  $alpha [$alpha $digit \_ \']* { \s -> TokenSym s }

{
-- The token type:
data Token = TokenLet
           | TokenIn
           | TokenUp
           | TokenDown
           | TokenPi
           | TokenMu
           | TokenNat
           | TokenInt Int
           | TokenSym String
           | TokenEq
           | TokenLam
           | TokenArr
           | TokenColon
           | TokenComma
           | TokenDot
           | TokenPlus
           | TokenMinus
           | TokenTimes
           | TokenDiv
           | TokenLParen
           | TokenRParen
           | TokenRB
           | TokenLB
           | TokenRC
           | TokenLC
           | TokenMod
           | TokenSig
           | TokenSharp
           | TokenAnd
           | TokenMerge
           deriving (Eq,Show)

scanTokens = alexScanTokens
}
