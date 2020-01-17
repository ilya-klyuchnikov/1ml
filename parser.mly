/*
 * (c) 2014 Andreas Rossberg
 */

%{
open Source
open Syntax

let position_to_pos position =
  { file = position.Lexing.pos_fname;
    line = position.Lexing.pos_lnum;
    column = position.Lexing.pos_cnum - position.Lexing.pos_bol
  }

let positions_to_region position1 position2 =
  { left = position_to_pos position1;
    right = position_to_pos position2
  }

let at () =
  positions_to_region (Parsing.symbol_start_pos ()) (Parsing.symbol_end_pos ())
let ati i =
  positions_to_region (Parsing.rhs_start_pos i) (Parsing.rhs_end_pos i)

let parse_error s = raise (Source.RegionError (Source.nowhere_region, s))
%}

%token TRUE FALSE HOLE PRIMITIVE
%token FUN LET LOCAL IN DO PACK UNPACK TYPE LIKE INCLUDE
%token IF THEN ELSE OR AND
%token EQUAL COLON SEAL ARROW DARROW
%token WITH
%token LPAR RPAR
%token LBRACE RBRACE
%token DOT
%token COMMA SEMI

%token EOF

%token<string> NAME
%token<string> SYM
%token<string> TEXT
%token<int> NUM

%start prog
%type<Syntax.exp> prog

%%

sym :
  | SYM
    { $1 }
;
name :
  | NAME
    { $1 }
  | LPAR sym RPAR
    { $2 }
;
namelist :
  | name
    { $1::[] }
  | name DOT namelist
    { $1::$3 }
;

head :
  | name
    { $1 }
  | HOLE
    { "_" }
;
typparam :
  | LPAR head COLON typ RPAR
    { ($2, $4) }
  | LPAR TYPE head RPAR
    { ($3, TypT) }
;
param :
  | typparam
    { $1 }
  | head
    { ($1, TypT) }
;
paramlist :
  |
    { [] }
  | param paramlist
    { $1::$2 }
;
arrow :
  | ARROW
    { Impure }
  | DARROW
    { Pure }
;

attyp :
  | pathexp
    { PathT($1) }
  | PRIMITIVE TEXT
    { PrimT($2) }
  | TYPE
    { TypT }
  | LBRACE dec RBRACE
    { StrT($2) }
  | LPAR RPAR
    { StrT(EmptyD) }
  | LPAR typlist RPAR
    { match $2 with [t] -> t | ts -> tupT(ts) }
;
apptyp :
  | attyp
    { $1 }
;
withtyp :
  | apptyp
    { $1 }
  | withtyp WITH namelist paramlist EQUAL pathexp
    { WithT($1, $3, funE($4, $6)) }
  | withtyp WITH TYPE namelist paramlist EQUAL apptyp
    { WithT($1, $4, funE($5, TypE($7))) }
;
typ :
  | withtyp
    { $1 }
  | typparam arrow typ
    { funT([$1], $3, $2) }
  | withtyp arrow typ
    { funT([("_", $1)], $3, $2) }
  | PACK typ
    { PackT($2) }
  | LIKE pathexp
    { LikeT($2) }
  | LET bind IN typ
    { letT($2, $4) }
;
typlist :
  | typ
    { $1::[] }
  | typ COMMA typlist
    { $1::$3 }
;

atdec :
  | head paramlist COLON typ
    { VarD($1, funT($2, $4, Pure)) }
  | TYPE head paramlist
    { VarD($2, funT($3, TypT, Pure)) }
  | head paramlist EQUAL exp
    { VarD($1, funT($2, LikeT($4), Pure)) }
  | TYPE head paramlist EQUAL typ
    { VarD($2, funT($3, LikeT(TypE($5)), Pure)) }
  | INCLUDE typ
    { InclD($2) }
  | LOCAL bind IN atdec
    { letD($2, $4) }
  | LPAR dec RPAR
    { $2 }
;
dec :
  |
    { EmptyD }
  | atdec
    { $1 }
  | atdec SEMI dec
    { SeqD($1, $3) }
;

atpathexp :
  | name
    { VarE($1) }
;
apppathexp :
  | atpathexp
    { $1 }
  | apppathexp atexp
    { appE($1, $2) }
  | apppathexp DOT name
    { DotE($1, $3) }
  | apppathexp DOT NUM
    { DotE($1, ("_" ^ string_of_int $3)) }
;
infpathexp :
  | apppathexp
    { $1 }
  | sym apppathexp
    { appE(VarE($1), $2) }
  | infpathexp sym apppathexp
    { appE(VarE($2), tupE[$1; $3]) }
;
pathexp :
  | infpathexp
    { $1 }
;

atexp :
  | name
    { VarE($1) }
  | PRIMITIVE TEXT
    { match Prim.fun_of_string $2 with
      | Some f -> PrimE(Prim.FunV f)
      | None -> parse_error ("unknown primitive \"" ^ $2 ^ "\"") }
  | NUM
    { PrimE(Prim.IntV($1)) }
  | TEXT
    { PrimE(Prim.TextV($1)) }
  | LBRACE bind RBRACE
    { StrE($2) }
  | LPAR RPAR
    { StrE(EmptyB) }
  | LPAR explist RPAR
    { match $2 with [e] -> e | es -> tupE(es) }
;
appexp :
  | atexp
    { $1 }
  | appexp atexp
    { appE($1, $2) }
  | appexp DOT name
    { DotE($1, $3) }
  | appexp DOT NUM
    { DotE($1, ("_" ^ string_of_int $3)) }
;
infexp :
  | appexp
    { $1 }
  | sym appexp
    { appE(VarE($1), $2) }
  | infexp sym appexp
    { appE(VarE($2), tupE[$1; $3]) }
  | infexp OR appexp
    { orE($1, $3) }
  | infexp AND appexp
    { andE($1, $3) }
;
annexp :
  | infexp
    { $1 }
  | TYPE typ
    { TypE($2) }
  | annexp COLON typ
    { annotE($1, $3) }
  | annexp SEAL typ
    { sealE($1, $3) }
  | PACK infexp COLON typ
    { packE($2, $4) }
  | UNPACK infexp COLON typ
    { unpackE($2, $4) }
;
exp :
  | annexp
    { $1 }
  | FUN param paramlist DARROW exp
    { funE($2::$3, $5) }
  | IF exp THEN exp ELSE infexp COLON typ
    { ifE($2, $4, $6, $8) }
  | LET bind IN exp
    { letE($2, $4) }
  | DO exp
    { doE($2) }
;
explist :
  | exp
    { $1::[] }
  | exp COMMA explist
    { $1::$3 }
;

atbind :
  | head paramlist EQUAL exp
    { VarB($1, funE($2, $4)) }
  | head paramlist COLON typ EQUAL exp
    { VarB($1, funE($2, annotE($6, $4))) }
  | head paramlist SEAL typ EQUAL exp
    { VarB($1, funE($2, sealE($6, $4))) }
  | TYPE head paramlist EQUAL typ
    { VarB($2, funE($3, TypE($5))) }
  | INCLUDE exp
    { InclB($2) }
  | LOCAL bind IN atbind
    { letB($2, $4) }
  | DO exp
    { doB($2) }
  | LPAR bind RPAR
    { $2 }
;
bind :
  |
    { EmptyB }
  | atbind
    { $1 }
  | atbind SEMI bind
    { SeqB($1, $3) }
;

prog :
  | bind EOF
    { StrE($1) }
;

%%
