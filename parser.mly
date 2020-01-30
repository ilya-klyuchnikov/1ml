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
%token FUN REC LET LOCAL IN DO WRAP UNWRAP TYPE INCLUDE END
%token IF THEN ELSE OR AND AS
%token EQUAL COLON SEAL ARROW DARROW
%token WITH
%token LPAR RPAR
%token LBRACE RBRACE
%token DOT AT TICK
%token COMMA SEMI

%token EOF

%token<string> NAME
%token<string> SYM
%token<string> TEXT
%token<char> CHAR
%token<int> NUM

%start prog
%type<Syntax.exp> prog

%%

label :
  | name
    { $1 }
  | sym
    { $1 }
  | NUM
    { index($1) }
;
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
annparam :
  | LPAR head COLON typ RPAR
    { let b, _ = varP($2) in (b, $4, Expl) }
  | LPAR TYPE head typparamlist RPAR
    { let b, _ = varP($3) in
      (b, funT($4, TypT, Pure),
        Expl) }
  | TICK LPAR head COLON TYPE RPAR
    { let b, _ = varP($3) in (b, TypT, Impl) }
  | TICK LPAR TYPE head RPAR
    { let b, _ = varP($4) in (b, TypT, Impl) }
  | TICK head
    { let b, _ = varP($2) in (b, TypT, Impl) }
;
param :
  | atpat
    { let b, t = (defaultP $1) in (b, t, Expl) }
  | TICK LPAR head COLON TYPE RPAR
    { let b, _ = varP($3) in (b, TypT, Impl) }
  | TICK LPAR TYPE head RPAR
    { let b, _ = varP($4) in (b, TypT, Impl) }
  | TICK head
    { let b, _ = varP($2) in (b, TypT, Impl) }
;
paramlist :
  |
    { [] }
  | param paramlist
    { $1::$2 }
;
typparamlist :
  | paramlist
    { List.map (fun p ->
        match p with
        | (b, HoleT, i) -> (b, TypT, i)
        | _ -> p
      ) $1 }
;
arrow :
  | ARROW
    { Impure }
  | DARROW
    { Pure }
;

attyp :
  | PRIMITIVE TEXT
    { PrimT($2) }
  | TYPE
    { TypT }
  | HOLE
    { HoleT }
  | LBRACE dec RBRACE
    { StrT($2) }
  | LPAR RPAR
    { StrT(EmptyD) }
  | LPAR typlist RPAR
    { match $2 with [t] -> t | ts -> tupT(ts) }
  | LPAR EQUAL exp RPAR
    { EqT($3) }
;
apptyp :
  | attyp
    { $1 }
  | pathexp
    { PathT($1) }
;
withtyp :
  | apptyp
    { $1 }
  | withtyp WITH LPAR namelist typparamlist EQUAL exp RPAR
    { WithT($1, $4, funE($5, $7)) }
  | withtyp WITH LPAR TYPE namelist typparamlist EQUAL typ RPAR
    { WithT($1, $5, funE($6, TypE($8))) }
;
typ :
  | withtyp
    { $1 }
  | annparam arrow typ
    { funT([$1], $3, $2) }
  | withtyp arrow typ
    { let b, _ = varP("_") in
      funT([(b, $1, Expl)], $3, $2) }
  | WRAP typ
    { WrapT($2) }
  | REC atpat DARROW typ
    { recT(defaultTP $2, $4) }
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
  | head typparamlist COLON typ
    { VarD($1, funT($2, $4, Pure)) }
  | TYPE head typparamlist
    { VarD($2, funT($3, TypT, Pure)) }
  | head typparamlist EQUAL exp
    { VarD($1, funT($2, EqT($4), Pure))
         }
  | TYPE head typparamlist EQUAL typ
    { VarD($2, funT($3, EqT(TypE($5)), Pure))
         }
  | INCLUDE typ
    { InclD($2) }
  | LOCAL bind IN dec END
    { letD($2, $4) }
/*
  | LPAR dec RPAR
    { $2 }
*/
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
  | HOLE
    { TypE(HoleT) }
;
apppathexp :
  | atpathexp
    { $1 }
  | apppathexp atexp
    { appE($1, $2) }
  | apppathexp DOT label
    { DotE($1, $3) }
  | AT attyp atexp
    { rollE($3, $2) }
  | AT name atexp
    { rollE($3, PathT(VarE($2))) }
  | apppathexp DOT AT attyp
    { unrollE($1, $4) }
  | apppathexp DOT AT name
    { unrollE($1, PathT(VarE($4))) }
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
  | HOLE
    { TypE(HoleT) }
  | PRIMITIVE TEXT
    { match Prim.fun_of_string $2 with
      | Some f -> PrimE(Prim.FunV f)
      | None -> parse_error ("unknown primitive \"" ^ $2 ^ "\"") }
  | NUM
    { PrimE(Prim.IntV($1)) }
  | CHAR
    { PrimE(Prim.CharV($1)) }
  | TEXT
    { PrimE(Prim.TextV($1)) }
  | LBRACE bind RBRACE
    { StrE($2) }
  | LPAR RPAR
    { StrE(EmptyB) }
  | LPAR explist RPAR
    { match $2 with [e] -> e | es -> tupE(es) }
  | LPAR expsemilist RPAR
    { seqE($2) }
  | LPAR DOT label RPAR
    { dotopE($3) }
;
appexp :
  | atexp
    { $1 }
  | appexp atexp
    { appE($1, $2) }
  | appexp DOT label
    { DotE($1, $3) }
  | AT attyp atexp
    { rollE($3, $2) }
  | AT name atexp
    { rollE($3, PathT(VarE($2))) }
  | appexp DOT AT attyp
    { unrollE($1, $4) }
  | appexp DOT AT name
    { unrollE($1, PathT(VarE($4))) }
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
  | DO appexp
    { doE($2) }
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
  | WRAP infexp COLON typ
    { wrapE($2, $4) }
  | UNWRAP infexp COLON typ
    { unwrapE($2, $4) }
;
exp :
  | annexp
    { $1 }
  | FUN param paramlist DARROW exp
    { funE($2::$3, $5) }
  | IF exp THEN exp ELSE infexp COLON typ
    { ifE($2, $4, $6, $8) }
  | IF exp THEN exp ELSE infexp
    { ifE($2, $4, $6, HoleT) }
  | LET bind IN exp
    { letE($2, $4) }
  | REC atpat DARROW exp
    { recE(defaultP $2, $4) }
;
explist :
  | exp
    { $1::[] }
  | exp COMMA explist
    { $1::$3 }
;
expsemilist :
  | exp SEMI
    { $1::[] }
  | exp SEMI exp
    { $1::$3::[] }
  | exp SEMI expsemilist
    { $1::$3 }
;

atbind :
  | head param paramlist EQUAL exp
    { VarB($1, funE($2::$3, $5)) }
  | head param paramlist COLON typ EQUAL exp
    { VarB($1, funE($2::$3, annotE($7, $5))) }
  | head paramlist SEAL typ EQUAL exp
    { VarB($1, funE($2, sealE($6, $4))) }
  | pat EQUAL exp
    { patB($1, $3) }
  | name
    { VarB($1, VarE($1)) }
  | TYPE head typparamlist EQUAL typ
    { VarB($2, funE($3, TypE($5))) }
  | INCLUDE exp
    { InclB($2) }
  | LOCAL bind IN bind END
    { letB($2, $4) }
  | DO exp
    { doB($2) }
/*
  | LPAR bind RPAR
    { $2 }
*/
;
bind :
  |
    { EmptyB }
  | atbind
    { $1 }
  | atbind SEMI bind
    { SeqB($1, $3) }
;

atpat :
  | head
    { if $1 = "_" then holeP else varP($1) }
  | LBRACE decon RBRACE
    { strP($2) }
  | LPAR RPAR
    { strP([]) }
  | LPAR patlist RPAR
    { match $2 with [p] -> p | ps -> tupP(ps) }
  | LPAR TYPE name typparamlist RPAR
    { annotP(varP($3),
        funT($4, TypT, Pure)) }
;
apppat :
  | atpat
    { $1 }
  | AT attyp atpat
    { rollP($3, $2) }
  | AT name atpat
    { rollP($3, PathT(VarE($2))) }
;
annpat :
  | apppat
    { $1 }
  | annpat COLON typ
    { annotP($1, $3) }
  | WRAP apppat COLON typ
    { wrapP($2, $4) }
;
pat :
  | annpat
    { $1 }
  | annpat AS annpat
    { asP($1, $3) }
;
patlist :
  | pat
    { $1::[] }
  | pat COMMA patlist
    { $1::$3 }
;

atdecon :
  | name EQUAL pat
    { ($1, $3) }
  | name
    { ($1, varP($1)) }
  | name COLON typ EQUAL pat
    { ($1, annotP($5, $3)) }
  | name COLON typ
    { ($1, annotP(varP($1), $3)) }
  | TYPE name typparamlist
    { ($2, annotP(varP($2),
        funT($3, TypT, Pure))) }
/*
  | LPAR decon RPAR
    { $2 }
*/
;
decon :
  |
    { [] }
  | atdecon
    { $1 :: [] }
  | atdecon SEMI decon
    { $1 :: $3 }
;

prog :
  | bind EOF
    { StrE($1) }
;

%%
