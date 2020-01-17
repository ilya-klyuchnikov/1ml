(*
 * (c) 2014 Andreas Rossberg
 *)

open Source

type var = string

type eff =
  | Pure
  | Impure

type typ =
  | PathT of exp
  | PrimT of string
  | TypT
  | StrT of dec
  | FunT of var * typ * typ * eff
  | PackT of typ
  | LikeT of exp
  | WithT of typ * var list * exp

and dec =
  | EmptyD
  | SeqD of dec * dec
  | VarD of var * typ
  | InclD of typ

and exp =
  | VarE of var
  | PrimE of Prim.const
  | TypE of typ
  | StrE of bind
  | FunE of var * typ * exp
  | PackE of var * typ
  | IfE of var * exp * exp * typ
  | DotE of exp * var
  | AppE of var * var
  | UnpackE of var * typ

and bind =
  | EmptyB
  | SeqB of bind * bind
  | VarB of var * exp
  | InclB of exp


let var_counts = ref []
let var s =
  let count = try List.assoc s !var_counts with Not_found ->
    let count = ref 0 in var_counts := (s, count) :: !var_counts; count
  in incr count; s ^ "$" ^ string_of_int !count


(* Sugar *)

let rec tupT(ts) = StrT(tupT' 1 ts)
and tupT' n = function
  | [] -> EmptyD
  | t::ts ->
    let x' = "_" ^ string_of_int n in
    let d = tupT' (n + 1) ts in
    SeqD(VarD(x', t), d)

let rec tupE(es) = StrE(tupE' 1 es)
and tupE' n = function
  | [] -> EmptyB
  | e::es ->
    let x' = "_" ^ string_of_int n in
    let b = tupE' (n + 1) es in
    SeqB(VarB(x', e), b)

let rec funT(ps, t, f) = (funT'(ps, t, f))
and funT'(ps, t, f) =
  match ps with
  | [] -> t
  | p::ps' ->
    FunT(fst p, snd p, funT'(ps', t, f), f)

let rec funE(ps, e) = (funE'(ps, e))
and funE'(ps, e) =
  match ps with
  | [] -> e
  | p::ps' -> FunE(fst p, snd p, funE'(ps', e))

let letE(b, e) =
  let x' = var "let" in
  let b2 = VarB(x', e) in
  DotE(StrE(SeqB(b, b2)), x')

let letT(b, t) = PathT(letE(b, TypE(t)))
let letD(b, d) = InclD(letT(b, StrT(d)))
let letB(b, b') = InclB(letE(b, StrE(b')))

let doE(e) = letE(VarB("_", e), tupE[])
let doB(e) = letB(VarB("_", e), EmptyB)

let ifE(e1, e2, e3, t) =
  match e1 with
  | VarE(x) -> IfE(x, e2, e3, t)
  | _ ->
    let x' = var "if" in
    let e = IfE(x', e2, e3, t) in
    letE(VarB(x', e1), e)

let orE(e1, e2) =
  ifE(e1, PrimE(Prim.BoolV(true)), e2,
    PrimT("bool"))
let andE(e1, e2) =
  ifE(e1, e2, PrimE(Prim.BoolV(false)),
    PrimT("bool"))

let appE(e1, e2) =
  match e1, e2 with
  | VarE(x1), VarE(x2) -> AppE(x1, x2)
  | VarE(x1), _ ->
    let x2' = var "app2" in
    letE(VarB(x2', e2), AppE(x1, x2'))
  | _, VarE(x2) ->
    let x1' = var "app1" in
    letE(VarB(x1', e1), AppE(x1', x2))
  | _, _ ->
    let x1' = var "app1" in
    let x2' = var "app2" in
    let b1 = VarB(x1', e1) in
    let b2 = VarB(x2', e2) in
    let b = SeqB(b1, b2) in
    letE(b, AppE(x1', x2'))

let packE(e, t) =
  match e with
  | VarE(x) -> PackE(x, t)
  | _ ->
    let x' = var "pack" in
    letE(VarB(x', e), PackE(x', t))

let unpackE(e, t) =
  match e with
  | VarE(x) -> UnpackE(x, t)
  | _ ->
    let x' = var "pack" in
    letE(VarB(x', e), UnpackE(x', t))

let annotE(e, t) =
  let x' = var "annot" in
  appE(FunE(x', t, VarE(x')), e)

let sealE(e, t) =
  unpackE(packE(e, t), t)   (* TODO: clone t! *)


(* String conversion *)

let node label = function
  | [] -> label
  | args -> label ^ "(" ^ String.concat ", " args ^ ")"

let label_of_eff p =
  match p with
  | Pure -> "P"
  | Impure -> "I"

let label_of_typ t =
  match t with
  | PathT _ -> "PathT"
  | PrimT _ -> "PrimT"
  | TypT -> "TypT"
  | StrT _ -> "StrT"
  | FunT _ -> "FunT"
  | PackT _ -> "PackT"
  | LikeT _ -> "LikeT"
  | WithT _ -> "WithT"

let label_of_dec d =
  match d with
  | EmptyD -> "EmptyD"
  | SeqD _ -> "SeqD"
  | VarD _ -> "VarD"
  | InclD _ -> "InclD"

let label_of_exp e =
  match e with
  | VarE _ -> "VarE"
  | PrimE _ -> "PrimE"
  | TypE _ -> "TypT"
  | StrE _ -> "StrE"
  | FunE _ -> "FunE"
  | PackE _ -> "PackE"
  | IfE _ -> "IfE"
  | DotE _ -> "DotE"
  | AppE _ -> "AppE"
  | UnpackE _ -> "UnpackE"

let label_of_bind b =
  match b with
  | EmptyB -> "EmptyB"
  | SeqB _ -> "SeqB"
  | VarB _ -> "VarB"
  | InclB _ -> "InclB"


let string_of_var x = x

let string_of_eff p = label_of_eff p

let rec string_of_typ t =
  let node' = node (label_of_typ t) in
  match t with
  | PathT(e) -> node' [string_of_exp e]
  | PrimT(n) -> node' ["\"" ^ n ^"\""]
  | TypT -> node' []
  | StrT(d) -> node' [string_of_dec d]
  | FunT(x, t1, t2, p) ->
    node' [string_of_var x; string_of_typ t1; string_of_typ t2; string_of_eff p]
  | PackT(t) -> node' [string_of_typ t]
  | LikeT(e) -> node' [string_of_exp e]
  | WithT(t, xs, e) ->
    node' ([string_of_typ t] @ List.map string_of_var xs @ [string_of_exp e])

and string_of_dec d =
  let node' = node (label_of_dec d) in
  match d with
  | EmptyD -> node' []
  | SeqD(d1, d2) -> node' [string_of_dec d1; string_of_dec d2]
  | VarD(x, t) -> node' [string_of_var x; string_of_typ t]
  | InclD(t) -> node' [string_of_typ t]

and string_of_exp e =
  let node' = node (label_of_exp e) in
  match e with
  | VarE(x) -> node' [string_of_var x]
  | PrimE(c) -> node' [Prim.string_of_const c]
  | TypE(t) -> node' [string_of_typ t]
  | StrE(b) -> node' [string_of_bind b]
  | FunE(x, t, e) -> node' [string_of_var x; string_of_typ t; string_of_exp e]
  | PackE(x, t) -> node' [string_of_var x; string_of_typ t]
  | IfE(x, e1, e2, t) ->
    node' [string_of_var x; string_of_exp e1; string_of_exp e2; string_of_typ t]
  | DotE(e, x) -> node' [string_of_exp e; string_of_var x]
  | AppE(x1, x2) -> node' [string_of_var x1; string_of_var x2]
  | UnpackE(x, t) -> node' [string_of_var x; string_of_typ t]

and string_of_bind b =
  let node' = node (label_of_bind b) in
  match b with
  | EmptyB -> node' []
  | SeqB(b1, b2) -> node' [string_of_bind b1; string_of_bind b2]
  | VarB(x, e) -> node' [string_of_var x; string_of_exp e]
  | InclB(e) -> node' [string_of_exp e]
