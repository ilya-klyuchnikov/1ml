(*
 * (c) 2014 Andreas Rossberg
 *)

open Source

type var = string

and impl =
  | Impl
  | Expl

and eff =
  | Pure
  | Impure

and typ =
  | PathT of exp
  | PrimT of string
  | TypT
  | HoleT
  | StrT of dec
  | FunT of var * typ * typ * eff * impl
  | WrapT of typ
  | EqT of exp
  | AsT of typ * typ
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
  | FunE of var * typ * exp * impl
  | WrapE of var * typ
  | RollE of var * typ
  | IfE of var * exp * exp * typ
  | DotE of exp * var
  | AppE of var * var
  | UnwrapE of var * typ
  | UnrollE of var * typ
  | RecE of var * typ * exp

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

let index n = "_" ^ string_of_int n


(* Sugar *)

let letE(b, e) =
  let x' = var "let" in
  let b2 = VarB(x', e) in
  DotE(StrE(SeqB(b, b2)), x')

let letT(b, t) = PathT(letE(b, TypE(t)))
let letD(b, d) = InclD(letT(b, StrT(d)))
let letB(b, b') = InclB(letE(b, StrE(b')))

let rec tupT(ts) = StrT(tupT' 1 ts)
and tupT' n = function
  | [] -> EmptyD
  | t::ts ->
    let d = tupT' (n + 1) ts in
    SeqD(VarD((index n), t), d)

let rec tupE(es) = StrE(tupE' 1 es)
and tupE' n = function
  | [] -> EmptyB
  | e::es ->
    let b = tupE' (n + 1) es in
    SeqB(VarB((index n), e), b)

let rec funT(ps, t, f) = (funT'(ps, t, f))
and funT'(ps, t, f) =
  match ps with
  | [] -> t
  | p::ps' ->
    let (b, t1, i) = p in
    let t2 = funT'(ps', t, f) in
    let x, t2' =
      match b with
      | EmptyB -> "_", t2
      | VarB(x, VarE("$")) -> x, t2
      | _ -> "$", letT(b, t2)
    in FunT(x, t1, t2', f, i)

let rec funE(ps, e) = (funE'(ps, e))
and funE'(ps, e) =
  match ps with
  | [] -> e
  | p::ps' ->
    let (b, t, i) = p in
    let e' = funE'(ps', e) in
    let x, e'' =
      match b with
      | EmptyB -> "_", e'
      | VarB(x, VarE("$")) -> x, e'
      | _ -> "$", letE(b, e')
    in FunE(x, t, e'', i)

let doE(e) = letE(VarB("_", e), tupE[])
let doB(e) = letB(VarB("_", e), EmptyB)

let seqE(es) =
  let b =
    List.fold_right (fun e b -> SeqB(doB(e), b))
      es (EmptyB)
  in
  doE(StrE(b))

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

let wrapE(e, t) =
  match e with
  | VarE(x) -> WrapE(x, t)
  | _ ->
    let x' = var "wrap" in
    letE(VarB(x', e), WrapE(x', t))

let unwrapE(e, t) =
  match e with
  | VarE(x) -> UnwrapE(x, t)
  | _ ->
    let x' = var "wrap" in
    letE(VarB(x', e), UnwrapE(x', t))

let rollE(e, t) =
  match e with
  | VarE(x) -> RollE(x, t)
  | _ ->
    let x' = var "@" in
    letE(VarB(x', e), RollE(x', t))

let unrollE(e, t) =
  match e with
  | VarE(x) -> UnrollE(x, t)
  | _ ->
    let x' = var "@" in
    letE(VarB(x', e), UnrollE(x', t))

let annotE(e, t) =
  let x' = var "annot" in
  appE(FunE(x', t, VarE(x'), Expl), e)

let sealE(e, t) =
  (* TODO: clone t! *)
  unwrapE(wrapE(e, WrapT(t)), WrapT(t))

let dotopE(x) =
  FunE("x", HoleT, DotE(VarE("x"), x), Expl)


let recT(p, t2) =
  let b, t1 = p in
  let e = TypE(t2) in
  let e' =
    match b with
    | VarB(x, _) -> RecE(x, t1, e)
    | EmptyB -> RecE("_", t1, e)
    | _ -> RecE("$", t1, letE(b, e))
  in PathT(e')

let recE(p, e) =
  let b, t = p in
  match b with
  | VarB(x, _) -> RecE(x, t, e)
  | EmptyB -> RecE("_", t, e)
  | _ -> RecE("$", t, letE(b, e))

let patB(p, e) =
  let b, topt = p in
  let e' =
    match topt with
    | None -> e
    | Some t -> annotE(e, t)
  in
  match b with
  | EmptyB -> doB(e')
  | VarB(x, VarE("$")) -> VarB(x, e')
  | _ -> letB(VarB("$", e'), b)

let defaultP p =
  match p with
  | b, None -> (b, HoleT)
  | b, Some t -> (b, t)

let defaultTP p =
  match p with
  | b, None -> (b, TypT)
  | b, Some t -> (b, t)

let varP(x) = VarB(x, VarE("$")), None

let holeP : bind * typ option =
  EmptyB, None

let asTopt(to1, to2) =
  match to1, to2 with
  | None, None -> None
  | None, some | some, None -> some
  | Some t1, Some t2 -> Some(AsT(t1, t2))

let asP(p1, p2) =
  let b1, to1 = p1 in
  let b2, to2 = p2 in
  SeqB(b1, b2), asTopt(to1, to2)

let annotP(p, t2) =
  let b, to1 = p in
  match b with
  | EmptyB | VarB(_, VarE("$")) -> b, Some t2
  | _ ->
    let t =
      match asTopt(to1, Some t2) with Some t -> t | None -> assert false in
    patB(p, annotE(VarE("$"), t)),
    Some t

let wrapP(p, t2) =
  let _, to1 = p in
  letB(
    VarB("$", UnwrapE("$", t2)),
    patB(p, VarE("$"))
  ),
  match to1 with
  | None -> Some t2
  | Some t1 -> Some (AsT(t2, WrapT(t1)))

let strP(xps) =
  match xps with
  | [] ->
    EmptyB, Some (StrT(EmptyD))
  | xp::_ ->
    let b, d =
      List.fold_right (fun xp (b, d) ->
        let x, p = xp in
        let _, t = (defaultP p) in
        SeqB(patB(p, DotE(VarE("$"), x)), b),
        SeqD(VarD(x, t), d)
      ) xps (EmptyB, EmptyD)
    in b, Some (StrT(d))

let rec tupP(ps) = strP(tupP' 1 ps)
and tupP' n = function
  | [] -> []
  | p::ps -> (((index n), p)) :: tupP' (n + 1) ps

let rollP(p, t2) =
  let _, to1 = p in
  letB(
    VarB("$", UnrollE("$", t2)),
    patB(p, VarE("$"))
  ),
  match to1 with
  | None -> Some t2
  | Some t1 ->
    Some (AsT(t2, PathT(RecE("_", TypT, TypE(t1)))))


(* String conversion *)

let node label = function
  | [] -> label
  | args -> label ^ "(" ^ String.concat ", " args ^ ")"

let label_of_impl i =
  match i with
  | Expl -> "Expl"
  | Impl -> "Impl"

let label_of_eff p =
  match p with
  | Pure -> "P"
  | Impure -> "I"

let label_of_typ t =
  match t with
  | PathT _ -> "PathT"
  | PrimT _ -> "PrimT"
  | TypT -> "TypT"
  | HoleT -> "HoleT"
  | StrT _ -> "StrT"
  | FunT _ -> "FunT"
  | WrapT _ -> "WrapT"
  | EqT _ -> "EqT"
  | AsT _ -> "AsT"
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
  | TypE _ -> "TypE"
  | StrE _ -> "StrE"
  | FunE _ -> "FunE"
  | WrapE _ -> "WrapE"
  | RollE _ -> "RollE"
  | IfE _ -> "IfE"
  | DotE _ -> "DotE"
  | AppE _ -> "AppE"
  | UnwrapE _ -> "UnwrapE"
  | UnrollE _ -> "UnrollE"
  | RecE _ -> "RecE"

let label_of_bind b =
  match b with
  | EmptyB -> "EmptyB"
  | SeqB _ -> "SeqB"
  | VarB _ -> "VarB"
  | InclB _ -> "InclB"


let string_of_var x = "\"" ^ x ^ "\""

let string_of_impl i = label_of_impl i
let string_of_eff p = label_of_eff p

let rec string_of_typ t =
  let node' = node (label_of_typ t) in
  match t with
  | PathT(e) -> node' [string_of_exp e]
  | PrimT(n) -> node' ["\"" ^ n ^ "\""]
  | TypT -> node' []
  | HoleT -> node' []
  | StrT(d) -> node' [string_of_dec d]
  | FunT(x, t1, t2, p, i) ->
    node' [string_of_var x; string_of_typ t1; string_of_typ t2;
      string_of_eff p; string_of_impl i]
  | WrapT(t) -> node' [string_of_typ t]
  | EqT(e) -> node' [string_of_exp e]
  | AsT(t1, t2) -> node' [string_of_typ t1; string_of_typ t2]
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
  | FunE(x, t, e, i) ->
    node' [string_of_var x; string_of_typ t; string_of_exp e; string_of_impl i]
  | WrapE(x, t) -> node' [string_of_var x; string_of_typ t]
  | RollE(x, t) -> node' [string_of_var x; string_of_typ t]
  | IfE(x, e1, e2, t) ->
    node' [string_of_var x; string_of_exp e1; string_of_exp e2; string_of_typ t]
  | DotE(e, x) -> node' [string_of_exp e; string_of_var x]
  | AppE(x1, x2) -> node' [string_of_var x1; string_of_var x2]
  | UnwrapE(x, t) -> node' [string_of_var x; string_of_typ t]
  | UnrollE(x, t) -> node' [string_of_var x; string_of_typ t]
  | RecE(x, t, e) -> node' [string_of_var x; string_of_typ t; string_of_exp e]

and string_of_bind b =
  let node' = node (label_of_bind b) in
  match b with
  | EmptyB -> node' []
  | SeqB(b1, b2) -> node' [string_of_bind b1; string_of_bind b2]
  | VarB(x, e) -> node' [string_of_var x; string_of_exp e]
  | InclB(e) -> node' [string_of_exp e]
