(*
 * (c) 2014 Andreas Rossberg
 *)

open Source
open Types
open Env
open Sub

module EL = Syntax

exception Error of string

let quote x = "`" ^ x ^ "'"


(* Verification *)

let verify_flag = ref false
let verify_fomega_flag = ref true

(* Recursive types *)

exception Recursive

let rec make_rec_typ = function
  | StrT(tr) ->
    let tr', kr = make_rec_row tr in
    TupT(tr'), ProdK(kr)
  | FunT(aks, t, s, Explicit Pure) ->
    let t', k = make_rec_extyp s in
    LamT(aks, t'), FunK(List.map snd aks, k)
  | TypT(ExT([], t)) -> t, BaseK
  | _ -> raise Recursive

and make_rec_extyp = function
  | ExT(aks, t) -> if aks = [] then make_rec_typ t else raise Recursive

and make_rec_row tr =
  let tkr = map_row make_rec_typ tr in
  map_row fst tkr, map_row snd tkr


let rec paths_typ ta ps = function
  | StrT(tr) -> paths_row ta ps tr
  | FunT(aks, t, s, Explicit Pure) ->
    paths_extyp ta (List.map (fun p -> AppT(p, varTs aks)) ps) s
  | TypT(ExT([], t)) ->
    (match ps with p::_ when p = t -> [ta] | _ -> [])
  | _ -> raise Recursive

and paths_extyp ta ps = function
  | ExT(aks, t) -> if aks = [] then paths_typ ta ps t else raise Recursive

and paths_row ta ps = function
  | [] -> []
  | (l, t)::tr ->
    let ts1 = paths_typ (DotT(ta, l)) ps t in
    let ts2 = paths_row ta (Lib.List.drop (List.length ts1) ps) tr in
    ts1 @ ts2


(* Instantiation *)

let rec instantiate env t =
  match follow_typ t with
  | FunT(aks1, t1, ExT(aks2, t2), Implicit) ->
    assert (aks2 = []);
    let ts, zs = guess_typs (Env.domain_typ env) aks1 in
    let t', zs' =
      instantiate env (subst_typ (subst aks1 ts) t2)
    in t', zs @ zs'
  | t -> t, []


(* Type Elaboration *)

let elab_impl env impl =
  match impl with
  | EL.Expl -> Explicit Pure
  | EL.Impl -> Implicit

let elab_eff env eff =
  match eff with
  | EL.Pure -> Pure
  | EL.Impure -> Impure

let rec elab_typ env typ l =
  Trace.elab (lazy ("[elab_typ] " ^ EL.label_of_typ typ));
  match typ with
  | EL.PathT(exp) ->
    let t, zs = elab_pathexp env exp l in
    (match t with
    | TypT(s) ->
      let ExT(aks, t) = s in
      let aks' = freshen_vars env (rename_vars (prepend_path l) aks) in
      ExT(aks', subst_typ (subst aks (varTs aks')) t), zs
    | InferT(z) ->
      let t', zs2 = guess_typ (Env.domain_typ env) BaseK in
      let s = ExT([], t') in
      resolve_always z (TypT(s));
      s, zs @ zs2
    | _ -> error "FIXME: Position" "expression does not denote a type"
    )

  | EL.PrimT(n) ->
    (match Prim.typ_of_string n with
    | Some t -> ExT([], PrimT(t)), []
    | None -> error "FIXME: Position" "unknown primitive type"
    )

  | EL.TypT ->
    let a = freshen_var env (default_path l "t") in
    ExT([a, BaseK], TypT(ExT([], VarT(a, BaseK)))), []

  | EL.HoleT ->
    let t, zs = guess_typ (Env.domain_typ env) BaseK in
    ExT([], t), zs

  | EL.StrT(dec) ->
    elab_dec env dec l

  | EL.FunT(var, typ1, typ2, eff, impl) ->
    let ExT(aks1, t1), zs1 = elab_typ env typ1 var in
    let ExT(aks2, t2), zs2 =
      elab_typ (add_val var t1 (add_typs aks1 env)) typ2 l in
    (match elab_eff env eff, elab_impl env impl with
    | Impure, Explicit _ ->
      let aks2' =
        freshen_vars (add_typs aks1 env) (rename_vars (cut_path l) aks2) in
      let s2' = ExT(aks2', subst_typ (subst aks2 (varTs aks2')) t2) in
      let t = FunT(aks1, t1, s2', Explicit Impure) in
      ExT([], t), lift_warn t env (zs1 @ zs2)
    | Pure, f ->
      let aks2' =
        freshen_vars (add_typs aks1 env)
          (List.map (fun (a2, k2) -> a2, funK(List.map snd aks1, k2)) aks2) in
      let tas2' =
        List.map (fun (a2', k2') -> appT(VarT(a2', k2'), varTs aks1)) aks2' in
      let t2' = subst_typ (subst aks2 tas2') t2 in
      let t = FunT(aks1, t1, ExT([], t2'), f) in
      ExT(aks2', t), lift_warn t (add_typs aks2' env) (zs1 @ zs2)
    | _ -> error "FIXME: Position" "impure function cannot be implicit"
    )

  | EL.WrapT(typ1) ->
    let s1, zs = elab_typ env typ1 "" in
    ExT([], WrapT(s1)), lift_warn (WrapT(s1)) env zs

  | EL.EqT(exp) ->
    let t, zs = elab_pathexp env exp l in
    ExT([], t), zs

  | EL.AsT(typ1, typ2) ->
    let ExT(aks1, t1) as s1, zs1 = elab_typ env typ1 l in
    let s2, zs2 = elab_typ env typ2 l in
    let zs3 = try equal_extyp env s1 s2 with Sub e ->
      error "FIXME: Position" (
        "inconsistent types equated by `as': " ^
        Types.string_of_extyp s1 ^ " vs " ^ Types.string_of_extyp s2
      )
    in
    s1, lift_warn t1 (add_typs aks1 env) (zs1 @ zs2 @ zs3)

  | EL.WithT(typ1, vars, exp) ->
    let t2, zs2 = elab_pathexp env exp l in
    let ExT(aks1, t1), zs1 = elab_typ env typ1 l in
    let ls = List.map (fun var -> var) vars in
    let ta = try project_typ ls t1 with Not_found ->
      error "FIXME: Position" ("path " ^ quote (String.concat "." ls) ^ " unbound") in
    let bs = vars_typ ta in
    let aks11 = List.filter (fun (a, k) -> not (VarSet.mem a bs)) aks1 in
    let aks12 = List.filter (fun (a, k) -> VarSet.mem a bs) aks1 in
    let ts, zs3 =
      try sub_typ env t2 ta (varTs aks12) with Sub e -> error "FIXME: Position"
        ("refinement type does not match type component: " ^ Sub.string_of_error e)
    in
    ExT(aks11, subst_typ (subst aks12 ts) t1),
    lift_warn t1 (add_typs aks11 env) (zs1 @ zs2 @ zs3)

and elab_dec env dec l =
  Trace.elab (lazy ("[elab_dec] " ^ EL.label_of_dec dec));
  match dec with
  | EL.VarD(var, typ) ->
    let l' = var in
    let ExT(aks, t), zs = elab_typ env typ (append_path l l') in
    Trace.bind (lazy ("[VarD] " ^ l ^ " : " ^
      string_of_norm_extyp (ExT(aks, t))));
    ExT(aks, StrT[l', t]), zs

  | EL.InclD(typ) ->
    let ExT(aks, t) as s, zs = elab_typ env typ l in
    (match t with
    | StrT(tr) -> ()
    | InferT(z) -> resolve_always z (StrT[])  (* TODO: row polymorphism *)
    | _ -> error "FIXME: Position" "included type is not a structure"
    ); s, zs

  | EL.EmptyD ->
    ExT([], StrT[]), []

  | EL.SeqD(dec1, dec2) ->
    (match elab_dec env dec1 l with
    | ExT(aks1, StrT(tr1)), zs1 ->
      (match elab_dec (add_row tr1 (add_typs aks1 env)) dec2 l with
      | ExT(aks2, StrT(tr2)), zs2 ->
        let ls = intersect_row tr1 tr2 in
        if ls <> [] then
          error "FIXME: Position" ("multiple declarations for " ^
            String.concat ", " (List.map (fun (l, _) -> quote l) ls));
        ExT(aks1 @ aks2, StrT(tr1 @ tr2)), zs1 @ zs2
      | _ -> assert false
      )
    | _ -> assert false
    )

and elab_pathexp env exp l =
  Trace.elab (lazy ("[elab_pathexp] " ^ EL.label_of_exp exp));
  let ExT(aks, t), p, zs = elab_instexp env exp l in
  if p = Impure then
    error "FIXME: Position" "impure path expression";
  if List.exists (fun (a, k) -> contains_typ a t) aks then
    error "FIXME: Position" "local type(s) escape scope"
  else
    follow_typ t, lift_warn t env zs


(* Expression elaboration *)

and lookup_var env var =
  try lookup_val var env with Not_found ->
    error "FIXME: Position" ("unbound identifier " ^ quote var)

and elab_instvar env var =
  instantiate env (lookup_var env var)

and elab_prim_typ = function
  | Prim.VarT -> VarT("a", BaseK)
  | t -> PrimT(t)

and elab_prim_typs = function
  | [t] -> elab_prim_typ t
  | ts -> StrT(tup_row (List.map elab_prim_typ ts))

and elab_prim_fun f =
  let t1 = elab_prim_typs (fst f.Prim.typ) in
  let t2 = elab_prim_typs (snd f.Prim.typ) in
  let t = FunT([], t1, ExT([], t2), Explicit Impure) in
  if Prim.is_poly f then
    let ta = TypT(ExT([], VarT("a", BaseK))) in
    FunT(["a", BaseK], ta, ExT([], t), Explicit Impure)
  else
    t

and elab_const = function
  | Prim.FunV(f) -> elab_prim_fun f
  | c -> PrimT(Prim.typ_of_const c)

and elab_exp env exp l =
  Trace.elab (lazy ("[elab_exp] " ^ EL.label_of_exp exp));
  match exp with
  | EL.VarE(var) ->
    ExT([], lookup_var env var), Pure, []

  | EL.PrimE(c) ->
    let t = elab_const c in
    ExT([], t), Pure, []

  | EL.TypE(typ) ->
    let s, zs = elab_typ env typ "" in
    ExT([], TypT(s)), Pure, zs

  | EL.StrE(bind) ->
    elab_bind env bind l

  | EL.FunE(var, typ, exp2, impl) ->
    let ExT(aks, t), zs1 = elab_typ env typ var in
    let s, p, zs2 =
      elab_exp (add_val var t (add_typs aks env)) exp2 "" in
    assert (let ExT(aks, _) = s in p = Impure || aks = []);
    let p' =
      match p, elab_impl env impl with
      | Impure, Explicit _ -> Explicit Impure
      | Pure, f -> f
      | _ -> error "FIXME: Position" "impure function cannot be implicit" in
    ExT([], FunT(aks, t, s, p')), Pure,
    lift_warn (FunT(aks, t, s, p')) env (zs1 @ zs2)

  | EL.WrapE(var, typ) ->
    let s, zs1 =
      match elab_typ env typ "" with
      | ExT([], WrapT(s)), zs1 -> s, zs1
      | _ -> error "FIXME: Position" "non-wrapped type for wrap"
    in
    let _, zs2 =
      try sub_extyp env (ExT([], lookup_var env var)) s []
      with Sub e -> error "FIXME: Position"
        ("wrapped type does not match annotation: " ^ Sub.string_of_error e)
    in
    ExT([], WrapT(s)), Pure, lift_warn (WrapT(s)) env (zs1 @ zs2)

  | EL.RollE(var, typ) ->
    let s, zs1 = elab_typ env typ l in
    let t, ak, t' =
      match s with
      | ExT([], (RecT(ak, t') as t)) -> t, ak, t'
      | _ -> error "FIXME: Position" "non-recursive type for rolling" in
    let _, zs2 =
      try sub_typ env (lookup_var env var) (subst_typ (subst [ak] [t]) t') []
      with Sub e -> error "FIXME: Position" ("rolled value does not match annotation") in
    ExT([], t), Pure, zs1 @ zs2

  | EL.IfE(var, exp1, exp2, typ) ->
    let t0, zs0 = elab_instvar env var in
    let _ =
      match t0 with
      | PrimT(Prim.BoolT) -> ()
      | InferT(z) -> resolve_always z (PrimT(Prim.BoolT))
      | _ -> error "FIXME: Position" "condition is not Boolean" in
    let ExT(aks, t) as s, zs = elab_typ env typ l in
    let s1, p1, zs1 = elab_exp env exp1 l in
    let s2, p2, zs2 = elab_exp env exp2 l in
    let _, zs3 = try sub_extyp env s1 s [] with Sub e -> error "FIXME: Position"
      ("branch type does not match annotation: " ^ Sub.string_of_error e) in
    let _, zs4 = try sub_extyp env s2 s [] with Sub e -> error "FIXME: Position"
      ("branch type does not match annotation: " ^ Sub.string_of_error e) in
    s, join_eff p1 p2,
    lift_warn t (add_typs aks env) (zs0 @ zs @ zs1 @ zs2 @ zs3 @ zs4)

  | EL.DotE(exp1, var) ->
    let ExT(aks, t), p, zs1 = elab_instexp env exp1 "" in
    let tr, zs2 =
      match t with
      | StrT(tr) -> tr, []
      | InferT(z) ->
        (* TODO: row polymorphism *)
        let t, zs = guess_typ (Env.domain_typ (add_typs aks env)) BaseK in
        let tr = [l, t] in
        resolve_always z (StrT(tr)); tr, zs
      | _ -> error "FIXME: Position" "expression is not a structure"
    in
    let t' = try List.assoc var tr with Not_found ->
      error "FIXME: Position" ("field " ^ quote var ^ " unbound in expression") in
    let aks' = freshen_vars env (rename_vars (cut_path var) aks) in
    let s = ExT(aks', subst_typ (subst aks (varTs aks')) t') in
    List.iter (subst_infer (subst aks (varTs aks'))) (zs1 @ zs2);
    s, p, zs1 @ zs2

  | EL.AppE(var1, var2) ->
    let tf, zs1 = elab_instvar env var1 in
    let aks1, t1, s, p, zs =
      match freshen_typ env tf with
      | FunT(aks1, t1, s, Explicit p) -> aks1, t1, s, p, []
      | InferT(z) ->
        let t1, zs1 = guess_typ (Env.domain_typ env) BaseK in
        let t2, zs2 = guess_typ (Env.domain_typ env) BaseK in
        let s = ExT([], t2) in
        resolve_always z (FunT([], t1, s, Explicit Impure));
        [], t1, s, Impure, zs1 @ zs2
      | _ -> error var1 "expression is not a function" in
    let t2 = lookup_var env var2 in
    let ts, zs3 =
      try sub_typ env t2 t1 (varTs aks1) with Sub e -> error "FIXME: Position"
        ("argument type does not match function: " ^ Sub.string_of_error e)
    in
    let ExT(aks2, t2) = s in
    let aks2' = freshen_vars env (rename_vars (prepend_path l) aks2) in
    let s' = ExT(aks2', subst_typ (subst aks2 (varTs aks2')) t2) in
    subst_extyp (subst aks1 ts) s', p, zs1 @ zs @ zs3

  | EL.UnwrapE(var, typ) ->
    let aks, t, s2, zs2 =
      match elab_typ env typ l with
      | ExT([], WrapT(ExT(aks, t) as s2)), zs2 -> aks, t, s2, zs2
      | _ -> error "FIXME: Position" "non-wrapped type for unwrap" in
    let t1, zs1 = elab_instvar env var in
    let s1 =
      match t1 with
      | WrapT(s1) -> s1
      | InferT(z) ->
        if resolve_typ z (WrapT(s2)) then s2
        else error "FIXME: Position" "inferred type would escape scope"
      | _ -> error "FIXME: Position" "expression is not a wrapped value" in
    let _, zs3 = try sub_extyp env s1 s2 [] with Sub e -> error "FIXME: Position"
      ("wrapped type does not match annotation: " ^ Sub.string_of_error e) in
    s2, Impure, lift_warn t (add_typs aks env) (zs1 @ zs2 @ zs3)

  | EL.UnrollE(var, typ) ->
    let s, zs1 = elab_typ env typ l in
    let t, ak, t' =
      match s with
      | ExT([], (RecT(ak, t') as t)) -> t, ak, t'
      | _ -> error "FIXME: Position" "non-recursive type for rolling" in
    let _, zs2 = try sub_typ env (lookup_var env var) t [] with Sub e ->
      error "FIXME: Position" ("unrolled value does not match annotation") in
    ExT([], subst_typ (subst [ak] [t]) t'), Pure, zs1 @ zs2

  | EL.RecE(var, typ, exp1) ->
    let ExT(aks1, t1) as s1, zs1 = elab_typ env typ l in
    let env1 = add_val var t1 (add_typs aks1 env) in
    (match aks1 with
    | [] ->
      let ExT(aks2, t2), p, zs2 = elab_exp env1 exp1 l in
      if p <> Pure then error "FIXME: Position" "recursive expression is not pure";
      let _, zs3 =
        try sub_typ (add_typs aks2 env1) t2 t1 [] with Sub e -> error "FIXME: Position"
          ("recursive expression does not match annotation: " ^
            Sub.string_of_error e)
      in
      (* TODO: syntactic restriction *)
      s1, Pure, lift_warn t1 (add_typs aks2 env) (zs1 @ zs2 @ zs3)
    | _ ->
      let t2, zs2 = elab_pathexp env1 exp1 l in
      let ts, zs3 =
        try sub_typ env1 t2 t1 (varTs aks1) with Sub e -> error "FIXME: Position"
          ("recursive type does not match annotation: " ^ Sub.string_of_error e)
      in
      let t3, k3 = try make_rec_typ t1 with Recursive ->
        error "FIXME: Position" "illegal type for recursive expression" in
      let a = freshen_var env var in
      let tas1 = paths_typ (VarT(a, k3)) (varTs aks1) t1 in
      let t3' = subst_typ (subst aks1 tas1) (subst_typ (subst aks1 ts) t3) in
      let t4 = RecT((a, k3), t3') in
      let t = subst_typ (subst aks1 (List.map (subst_typ [a, t4]) tas1)) t1 in
      ExT([], t), Pure, lift_warn t env (zs1 @ zs2 @ zs3)
    )

(*
rec (X : (b : type) => {type t; type u a}) fun (b : type) => {type t = (X int.u b, X bool.t); type u a = (a, X b.t)}
s1 = ?Xt:*->*, Xu:*->*->*. !b:*. [= b] -> {t : [= Xt b], u : !a:*. [= a] => [= Xu b a]}
s2 = !b:*. [= b] => {t : [= (Xu int b, Xt bool)], u : !a:*. [= a] => [= (a, Xt b)]}

as1 = Xt, Xu
ts = \b:*. (Xu int b, Xt bool), \b:*, a:*. (a, Xt b)
k3 = {t:*->*,u:*->*->*}
t3 = \b:*. {t = Xt b, u = \a:*. Xu b a}
tas1 = X.t, X.u
t3' = \b:*. {t = (X.u int b, X.t bool), u = \a:*. (a, X.t b)}
t4 = @X:{t:*->*,u:*->*->*}. \b:*. {t = (X.u int b, X.t bool), u = \a:*. (a, X.t b)}
t = !b:*. [= b] -> {t : [= t4.t b], u : !a:*. [= a] => [= (a, t4.u b a)]}
*)

and elab_bind env bind l =
  Trace.elab (lazy ("[elab_bind] " ^ EL.label_of_bind bind));
  match bind with
  | EL.VarB(var, exp) ->
    let l' = var in
    let ExT(aks, t), p, zs = elab_genexp env exp (append_path l l') in
    Trace.bind (lazy ("[VarB] " ^ l' ^ " : " ^
      string_of_norm_extyp (ExT(aks, t))));
    let s = ExT(aks, StrT[l', t]) in
    s, p, zs

  | EL.InclB(exp) ->
    let ExT(aks, t) as s, p, zs = elab_instexp env exp l in
    (match t with
    | StrT(tr) -> ()
    | InferT(z) -> resolve_always z (StrT[])  (* TODO: row polymorphism *)
    | _ -> error "FIXME: Position" "included expression is not a structure"
    );
    s, p, zs

  | EL.EmptyB ->
    ExT([], StrT[]), Pure, []

  | EL.SeqB(bind1, bind2) ->
    (match elab_bind env bind1 l with
    | ExT(aks1, StrT(tr1)), p1, zs1 ->
      (match elab_bind (add_row tr1 (add_typs aks1 env)) bind2 l with
      | ExT(aks2, StrT(tr2)), p2, zs2 ->
        let tr1' = diff_row tr1 tr2 in
        let s = ExT(aks1 @ aks2, StrT(tr1' @ tr2)) in
        s, join_eff p1 p2,
        lift_warn (unexT s) env (zs1 @ zs2)  (* TODO: over-strict! *)
      | _ -> error "FIXME: Position" "internal SeqB2"
      )
    | _ -> error "FIXME: Position" "internal SeqB1"
    )

and elab_genexp env exp l =
  let level = level () in
  let a1 = freshen_var env "$" in
  let ExT(aks, t) as s, p, zs = elab_exp (add_typ a1 BaseK env) exp l in
  let zs1, zs2 =
    List.partition (fun z ->
      match !z with
      | Undet u -> u.level >= level
      | Det _ -> assert false
    ) (lift (add_typs aks env) zs) in
  if p = Impure || zs1 = [] then
    s, p, zs1 @ zs2
  else begin
    assert (aks = []);
    let kr = List.mapi (fun i _ -> lab (i + 1), BaseK) zs1 in
    let k1 = ProdK(kr) in
    let ta1 = VarT(a1, ProdK(kr)) in
    let tr = map_rowi (fun l k -> TypT(ExT([], DotT(ta1, l)))) kr in
    List.iter2 (fun z (l, k) -> close_typ z (DotT(ta1, l))) zs1 kr;
    let t1' = StrT(tr) in
    ExT(aks, FunT([a1, k1], t1', ExT([], t), Implicit)), Pure, zs2
  end

and elab_instexp env exp l =
  let ExT(aks, t), p, zs1 = elab_exp env exp l in
  let t', zs2 = instantiate (add_typs aks env) t in
  ExT(aks, t'), p, zs1 @ zs2


let elab env exp =
  let s, p, zs = elab_exp env exp "" in
  s, p
