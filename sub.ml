(*
 * (c) 2014 Andreas Rossberg
 *)

open Types
open Env


(* Errors *)

type error =
  | Missing
  | Mismatch of typ * typ
  | Struct of lab * error
  | FunEffect of eff * eff
  | FunParam of error
  | FunResult of error
  | Type of error
  | Wrap of error
  | Left of error
  | Right of error

exception Sub of error

let quote x = "`" ^ x ^ "'"

let rec string_of_error = function
  | Missing -> "missing"
  | Mismatch(t1, t2) ->
    "mismatch (" ^ string_of_typ_sort t1 ^ " vs " ^ string_of_typ_sort t2 ^ ")"
    ^ " (trying " ^ string_of_typ t1 ^ " < " ^ string_of_typ t2 ^ ")"
  | Struct(l, e) -> "field " ^ quote l ^ ": " ^ string_of_error e
  | FunEffect(p1, p2) -> "mismatch (" ^
    string_of_eff_sort p1 ^ " vs " ^ string_of_eff_sort p2 ^ " function)"
  | FunParam e -> "function parameter type: " ^ string_of_error e
  | FunResult e -> "function result type: " ^ string_of_error e
  | Type e -> "type" ^ string_of_error e
  | Wrap e -> "wrapped" ^ string_of_error e
  | Left e -> ": " ^ string_of_error e
  | Right e -> " on right-hand side: " ^ string_of_error e

(* Lifting *)

let lift env zs =
  let dom = domain_typ env in
  List.filter (fun z ->
    match !z with
    | Det _ -> false
    | Undet u -> u.vars <- VarSet.inter u.vars dom; true
  ) zs


module IdSet = Set.Make(struct type t = int let compare = compare end)
let warned_already = ref IdSet.empty

let lift_warn at t env zs =
  let dom = domain_typ env in
  List.filter (fun z ->
    match !z with
    | Det _ -> false
    | Undet u ->
      let local = VarSet.diff u.vars dom in
      if not (VarSet.is_empty local) then (
        u.vars <- VarSet.inter u.vars dom;
        if not (IdSet.mem u.id !warned_already) && occurs_typ u t then (
          let names = String.concat ", " (VarSet.elements local) in
          Source.warn at (
            "undetermined type " ^ string_of_typ (InferT z) ^
            " local to type " ^ names ^ " in type " ^ string_of_typ t
          )
        );
        warned_already := IdSet.add u.id !warned_already
      );
      true
  ) zs


(* Subtyping *)

let resolve_typ z t =
  Trace.sub (lazy ("[resolve_typ] z = " ^ string_of_norm_typ (InferT(z))));
  Trace.sub (lazy ("[resolve_typ] t = " ^ string_of_norm_typ t));
  resolve_typ z t

let unify_typ t1 t2 =
  Trace.sub (lazy ("[unify_typ] t1 = " ^ string_of_norm_typ t1));
  Trace.sub (lazy ("[unify_typ] t2 = " ^ string_of_norm_typ t2));
  unify_typ t1 t2


let rec sub_typ env t1 t2 ps =
  Trace.sub (lazy ("[sub_typ] t1 = " ^ string_of_norm_typ t1));
  Trace.sub (lazy ("[sub_typ] t2 = " ^ string_of_norm_typ t2));
  Trace.sub (lazy ("[sub_typ] ps = " ^
    String.concat ", " (List.map string_of_norm_typ ps)));
  let ts, zs =
    match norm_typ t1, freshen_typ env (norm_typ t2) with
    | t1, FunT(aks21, t21, ExT(aks22, t22), Implicit) ->
      assert (aks22 = []);
      let ts, zs = sub_typ (add_typs aks21 env) t1 t22 ps in
      List.map (fun t -> LamT(aks21, t)) ts, lift env zs

    | FunT(aks11, t11, ExT(aks12, t12), Implicit), t2 ->
      assert (aks12 = []);
      let ts1, zs1 = guess_typs (Env.domain_typ env) aks11 in
      let t1' = subst_typ (subst aks11 ts1) t12 in
      let ts2, zs2 = sub_typ env t1' t2 ps in
      ts2, zs1 @ zs2

    | TypT(s1), TypT(s2) ->
      (match s1, s2, ps with
      | ExT(aks1, t), ExT([], p1), p2::ps' when p1 = p2 ->
        if aks1 <> [] || not (!undecidable_flag || is_small_typ t) then
          raise (Sub (Mismatch (t1, t2)));
        [t], []
      | _ ->
        let zs = try equal_extyp env s1 s2 with Sub e -> raise (Sub (Type e)) in
        [], zs
      )

    | StrT(tr1), StrT(tr2) ->
      let ts, zs = sub_row env tr1 tr2 ps in
      ts, zs

    | FunT(aks1, t11, s1, Explicit p1), FunT(aks2, t21, s2, Explicit p2) ->
      if p1 = Impure && p2 = Pure then raise (Sub (FunEffect(p1, p2)));
      let env' = add_typs aks2 env in
      let ts1, zs1 =
        try sub_typ env' t21 t11 (varTs aks1) with Sub e ->
          raise (Sub (FunParam e)) in
      let ps' = List.map (fun p -> AppT(p, varTs aks2)) ps in
      let ts2, zs2 =
        try sub_extyp env' (subst_extyp (subst aks1 ts1) s1) s2 ps'
        with Sub e -> raise (Sub (FunResult e)) in
      List.map (fun t -> LamT(aks2, t)) ts2, lift env (zs1 @ zs2)

    | WrapT(s1), WrapT(s2) ->
      let _, zs =
        try sub_extyp env s1 s2 [] with Sub e -> raise (Sub (Wrap e)) in
      [], zs

    | AppT(t1', ts1), AppT(t2', ts2) ->
      (try
        let zs1 = equal_typ env t1' t2' in
        let zs2 = List.concat (List.map2 (equal_typ env) ts1 ts2) in
        [], zs1 @ zs2
      with Sub e ->
        raise (Sub (Mismatch(t1, t2)))
      )

    | DotT(t1', l1), DotT(t2', l2) ->
      if l1 <> l2 then raise (Sub (Mismatch(t1, t2))) else
      let zs = try equal_typ env t1' t2' with Sub e ->
        raise (Sub (Mismatch(t1, t2))) in
      [], zs

    | RecT(ak1, t1'), RecT(ak2, t2') ->
      if snd ak1 <> snd ak2 then
        raise (Sub (Mismatch(t1, t2)));
      let zs = try
          equal_typ (add_typs [ak2] env)
            (subst_typ (subst [ak1] (varTs [ak2])) t1') t2'
        with Sub e ->
          raise (Sub (Mismatch(t1, t2)))
      in [], lift env zs

    | InferT(z) as t1, (TypT(_) as t2) ->
      let t11, zs1 = guess_typ (Env.domain_typ env) BaseK in
      let t1' = TypT(ExT([], t11)) in
      let ts, zs2 = sub_typ env t1' t2 ps in
      if not (resolve_typ z t1') then raise (Sub (Mismatch(t1, t2)));
      ts, zs1 @ zs2

    | InferT(z) as t1, (StrT(tr2) as t2) ->
      (* TODO: row polymorphism *)
      let tzsr = map_row (fun _ -> guess_typ (Env.domain_typ env) BaseK) tr2 in
      let t1' = StrT(map_row fst tzsr) in
      let zs1 = List.concat (List.map snd (List.map snd tzsr)) in
      let ts, zs2 = sub_typ env t1' t2 ps in
      if not (resolve_typ z t1') then raise (Sub (Mismatch(t1, t2)));
      ts, zs1 @ zs2

    | InferT(z) as t1, (FunT([], t21, ExT([], t22), Explicit Impure) as t2) ->
      let t11, zs1 = guess_typ (Env.domain_typ env) BaseK in
      let t12, zs2 = guess_typ (Env.domain_typ env) BaseK in
      let t1' = FunT([], t11, ExT([], t12), Explicit Impure) in
      let ts, zs3 = sub_typ env t1' t2 ps in
      if not (resolve_typ z t1') then raise (Sub (Mismatch(t1, t2)));
      ts, zs1 @ zs2 @ zs3

    | InferT(z) as t1, t2 ->
      if not (resolve_typ z t2) then raise (Sub (Mismatch(t1, t2)));
      [], []

    | TypT(_) as t1, (InferT(z) as t2) ->
      let t21, zs1 = guess_typ (Env.domain_typ env) BaseK in
      let t2' = TypT(ExT([], t21)) in
      let ts, zs2 = sub_typ env t1 t2' ps in
      if not (resolve_typ z t2') then raise (Sub (Mismatch(t1, t2)));
      ts, zs1 @ zs2

    | StrT(tr1) as t1, (InferT(z) as t2) ->
      (* TODO: row polymorphism *)
      let tzsr = map_row (fun _ -> guess_typ (Env.domain_typ env) BaseK) tr1 in
      let t2' = StrT(map_row fst tzsr) in
      let zs1 = List.concat (List.map snd (List.map snd tzsr)) in
      let ts, zs2 = sub_typ env t1 t2' ps in
      if not (resolve_typ z t2') then raise (Sub (Mismatch(t1, t2)));
      ts, zs1 @ zs2

    | FunT([], t11, ExT([], t12), Explicit p) as t1, (InferT(z) as t2) ->
      let t21, zs1 = guess_typ (Env.domain_typ env) BaseK in
      let t22, zs2 = guess_typ (Env.domain_typ env) BaseK in
      let t2' = FunT([], t21, ExT([], t22), Explicit Impure) in
      let ts, zs3 = sub_typ env t1 t2' ps in
      if not (resolve_typ z t2') then raise (Sub (Mismatch(t1, t2)));
      ts, zs1 @ zs2 @ zs3

    | t1, (InferT(z) as t2) ->
      if not (resolve_typ z t1) then raise (Sub (Mismatch(t1, t2)));
      [], []

    | t1', t2' when unify_typ t1' t2' ->
      [], []

    | _ -> raise (Sub (Mismatch(t1, t2)))
  in
  Trace.sub (lazy ("[sub_typ] done t1 = " ^ string_of_norm_typ t1));
  Trace.sub (lazy ("[sub_typ] done t2 = " ^ string_of_norm_typ t2));
  Trace.sub (lazy ("[sub_typ] done ts = " ^
    String.concat ", " (List.map string_of_norm_typ ts)));
  ts, zs

and sub_extyp env s1 s2 ps =
  Trace.sub (lazy ("[sub_extyp] s1 = " ^ string_of_norm_extyp s1));
  Trace.sub (lazy ("[sub_extyp] s2 = " ^ string_of_norm_extyp s2));
  let ExT(aks2, t2) = freshen_extyp env s2 in
  let ExT(aks1, t1) = freshen_extyp (add_typs aks2 env) s1 in
  match aks1, aks2 with
  | [], [] ->
    sub_typ env t1 t2 ps
  | _ ->
    let ts, zs = sub_typ (add_typs aks1 env) t1 t2 (varTs aks2) in
    [], lift env zs

and sub_row env tr1 tr2 ps =
  match tr2 with
  | [] ->
    [], []
  | (l, t2)::tr2' ->
    Trace.sub (lazy ("[sub_row] l = " ^ l));
    let ts1, zs1 =
      try sub_typ env (List.assoc l tr1) t2 ps with
      | Not_found -> raise (Sub (Struct(l, Missing)))
      | Sub e -> raise (Sub (Struct(l, e)))
    in
    let rec psubst p t =
      match p with
      | VarT(a, k) -> a, t
      | AppT(p', ts) -> psubst p' (LamT(List.map unvarT ts, t))
      | _ -> assert false
    in
    let su = List.map2 psubst (Lib.List.take (List.length ts1) ps) ts1 in
    let ps' = Lib.List.drop (List.length ts1) ps in
    let ts2, zs2 = sub_row env tr1 (subst_row su tr2') ps' in
    ts1 @ ts2, zs1 @ zs2

and equal_typ env t1 t2 =
  Trace.sub (lazy ("[equal_typ] t1 = " ^ string_of_norm_typ t1));
  Trace.sub (lazy ("[equal_typ] t2 = " ^ string_of_norm_typ t2));
  let _, zs1 =
    try sub_typ env t1 t2 [] with Sub e -> raise (Sub (Left e)) in
  let _, zs2 =
    try sub_typ env t2 t1 [] with Sub e -> raise (Sub (Right e)) in
  zs1 @ zs2

and equal_extyp env s1 s2 =
  Trace.sub (lazy ("[equal_extyp] s1 = " ^ string_of_norm_extyp s1));
  Trace.sub (lazy ("[equal_extyp] s2 = " ^ string_of_norm_extyp s2));
  let _, zs1 =
    try sub_extyp env s1 s2 [] with Sub e -> raise (Sub (Left e)) in
  let _, zs2 =
    try sub_extyp env s2 s1 [] with Sub e -> raise (Sub (Right e)) in
  zs1 @ zs2
