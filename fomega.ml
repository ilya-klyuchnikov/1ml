(*
 * (c) 2014 Andreas Rossberg
 *)

type lab = string
type var = string

module VarMap = Map.Make(String)

module VarSet = Set.Make(String)

let basename x = try String.sub x 0 (String.index x '#') with Not_found -> x

let rename_for vars x =
  let x' = basename x in
  let rec iter i =
    let x'' = x' ^ string_of_int i in
    if VarSet.mem x'' vars then iter (i + 1) else x''
  in if VarSet.mem x' vars then iter 1 else x'

let renamings = ref VarMap.empty

let rename x =
  let x' = basename x in
  let n = try VarMap.find x' !renamings with Not_found ->
    let n = ref 0 in renamings := VarMap.add x' n !renamings; n
  in incr n; x' ^ "#" ^ string_of_int !n
