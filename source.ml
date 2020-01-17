(*
 * (c) 2014 Andreas Rossberg
 *)

type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}

type 'a phrase = {at : region; it : 'a}

exception Error of string * string

exception RegionError of region * string

(* Positions and regions *)

let nowhere_pos = {file = ""; line = 0; column = 0}
let nowhere_region = {left = nowhere_pos; right = nowhere_pos}

let string_of_pos pos =
  string_of_int pos.line ^ "." ^ string_of_int (pos.column + 1)
let string_of_region r =
  r.left.file ^ ":" ^ string_of_pos r.left ^ "-" ^ string_of_pos r.right

let before region = {left = region.left; right = region.left}
let after region = {left = region.right; right = region.right}

let rec span regions = match regions with
  | [] -> raise (Failure "span")
  | r::rs -> span' r.left r.right rs
and span' left right regions = match regions with
  | [] -> {left = left; right = right}
  | r::rs -> span' (min left r.left) (max right r.right) rs


(* Phrases *)

let (@@) phrase' region = {at = region; it = phrase'}

(* Errors *)

let error at m = raise (Error (at, m))
