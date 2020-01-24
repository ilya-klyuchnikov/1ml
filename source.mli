(*
 * (c) 2014 Andreas Rossberg
 *)

type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}

exception Error of string * string

exception RegionError of region * string

val nowhere_pos : pos
val nowhere_region : region

val string_of_region : region -> string

val error : string -> string -> 'a  (* raises Error *)
val warn : string -> unit
