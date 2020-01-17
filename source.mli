(*
 * (c) 2014 Andreas Rossberg
 *)

type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}

type 'a phrase = {at : region; it : 'a}

exception Error of string * string

exception RegionError of region * string

val nowhere_pos : pos
val nowhere_region : region

val string_of_pos : pos -> string
val string_of_region : region -> string

val before : region -> region
val after : region -> region
val span : region list -> region

val (@@) : 'a -> region -> 'a phrase

val error : string -> string -> 'a  (* raises Error *)
