(*
 * (c) 2014 Andreas Rossberg
 *)

type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}

type 'a phrase = {at : region; it : 'a}

exception Error of region * string

val nowhere_pos : pos
val nowhere_region : region

val string_of_pos : pos -> string
val string_of_region : region -> string

val before : region -> region
val after : region -> region
val span : region list -> region

val (@@) : 'a -> region -> 'a phrase
val (@@@) : 'a -> region list -> 'a phrase
val dup : 'a phrase -> 'a phrase

val at : 'a phrase -> region
val it : 'a phrase -> 'a

val warn : region -> string -> unit
val error : region -> string -> 'a  (* raises Error *)
val indent : string -> string
