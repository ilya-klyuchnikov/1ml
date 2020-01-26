(*
 * (c) 2014 Andreas Rossberg
 *)

(* Lifting *)

val lift : Env.env -> Types.infer ref list -> Types.infer ref list
val lift_warn :
  Types.typ -> Env.env -> Types.infer ref list ->
    Types.infer ref list


(* Subtyping *)

type error
exception Sub of error

val string_of_error : error -> string

val sub_typ :
  Env.env -> Types.typ -> Types.typ -> Types.typ list ->
    Types.typ list * Types.infer ref list (* raise Sub *)
val sub_extyp :
  Env.env -> Types.extyp -> Types.extyp -> Types.typ list ->
    Types.typ list * Types.infer ref list (* raise Sub *)

val equal_typ :
  Env.env -> Types.typ -> Types.typ -> Types.infer ref list (* raise Sub *)
val equal_extyp :
  Env.env -> Types.extyp -> Types.extyp -> Types.infer ref list (* raise Sub *)
