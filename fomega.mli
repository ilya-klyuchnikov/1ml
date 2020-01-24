(*
 * (c) 2014 Andreas Rossberg
 *)

(* Syntax *)

type lab = string
type var = string

(* Renaming *)

module VarSet : Set.S with type elt = var

val rename : var -> var
val rename_for : VarSet.t -> var -> var
