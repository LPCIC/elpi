(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Elpi_ast

type fixity = Infixl | Infixr | Infix | Prefix | Postfix

(* raises Not_found is the constant has no declared fixity *)
val min_precedence : int   (* minimal precedence in use *)
val lam_precedence : int   (* precedence of lambda abstraction *)
val appl_precedence : int  (* precedence of applications *)
val inf_precedence : int   (* greater than any used precedence *)
val list_element_prec : int
val precedence_of : Func.t -> fixity * int
val parse_program : paths:string list -> filenames:string list -> decl list
val parse_goal : string -> term
val parse_goal_from_stream : char Stream.t -> term
val get_literal : string -> string

module PointerFunc : sig
 type latex_export =
  {process:
    'a 'b. path:string -> shortpath:string -> ('a -> 'b) -> 'a -> 'b
   ; export: clause -> unit}
(* to avoid a cycle in the Makefile, we introduce a pointer 
   function which points to a function in the latex_exporter.ml *)
 val set_latex_export : latex_export -> unit
end
