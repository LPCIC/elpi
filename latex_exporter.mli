(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Export : sig
  val export_clauses : Parser.term list -> string 
  val set_pointer : unit -> unit
end
