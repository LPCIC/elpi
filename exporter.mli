(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Export : sig
  val export_clauses : Elpi_parser.term list -> unit 
end
