let elpi_stuff = ref []

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

let pp_ctx _ _ = ()
type ctx = Entry of (string[@elpi.key]) * bool
[@@deriving elpi { declaration = elpi_stuff; index = (module String) }]

let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var]
  | App of term * term
  | Lam of bool * string * (term[@elpi.binder (fun b s -> Entry(s,b))])
[@@deriving elpi { declaration = elpi_stuff; context = (() : term -> ctx) }]

open Elpi.API

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi, _ = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()