let declaration = ref []

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

type term =
  | Var of string [@elpi.var tctx]
  | App of term * term
  | Tapp of term * ty
  | Lam of ty * string * (term[@elpi.binder tctx (fun b s -> Entry(s,b))])
and ty =
  | TVar of string [@elpi.var tctx]
  | TIdx of ty * term
  | TAbs of string * bool * (ty[@elpi.binder tctx (fun s b -> TEntry(s,b))])
and tctx =
  | Entry of (string[@elpi.index]) * ty
  | TEentry of (string[@elpi.index]) * bool
  [@@elpi.index (module String)]
[@@deriving elpi { declaration }]

ONLY ONE 

open Elpi.API
open BuiltInPredicate
open Notation
let in_ctx_for_term : 'csts. (ctx_for_term, 'csts) ContextualConversion.ctx_readback = in_ctx_for_term

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !declaration

let main () =
  let _elpi = Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()
