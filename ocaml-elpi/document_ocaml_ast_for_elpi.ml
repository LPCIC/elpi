(* This simple file documents is Sys.argv.(1) the Elpi description of OCaml's AST *)

open Elpi.API

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1))
    (Ocaml_elpi_ppx.Ocaml_ast_for_elpi.parsetree_declaration)

let main () =
  let elpi = Setup.init ~builtins:[builtin ; Elpi.Builtin.std_builtins] () in
  BuiltIn.document_file builtin;
  flush_all ();
  let program = Parse.program ~elpi ~files:[] in
  let program = Compile.program ~elpi ~flags:Compile.default_flags [program] in
  let query =
    let open Query in
    compile program (Ast.Loc.initial "ppx") @@
      Query { predicate = "true"; arguments = N } in
  if Compile.static_check ~checker:Elpi.Builtin.(default_checker ()) query then exit 0
  else (Printf.eprintf "document_ocaml_ast: generated elpi code does not type check"; exit 1)
;;

main ()
