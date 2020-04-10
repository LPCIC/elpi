open Elpi.API
open Ocaml_ast_for_elpi

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) 
    (parsetree_declaration @ Elpi.Builtin.PPX.declarations)

TODO: separate declarations (in elpi.ppx) so that we can assemble the
program differently (put before the source of the rewriter, than the
identity mapping provided by the ppx)

let program_src = ref ""
let typecheck = ref false

let map_structure s =
  if !program_src = "" then begin
    Printf.eprintf "elpi.ocaml_ppx: you must pass --cookie 'program=\"some_file.elpi\"'";
    exit 1;
  end;
  let elpi, _ = Setup.init ~builtins:[builtin;Elpi.Builtin.std_builtins] ~basedir:"." [] in
  BuiltIn.document_file builtin;
  let program = Parse.program ~elpi [!program_src] in
  let program = Compile.program ~elpi ~flags:Compile.default_flags [program] in
  let query =
    let open Query in
    let open ContextualConversion in
    compile program (Ast.Loc.initial "ppx") @@
      Query { predicate = "map.structure"; arguments = D(!< structure,s,(Q(!< structure,"Result",N))) } in
  if !typecheck then begin
    if not @@ Compile.static_check ~checker:Elpi.Builtin.(default_checker ()) query then begin
      exit 1
    end
  end;
  let exe = Compile.optimize query in
  match Execute.once exe with
  | Execute.Success { output = (s,_); _ } -> s
  |  _ ->
     Printf.eprintf "elpi.ocaml_ppx: rewriter %s failed" !program_src;
     exit 1
;;

let erase_loc =
  let open Ppxlib in
  (* let open Ppxlib.Ast_pattern in *)
  object
    inherit [State.t] Ast_traverse.fold_map
    method! location _ (st : State.t) = Ocaml_ast_for_elpi.dummy_location, st
  end
;;

let expression_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.expression (Lexing.from_string s) in
  let e, state = erase_loc#expression e state in
  let state, x, gls = (ContextualConversion.(!<) expression).Conversion.embed ~depth state e in
  assert(gls = []);
  state, x

let () = Quotation.set_default_quotation expression_quotation

let pattern_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.pattern (Lexing.from_string s) in
  let e, state = erase_loc#pattern e state in
  let state, x, gls = (ContextualConversion.(!<) pattern).Conversion.embed ~depth state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"pat" pattern_quotation

open Ppxlib

let arg_program t =
  match Driver.Cookies.get t "program" Ast_pattern.(estring __) with
  | Some p -> program_src := p
  | _ -> ()

let arg_typecheck t =
  match Driver.Cookies.get t "typecheck" Ast_pattern.(__) with
  | Some _ -> typecheck := true
  | _ -> ()

let () =
  Driver.Cookies.add_handler arg_program;
  Driver.register_transformation
    ~impl:map_structure
    "elpi"