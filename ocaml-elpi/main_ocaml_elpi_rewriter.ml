open Elpi.API
open Ocaml_ast_for_elpi

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) parsetree_declaration

let mapper = String.concat "\n" (Elpi.Builtin.PPX.mapper_src :: parsetree_mapper)

let program_src = ref ""
let typecheck = ref false
let debug = ref (try ignore(Sys.getenv "DEBUG"); true with Not_found -> false)

let map_structure s =
  if !program_src = "" then begin
    Printf.eprintf {|
ocaml-elpi.ppx: no program specified. Supported options:
  --cookie 'program=\"some_file.elpi\"'  source code of the rewriter (mandatory)
  --cookie typecheck=1                   typcheck the program
  --cookie debug=1                       print debug trace (also env DEBUG=1)
|};
    exit 1;
  end;
  let elpi, _ = Setup.init ~builtins:[builtin;Elpi.Builtin.std_builtins] ~basedir:"." [] in
  BuiltIn.document_file builtin;
  if !debug then
    Setup.trace ["-trace-on";"tty";"stderr";"-trace-only";"user";"-trace-only-pred";"map";"-trace-at";"run";"1";"99999"];
  let program = Parse.program ~elpi [!program_src] in
  let mapper = Parse.program_from_stream ~elpi (Ast.Loc.initial "mapper") (Stream.of_string mapper) in
  let program = Compile.program ~elpi ~flags:Compile.default_flags [program;mapper] in
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

let () = Quotation.register_named_quotation ~name:"expr" expression_quotation
let () = Quotation.set_default_quotation expression_quotation

let pattern_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.pattern (Lexing.from_string s) in
  let e, state = erase_loc#pattern e state in
  let state, x, gls = (ContextualConversion.(!<) pattern).Conversion.embed ~depth state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"pat" pattern_quotation

let type_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.core_type (Lexing.from_string s) in
  let e, state = erase_loc#core_type e state in
  let state, x, gls = (ContextualConversion.(!<) core_type).Conversion.embed ~depth state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"type" type_quotation

let stri_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.toplevel_phrase (Lexing.from_string s) in
  match e with
  | Ptop_def [e] ->
      let e, state = erase_loc#structure_item e state in
      let state, x, gls = (ContextualConversion.(!<) structure_item).Conversion.embed ~depth state e in
      assert(gls = []);
      state, x
  | Ptop_def _ ->
      Ppxlib.Location.raise_errorf "{{:stri ...}} takes only one signature item, use {{:str ...}} for more"
  | Ptop_dir { pdir_loc = loc; _ } ->
      Ppxlib.Location.raise_errorf ~loc "{{:stri ...}} cannot contain a #directive"

let () = Quotation.register_named_quotation ~name:"stri" stri_quotation

let sigi_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.interface (Lexing.from_string s) in
  match e with
  | [e] ->
      let e, state = erase_loc#signature_item e state in
      let state, x, gls = (ContextualConversion.(!<) signature_item).Conversion.embed ~depth state e in
      assert(gls = []);
      state, x
  | _ ->
      Ppxlib.Location.raise_errorf "{{:sigi ...}} takes only one signature item, use {{:sig ...}} for more"

let () = Quotation.register_named_quotation ~name:"sigi" stri_quotation

let structure_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.implementation (Lexing.from_string s) in
  let e, state = erase_loc#structure e state in
  let state, x, gls = (ContextualConversion.(!<) structure).Conversion.embed ~depth state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"str" structure_quotation

let signature_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.interface (Lexing.from_string s) in
  let e, state = erase_loc#signature e state in
  let state, x, gls = (ContextualConversion.(!<) signature).Conversion.embed ~depth state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"sig" signature_quotation


open Ppxlib

let arg_program t =
  match Driver.Cookies.get t "program" Ast_pattern.(estring __) with
  | Some p -> program_src := p
  | _ -> ()

let arg_typecheck t =
  match Driver.Cookies.get t "typecheck" Ast_pattern.(__) with
  | Some _ -> typecheck := true
  | _ -> ()

let arg_debug t =
  match Driver.Cookies.get t "debug" Ast_pattern.(__) with
  | Some _ -> debug := true
  | _ -> ()

let () =
  Driver.Cookies.add_handler arg_program;
  Driver.register_transformation
    ~impl:map_structure
    "elpi"