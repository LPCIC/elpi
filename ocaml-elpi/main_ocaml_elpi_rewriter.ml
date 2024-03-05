open Elpi.API
open Ocaml_ast_for_elpi

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) parsetree_declaration

let mapper_src = {|
namespace ppx {

pred map.list i:(A -> B -> prop), i:list A, o:list B.
map.list _ [] [].
map.list F [X|XS] [Y|YS] :- F X Y, map.list F XS YS.

pred map.option i:(A -> B -> prop), i:option A, o:option B.
map.option _ none none.
map.option F (some X) (some Y) :- F X Y.

pred map.pair i:(A1 -> B1 -> prop), i:(A2 -> B2 -> prop), i:pair A1 A2, o:pair B1 B2.
map.pair F1 F2 (pr X1 X2) (pr Y1 Y2) :- F1 X1 Y1, F2 X2 Y2.

pred map.triple i:(A1 -> B1 -> prop), i:(A2 -> B2 -> prop), i:(A3 -> B3 -> prop), i:triple A1 A2 A3, o:triple B1 B2 B3.
map.triple F1 F2 F3 (triple X1 X2 X3) (triple Y1 Y2 Y3) :- F1 X1 Y1, F2 X2 Y2, F3 X3 Y3.

pred map.quadruple i:(A1 -> B1 -> prop), i:(A2 -> B2 -> prop), i:(A3 -> B3 -> prop), i:(A4 -> B4 -> prop), i:quadruple A1 A2 A3 A4, o:quadruple B1 B2 B3 B4.
map.quadruple F1 F2 F3 F4 (quadruple X1 X2 X3 X4) (quadruple Y1 Y2 Y3 Y4) :- F1 X1 Y1, F2 X2 Y2, F3 X3 Y3, F4 X4 Y4.

pred map.quintuple i:(A1 -> B1 -> prop), i:(A2 -> B2 -> prop), i:(A3 -> B3 -> prop), i:(A4 -> B4 -> prop), i:(A5 -> B5 -> prop), i:quintuple A1 A2 A3 A4 A5, o:quintuple B1 B2 B3 B4 B5.
map.quintuple F1 F2 F3 F4 F5 (quintuple X1 X2 X3 X4 X5) (quintuple Y1 Y2 Y3 Y4 Y5) :- F1 X1 Y1, F2 X2 Y2, F3 X3 Y3, F4 X4 Y4, F5 X5 Y5.

}
|}

let mapper = String.concat "\n" (mapper_src :: parsetree_mapper)

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
  let elpi = Setup.init ~builtins:[builtin;Elpi.Builtin.std_builtins] ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  BuiltIn.document_file builtin;
  if !debug then
    ignore @@ Setup.trace ["-trace-on";"tty";"stderr";"-trace-only";"user";"-trace-only-pred";"map";"-trace-at";"run";"1";"99999"];
  let program = Parse.program ~elpi ~files:[!program_src] in
  let mapper =
    Parse.program_from ~elpi ~loc:(Ast.Loc.initial "mapper") (Lexing.from_string mapper) in
  let program = Compile.program ~elpi ~flags:Compile.default_flags [program;mapper] in
  let query =
    let open Query in
    compile program (Ast.Loc.initial "ppx") @@
      CQuery ("map.structure", DC(structure,s,(QC(structure,"Result",NC))),new ctx_for_structure [],RawData.no_constraints) in
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
    method! location_stack l (st : State.t) = [], st
  end
;;

let expression_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.expression (Lexing.from_string s) in
  let e, state = erase_loc#expression e state in
  let ctx = new ctx_for_expression [] state in
  let csts = RawData.no_constraints in
  let state, x, gls = (expression).ContextualConversion.embed ~depth ctx csts state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"expr" expression_quotation
let () = Quotation.set_default_quotation expression_quotation

let pattern_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.pattern (Lexing.from_string s) in
  let e, state = erase_loc#pattern e state in
  let ctx = new ctx_for_pattern [] state in
  let csts = RawData.no_constraints in
  let state, x, gls = (pattern).ContextualConversion.embed ~depth ctx csts state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"pat" pattern_quotation

let type_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.core_type (Lexing.from_string s) in
  let e, state = erase_loc#core_type e state in
  let ctx = new ctx_for_core_type [] state in
  let csts = RawData.no_constraints in
  let state, x, gls = (core_type).ContextualConversion.embed ~depth ctx csts state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"type" type_quotation

let stri_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.toplevel_phrase (Lexing.from_string s) in
  match e with
  | Ptop_def [e] ->
      let e, state = erase_loc#structure_item e state in
      let ctx = new ctx_for_structure_item [] state in
      let csts = RawData.no_constraints in
      let state, x, gls = (structure_item).ContextualConversion.embed ~depth ctx csts state e in
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
      let ctx = new ctx_for_signature_item [] state in
      let csts = RawData.no_constraints in
      let state, x, gls = (signature_item).ContextualConversion.embed ~depth ctx csts state e in
      assert(gls = []);
      state, x
  | _ ->
      Ppxlib.Location.raise_errorf "{{:sigi ...}} takes only one signature item, use {{:sig ...}} for more"

let () = Quotation.register_named_quotation ~name:"sigi" stri_quotation

let structure_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.implementation (Lexing.from_string s) in
  let e, state = erase_loc#structure e state in
  let ctx = new ctx_for_structure [] state in
  let csts = RawData.no_constraints in
  let state, x, gls = (structure).ContextualConversion.embed ~depth ctx csts state e in
  assert(gls = []);
  state, x

let () = Quotation.register_named_quotation ~name:"str" structure_quotation

let signature_quotation ~depth state _loc s =
  let e = Ppxlib.Parse.interface (Lexing.from_string s) in
  let e, state = erase_loc#signature e state in
  let ctx = new ctx_for_signature [] state in
  let csts = RawData.no_constraints in
  let state, x, gls = (signature).ContextualConversion.embed ~depth ctx csts state e in
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
