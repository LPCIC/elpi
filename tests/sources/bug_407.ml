open Elpi.API

let global = Ast.Loc.initial "init"
let base_str = 
  {| kind foo type. 
     external symbol mk_t : int -> foo = "1".

     type is_t foo -> int -> (pred).
     is_t (mk_t N) N.
  |}

let is_t_c = RawData.Constants.declare_global_symbol "is_t"
let mk_t_c = RawData.Constants.declare_global_symbol "mk_t"
let query = 
  Ast.Term.mkAppGlobal ~loc:global ~hdloc:global is_t_c
    (Ast.Term.mkVar ~loc:global ~hdloc:global (Ast.Name.from_string "X") []) 
    [Ast.Term.mkOpaque ~loc:global (RawOpaqueData.int.cino 4)]

let () = begin 
  let flags = { Compile.default_flags with Compile.print_units = true } in
  let elpi = Setup.init 
    ~builtins:[Elpi.Builtin.std_builtins]
    ~flags:(Compile.to_setup_flags flags)
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  let base = Parse.program_from ~elpi ~loc:global ~digest:(Digest.string "") (Lexing.from_string base_str) in
  let pgm = Compile.program ~flags ~elpi base in
  let query = Compile.optimize @@ RawQuery.compile_term pgm (fun st -> st, query) in
  match Execute.once query with
  | Execute.Success r ->
    Setup.StrMap.iter begin fun k v ->
      match RawData.look ~depth:0 v with
      | RawData.App (c, _, _) ->
        Format.printf "Solution: %a, %d, %d\n"
          (Pp.term r.pp_ctx) v
          c
          mk_t_c;
        assert(c == mk_t_c)
      | _ -> exit 1
    end r.assignments
  | _ -> exit 1
  end