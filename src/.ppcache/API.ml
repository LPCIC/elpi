(*02b4f581e688efce20aa37de517a1147f85853f8 *src/API.ml --cookie elpi_trace="false"*)
#1 "src/API.ml"
module type Runtime  = module type of Runtime_trace_off
let r = ref ((module Runtime_trace_off) : (module Runtime))
let set_runtime b =
  (match b with
   | true -> r := ((module Runtime_trace_on) : (module Runtime))
   | false -> r := ((module Runtime_trace_off) : (module Runtime)));
  (let module R = (val !r) in
     Util.set_spaghetti_printer Data.pp_const R.Pp.pp_constant)
let set_trace argv =
  let args = Trace_ppx_runtime.Runtime.parse_argv argv in
  set_runtime (!Trace_ppx_runtime.Runtime.debug); args
module Setup =
  struct
    type builtins = (string * Data.BuiltInPredicate.declaration list)
    type elpi = (Parser.parser_state * Compiler.compilation_unit)
    let init ~builtins  ~basedir:cwd  argv =
      let new_argv = set_trace argv in
      let (new_argv, paths) =
        let rec aux args paths =
          function
          | [] -> ((List.rev args), (List.rev paths))
          | "-I"::p::rest -> aux args (p :: paths) rest
          | x::rest -> aux (x :: args) paths rest in
        aux [] [] new_argv in
      let parsing_state =
        Parser.init ~lp_syntax:Parser.lp_gramext ~paths ~cwd in
      let state = Compiler.init_state Compiler.default_flags in
      let state =
        List.fold_left
          (fun state ->
             fun (_, decls) ->
               List.fold_left
                 (fun state ->
                    function
                    | Data.BuiltInPredicate.MLCode (p, _) ->
                        Compiler.Builtins.register state p
                    | Data.BuiltInPredicate.MLData _ -> state
                    | Data.BuiltInPredicate.LPCode _ -> state
                    | Data.BuiltInPredicate.LPDoc _ -> state) state decls)
          state builtins in
      let header =
        builtins |>
          (List.map
             (fun (fname, decls) ->
                let b = Buffer.create 1024 in
                let fmt = Format.formatter_of_buffer b in
                Data.BuiltInPredicate.document fmt decls;
                Format.pp_print_flush fmt ();
                (let text = Buffer.contents b in
                 let strm = Stream.of_string text in
                 let loc = Util.Loc.initial fname in
                 try
                   Parser.parse_program_from_stream parsing_state
                     ~print_accumulated_files:false loc strm
                 with
                 | Parser.ParseError (loc, msg) ->
                     (List.iteri
                        (fun i ->
                           fun s -> Printf.eprintf "%4d: %s\n" (i + 1) s)
                        (let open Re.Str in
                           split_delim (regexp_string "\n") text);
                      Printf.eprintf "Excerpt of %s:\n%s\n" fname
                        (String.sub text loc.Util.Loc.line_starts_at
                           (let open Util.Loc in
                              loc.source_stop - loc.line_starts_at));
                      Util.anomaly ~loc msg)))) in
      let header =
        try Compiler.unit_of_ast state (List.concat header)
        with | Compiler.CompileError (loc, msg) -> Util.anomaly ?loc msg in
      ((parsing_state, header), new_argv)
    let trace args =
      match set_trace args with
      | [] -> ()
      | l ->
          Util.error
            ("Elpi_API.trace got unknown arguments: " ^ (String.concat " " l))
    let usage =
      "\nParsing options:\n" ^
        ("\t-I PATH  search for accumulated files in PATH\n" ^
           Trace_ppx_runtime.Runtime.usage)
    let set_warn = Util.set_warn
    let set_error = Util.set_error
    let set_anomaly = Util.set_anomaly
    let set_type_error = Util.set_type_error
    let set_std_formatter = Util.set_std_formatter
    let set_err_formatter fmt =
      Util.set_err_formatter fmt;
      (let open Trace_ppx_runtime.Runtime in set_trace_output TTY fmt)
  end
module EA = Ast
module Ast =
  struct
    type program = Ast.Program.t
    type query = Ast.Goal.t
    module Loc = Util.Loc
  end
module Parse =
  struct
    let program ~elpi:(ps, _)  ?(print_accumulated_files= false)  =
      Parser.parse_program ps ~print_accumulated_files
    let program_from_stream ~elpi:(ps, _)  ?(print_accumulated_files= false) 
      = Parser.parse_program_from_stream ps ~print_accumulated_files
    let goal loc s = Parser.parse_goal ~loc s
    let goal_from_stream loc s = Parser.parse_goal_from_stream ~loc s
    exception ParseError = Parser.ParseError
  end
module ED = Data
module Data =
  struct
    type term = Data.term
    type constraints = Data.constraints
    type state = Data.State.t
    type pretty_printer_context = ED.pp_ctx
    type constant = Data.constant
    module StrMap = Util.StrMap
    type 'a solution = 'a Data.solution =
      {
      assignments: term StrMap.t ;
      constraints: constraints ;
      state: state ;
      output: 'a ;
      pp_ctx: pretty_printer_context }
    type hyp = Data.clause_src = {
      hdepth: int ;
      hsrc: term }
    type hyps = hyp list
    module Constants = struct module Map = Data.Constants.Map end
  end
module Compile =
  struct
    type program = (ED.State.t * Compiler.program)
    type 'a query = 'a Compiler.query
    type 'a executable = 'a ED.executable
    type compilation_unit = Compiler.compilation_unit
    exception CompileError = Compiler.CompileError
    let program ~flags  ~elpi:(_, header)  l =
      Compiler.program_of_ast (Compiler.init_state flags) ~header
        (List.flatten l)
    let query (s, p) t = Compiler.query_of_ast s p t
    let static_check ~checker  q =
      let module R = (val !r) in
        let open R in
          Compiler.static_check
            ~exec:(execute_once ~delay_outside_fragment:false) ~checker q
    module StrSet = Util.StrSet
    type flags = Compiler.flags =
      {
      defined_variables: StrSet.t ;
      print_passes: bool }
    let default_flags = Compiler.default_flags
    let optimize = Compiler.optimize_query
    let unit ~elpi:(_, header)  ~flags  x =
      Compiler.unit_of_ast (Compiler.init_state flags) ~header x
    let assemble ~elpi:(_, header)  = Compiler.assemble_units ~header
  end
module Execute =
  struct
    type 'a outcome = 'a ED.outcome =
      | Success of 'a Data.solution 
      | Failure 
      | NoMoreSteps 
    let once ?max_steps  ?delay_outside_fragment  p =
      let module R = (val !r) in
        R.execute_once ?max_steps ?delay_outside_fragment p
    let loop ?delay_outside_fragment  p ~more  ~pp  =
      let module R = (val !r) in
        R.execute_loop ?delay_outside_fragment p ~more ~pp
  end
module Pp =
  struct
    let term pp_ctx f t =
      let module R = (val !r) in
        let open R in R.Pp.uppterm ~pp_ctx 0 [] 0 [||] f t
    let constraints pp_ctx f c =
      let module R = (val !r) in
        let open R in
          Util.pplist ~boxed:true (let open R in pp_stuck_goal ~pp_ctx) "" f
            c
    let state = ED.State.pp
    let query f c =
      let module R = (val !r) in
        let open R in
          Compiler.pp_query (fun ~depth -> R.Pp.uppterm depth [] 0 [||]) f c
    module Ast = struct let program = EA.Program.pp end
  end
module Conversion =
  struct
    type extra_goals = ED.extra_goals
    include ED.Conversion
    let (^^) t =
      {
        t with
        embed =
          (fun ~depth ->
             fun h ->
               fun c ->
                 fun s -> fun x -> t.embed ~depth ((new ctx) h#raw) c s x);
        readback =
          (fun ~depth ->
             fun h ->
               fun c ->
                 fun s -> fun x -> t.readback ~depth ((new ctx) h#raw) c s x)
      }
  end
module RawOpaqueData =
  struct
    include Util.CData
    include ED.C
    let { cin = of_char; isc = is_char; cout = to_char } as char =
      declare
        {
          data_compare = Pervasives.compare;
          data_pp = (fun fmt -> fun c -> Format.fprintf fmt "%c" c);
          data_hash = Hashtbl.hash;
          data_name = "char";
          data_hconsed = false
        }
    let of_char x = ED.mkCData (of_char x)
    let { cin = of_out_stream; isc = is_out_stream; cout = to_out_stream } as
          out_stream
      =
      declare
        {
          data_compare = (fun (_, s1) -> fun (_, s2) -> String.compare s1 s2);
          data_pp =
            (fun fmt -> fun (_, d) -> Format.fprintf fmt "<out_stream:%s>" d);
          data_hash = (fun (x, _) -> Hashtbl.hash x);
          data_name = "out_stream";
          data_hconsed = false
        }
    let of_out_stream x = ED.mkCData (of_out_stream x)
    let { cin = of_in_stream; isc = is_in_stream; cout = to_in_stream } as
          in_stream
      =
      declare
        {
          data_compare = (fun (_, s1) -> fun (_, s2) -> String.compare s1 s2);
          data_pp =
            (fun fmt -> fun (_, d) -> Format.fprintf fmt "<in_stream:%s>" d);
          data_hash = (fun (x, _) -> Hashtbl.hash x);
          data_name = "in_stream";
          data_hconsed = false
        }
    let of_in_stream x = ED.mkCData (of_in_stream x)
    type name = string
    type doc = string
    type 'a declaration =
      {
      name: name ;
      doc: doc ;
      pp: Format.formatter -> 'a -> unit ;
      compare: 'a -> 'a -> int ;
      hash: 'a -> int ;
      hconsed: bool ;
      constants: (name * 'a) list }
    let conversion_of_cdata ~name  ?(doc= "")  ~constants_map 
      { cin; isc; cout; name = c } =
      let ty = Conversion.TyName name in
      let embed ~depth:_  _ _ state x = (state, (ED.Term.CData (cin x)), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match R.deref_head ~depth t with
            | ED.Term.CData c when isc c -> (state, (cout c), [])
            | ED.Term.Const i as t when i < 0 ->
                (try
                   (state, (snd @@ (ED.Constants.Map.find i constants_map)),
                     [])
                 with
                 | Not_found -> raise (Conversion.TypeErr (ty, depth, t)))
            | t -> raise (Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        let module R = (val !r) in
          let open R in
            if doc <> ""
            then
              (ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
               Format.fprintf fmt "@\n");
            Format.fprintf fmt
              "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
            ED.Constants.Map.iter
              (fun _ ->
                 fun (c, _) ->
                   Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
              constants_map in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> pp fmt (cin x))
      }
    let declare { name; doc; pp; compare; hash; hconsed; constants } =
      let cdata =
        declare
          {
            data_compare = compare;
            data_pp = pp;
            data_hash = hash;
            data_name = name;
            data_hconsed = hconsed
          } in
      (cdata,
        (List.fold_right
           (fun (n, v) ->
              ED.Constants.Map.add
                (ED.Global_symbols.declare_global_symbol n) (n, v)) constants
           ED.Constants.Map.empty), doc)
    let declare_cdata (cd, constants_map, doc) =
      conversion_of_cdata ~name:(cd.Util.CData.name) ~doc ~constants_map cd
  end
module OpaqueData =
  struct
    type name = string
    type doc = string
    type 'a declaration = 'a RawOpaqueData.declaration =
      {
      name: name ;
      doc: doc ;
      pp: Format.formatter -> 'a -> unit ;
      compare: 'a -> 'a -> int ;
      hash: 'a -> int ;
      hconsed: bool ;
      constants: (name * 'a) list }
    let declare x =
      (x |> RawOpaqueData.declare) |> RawOpaqueData.declare_cdata
  end
module Elpi =
  struct
    type t =
      | Arg of string 
      | Ref of ED.uvar_body 
    let pp fmt handle =
      match handle with
      | Arg str -> Format.fprintf fmt "%s" str
      | Ref ub ->
          let module R = (val !r) in
            let open R in R.Pp.uppterm 0 [] 0 [||] fmt (ED.mkUVar ub 0 0)
    let show m = Format.asprintf "%a" pp m
    let equal h1 h2 =
      match (h1, h2) with
      | (Ref p1, Ref p2) -> p1 == p2
      | (Arg s1, Arg s2) -> String.equal s1 s2
      | _ -> false
    let compilation_is_over ~args  k =
      match k with
      | Ref _ -> assert false
      | Arg s -> Ref (Util.StrMap.find s args)
    let uvk =
      ED.State.declare ~name:"elpi:uvk" ~pp:(Util.StrMap.pp pp)
        ~clause_compilation_is_over:(fun x -> Util.StrMap.empty)
        ~goal_compilation_is_over:(fun ~args ->
                                     fun x ->
                                       Some
                                         (Util.StrMap.map
                                            (compilation_is_over ~args) x))
        ~compilation_is_over:(fun _ -> None)
        ~execution_is_over:(fun _ -> None)
        ~init:(fun () -> Util.StrMap.empty)
    let fresh_name =
      let i = ref 0 in fun () -> incr i; Printf.sprintf "_uvk_%d_" (!i)
    let alloc_Elpi name state =
      if ED.State.get ED.while_compiling state
      then
        let (state, _arg) = Compiler.mk_Arg ~name ~args:[] state in
        (state, (Arg name))
      else (let module R = (val !r) in (state, (Ref (ED.oref ED.dummy))))
    let make ?name  state =
      match name with
      | None -> alloc_Elpi (fresh_name ()) state
      | Some name ->
          (try (state, (Util.StrMap.find name (ED.State.get uvk state)))
           with
           | Not_found ->
               let (state, k) = alloc_Elpi name state in
               ((ED.State.update uvk state (Util.StrMap.add name k)), k))
    let get ~name  state =
      try Some (Util.StrMap.find name (ED.State.get uvk state))
      with | Not_found -> None
  end
module RawData =
  struct
    type constant = ED.Term.constant
    type builtin = ED.Term.constant
    type uvar_body = ED.Term.uvar_body
    type term = ED.Term.term
    type view =
      | Const of constant 
      | Lam of term 
      | App of constant * term * term list 
      | Cons of term * term 
      | Nil 
      | Builtin of builtin * term list 
      | CData of RawOpaqueData.t 
      | UnifVar of Elpi.t * term list 
    let rec look ~depth  t =
      let module R = (val !r) in
        let open R in
          match R.deref_head ~depth t with
          | ED.Term.Arg _|ED.Term.AppArg _ -> assert false
          | ED.Term.AppUVar (ub, 0, args) -> UnifVar ((Ref ub), args)
          | ED.Term.AppUVar (ub, lvl, args) ->
              look ~depth (R.expand_appuv ub ~depth ~lvl ~args)
          | ED.Term.UVar (ub, lvl, ano) ->
              look ~depth (R.expand_uv ub ~depth ~lvl ~ano)
          | ED.Term.Discard ->
              let ub = ED.oref ED.dummy in
              UnifVar ((Ref ub), (R.mkinterval 0 depth 0))
          | x -> Obj.magic x
    let kool =
      function
      | UnifVar (Ref ub, args) -> ED.Term.AppUVar (ub, 0, args)
      | UnifVar (Arg _, _) -> assert false
      | x -> Obj.magic x[@@inline ]
    let mkConst n = let module R = (val !r) in R.mkConst n
    let mkLam = ED.Term.mkLam
    let mkApp = ED.Term.mkApp
    let mkCons = ED.Term.mkCons
    let mkNil = ED.Term.mkNil
    let mkDiscard = ED.Term.mkDiscard
    let mkBuiltin = ED.Term.mkBuiltin
    let mkCData = ED.Term.mkCData
    let mkAppL x l = let module R = (val !r) in R.mkAppL x l
    let mkGlobal i =
      if i >= 0 then Util.anomaly "mkGlobal: got a bound variable"; mkConst i
    let mkBound i =
      if i < 0 then Util.anomaly "mkBound: got a global constant"; mkConst i
    let cmp_builtin i j = i - j
    module Constants =
      struct
        let declare_global_symbol = ED.Global_symbols.declare_global_symbol
        let show c = ED.Constants.show c
        let eqc = ED.Global_symbols.eqc
        let orc = ED.Global_symbols.orc
        let andc = ED.Global_symbols.andc
        let rimplc = ED.Global_symbols.rimplc
        let pic = ED.Global_symbols.pic
        let sigmac = ED.Global_symbols.sigmac
        let implc = ED.Global_symbols.implc
        let cutc = ED.Global_symbols.cutc
        let ctypec = ED.Global_symbols.ctypec
        let spillc = ED.Global_symbols.spillc
        module Map = ED.Constants.Map
        module Set = ED.Constants.Set
      end
    let of_term x = x
    type suspended_goal = ED.suspended_goal =
      {
      context: Data.hyps ;
      goal: (int * term) }
    type constraints = Data.constraints
    let constraints l =
      let module R = (val !r) in
        let open R in
          Util.map_filter (fun x -> R.get_suspended_goal x.ED.kind) l
    let no_constraints = []
    let mkUnifVar handle ~args  state =
      match handle with
      | Elpi.Ref ub -> ED.Term.mkAppUVar ub 0 args
      | Elpi.Arg name -> Compiler.get_Arg state ~name ~args
  end
module FlexibleData =
  struct
    module Elpi = Elpi
    module type Host  =
      sig
        type t
        val compare : t -> t -> int
        val pp : Format.formatter -> t -> unit
        val show : t -> string
      end
    let uvmap_no = ref 0
    module Map(T:Host) =
      struct
        open Util
        module H2E = (Map.Make)(T)
        type t =
          {
          h2e: Elpi.t H2E.t ;
          e2h_compile: T.t StrMap.t ;
          e2h_run: T.t PtrMap.t }
        let empty =
          {
            h2e = H2E.empty;
            e2h_compile = StrMap.empty;
            e2h_run = (PtrMap.empty ())
          }
        let add uv v { h2e; e2h_compile; e2h_run } =
          let h2e = H2E.add v uv h2e in
          match uv with
          | Elpi.Ref ub ->
              { h2e; e2h_compile; e2h_run = (PtrMap.add ub v e2h_run) }
          | Arg s ->
              { h2e; e2h_run; e2h_compile = (StrMap.add s v e2h_compile) }
        let elpi v { h2e } = H2E.find v h2e
        let host handle { e2h_compile; e2h_run } =
          match handle with
          | Elpi.Ref ub -> PtrMap.find ub e2h_run
          | Arg s -> StrMap.find s e2h_compile
        let remove_both handle v { h2e; e2h_compile; e2h_run } =
          let h2e = H2E.remove v h2e in
          match handle with
          | Elpi.Ref ub ->
              { h2e; e2h_compile; e2h_run = (PtrMap.remove ub e2h_run) }
          | Arg s ->
              { h2e; e2h_run; e2h_compile = (StrMap.remove s e2h_compile) }
        let remove_elpi k m = let v = host k m in remove_both k v m
        let remove_host v m = let handle = elpi v m in remove_both handle v m
        let filter f { h2e; e2h_compile; e2h_run } =
          let e2h_compile =
            StrMap.filter (fun n -> fun v -> f v (H2E.find v h2e))
              e2h_compile in
          let e2h_run =
            PtrMap.filter (fun ub -> fun v -> f v (H2E.find v h2e)) e2h_run in
          let h2e = H2E.filter f h2e in { h2e; e2h_compile; e2h_run }
        let fold f { h2e } acc =
          let module R = (val !r) in
            let open R in
              let get_val =
                function
                | Elpi.Ref { ED.Term.contents = ub } when ub != ED.dummy ->
                    Some (R.deref_head ~depth:0 ub)
                | Elpi.Ref _ -> None
                | Elpi.Arg _ -> None in
              H2E.fold
                (fun k -> fun uk -> fun acc -> f k uk (get_val uk) acc) h2e
                acc
        let uvn = incr uvmap_no; !uvmap_no
        let pp fmt (m : t) =
          let pp k uv _ () =
            Format.fprintf fmt "@[<h>%a@ <-> %a@]@ " T.pp k Elpi.pp uv in
          Format.fprintf fmt "@[<v>"; fold pp m (); Format.fprintf fmt "@]"
        let show m = Format.asprintf "%a" pp m
        let uvmap =
          ED.State.declare ~name:(Printf.sprintf "elpi:uvm:%d" uvn) ~pp
            ~clause_compilation_is_over:(fun x -> empty)
            ~goal_compilation_is_over:(fun ~args ->
                                         fun { h2e; e2h_compile; e2h_run } ->
                                           let h2e =
                                             H2E.map
                                               (Elpi.compilation_is_over
                                                  ~args) h2e in
                                           let e2h_run =
                                             StrMap.fold
                                               (fun k ->
                                                  fun v ->
                                                    fun m ->
                                                      PtrMap.add
                                                        (StrMap.find k args)
                                                        v m) e2h_compile
                                               (PtrMap.empty ()) in
                                           Some
                                             {
                                               h2e;
                                               e2h_compile = StrMap.empty;
                                               e2h_run
                                             })
            ~compilation_is_over:(fun x -> Some x)
            ~execution_is_over:(fun x -> Some x) ~init:(fun () -> empty)
      end
    let uvar =
      {
        Conversion.ty = (Conversion.TyName "uvar");
        pp_doc =
          (fun fmt ->
             fun () ->
               Format.fprintf fmt "Unification variable, as the uvar keyword");
        pp = (fun fmt -> fun (k, _) -> Format.fprintf fmt "%a" Elpi.pp k);
        embed =
          (fun ~depth ->
             fun _ ->
               fun _ ->
                 fun s ->
                   fun (k, args) -> (s, (RawData.mkUnifVar k ~args s), []));
        readback =
          (fun ~depth ->
             fun _ ->
               fun _ ->
                 fun state ->
                   fun t ->
                     match RawData.look ~depth t with
                     | RawData.UnifVar (k, args) -> (state, (k, args), [])
                     | _ ->
                         raise
                           (Conversion.TypeErr ((TyName "uvar"), depth, t)))
      }
  end
module BuiltIn =
  struct
    include ED.BuiltInPredicate
    let declare ~file_name  l = (file_name, l)
    let document_fmt fmt (_, l) = ED.BuiltInPredicate.document fmt l
    let document_file ?(header= "")  (name, l) =
      let oc = open_out name in
      let fmt = Format.formatter_of_out_channel oc in
      Format.fprintf fmt "%s%!" header;
      ED.BuiltInPredicate.document fmt l;
      Format.pp_print_flush fmt ();
      close_out oc
  end
module BuiltInData =
  struct
    let () = ()
    let int : 'h . (int, 'h) Conversion.t =
      let name = "int" in
      let doc = "" in
      let cdata = ED.C.int in
      let constants = [] in
      let constants_map = ED.Constants.Map.empty in
      let { Util.CData.cin = cin; isc; cout; name = c } = cdata in
      let ty = Conversion.TyName name in
      let embed ~depth:_  _ _ state x = (state, (ED.Term.CData (cin x)), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match R.deref_head ~depth t with
            | ED.Term.CData c when isc c -> (state, (cout c), [])
            | ED.Term.Const i as t when i < 0 ->
                (try (state, (ED.Constants.Map.find i constants_map), [])
                 with
                 | Not_found -> raise (Conversion.TypeErr (ty, depth, t)))
            | t -> raise (Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        let module R = (val !r) in
          let open R in
            if doc <> ""
            then
              (ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
               Format.fprintf fmt "@\n");
            Format.fprintf fmt
              "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
            List.iter
              (fun (c, _) ->
                 Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
              constants in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> Util.CData.pp fmt (cin x))
      }
    let float : 'h . (float, 'h) Conversion.t =
      let name = "float" in
      let doc = "" in
      let cdata = ED.C.float in
      let constants = [] in
      let constants_map = ED.Constants.Map.empty in
      let { Util.CData.cin = cin; isc; cout; name = c } = cdata in
      let ty = Conversion.TyName name in
      let embed ~depth:_  _ _ state x = (state, (ED.Term.CData (cin x)), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match R.deref_head ~depth t with
            | ED.Term.CData c when isc c -> (state, (cout c), [])
            | ED.Term.Const i as t when i < 0 ->
                (try (state, (ED.Constants.Map.find i constants_map), [])
                 with
                 | Not_found -> raise (Conversion.TypeErr (ty, depth, t)))
            | t -> raise (Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        let module R = (val !r) in
          let open R in
            if doc <> ""
            then
              (ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
               Format.fprintf fmt "@\n");
            Format.fprintf fmt
              "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
            List.iter
              (fun (c, _) ->
                 Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
              constants in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> Util.CData.pp fmt (cin x))
      }
    let string : 'h . (string, 'h) Conversion.t =
      let name = "string" in
      let doc = "" in
      let cdata = ED.C.string in
      let constants = [] in
      let constants_map = ED.Constants.Map.empty in
      let { Util.CData.cin = cin; isc; cout; name = c } = cdata in
      let ty = Conversion.TyName name in
      let embed ~depth:_  _ _ state x = (state, (ED.Term.CData (cin x)), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match R.deref_head ~depth t with
            | ED.Term.CData c when isc c -> (state, (cout c), [])
            | ED.Term.Const i as t when i < 0 ->
                (try (state, (ED.Constants.Map.find i constants_map), [])
                 with
                 | Not_found -> raise (Conversion.TypeErr (ty, depth, t)))
            | t -> raise (Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        let module R = (val !r) in
          let open R in
            if doc <> ""
            then
              (ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
               Format.fprintf fmt "@\n");
            Format.fprintf fmt
              "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
            List.iter
              (fun (c, _) ->
                 Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
              constants in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> Util.CData.pp fmt (cin x))
      }
    let loc : 'h . (Util.Loc.t, 'h) Conversion.t =
      let name = "loc" in
      let doc = "" in
      let cdata = ED.C.loc in
      let constants = [] in
      let constants_map = ED.Constants.Map.empty in
      let { Util.CData.cin = cin; isc; cout; name = c } = cdata in
      let ty = Conversion.TyName name in
      let embed ~depth:_  _ _ state x = (state, (ED.Term.CData (cin x)), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match R.deref_head ~depth t with
            | ED.Term.CData c when isc c -> (state, (cout c), [])
            | ED.Term.Const i as t when i < 0 ->
                (try (state, (ED.Constants.Map.find i constants_map), [])
                 with
                 | Not_found -> raise (Conversion.TypeErr (ty, depth, t)))
            | t -> raise (Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        let module R = (val !r) in
          let open R in
            if doc <> ""
            then
              (ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
               Format.fprintf fmt "@\n");
            Format.fprintf fmt
              "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
            List.iter
              (fun (c, _) ->
                 Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
              constants in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> Util.CData.pp fmt (cin x))
      }
    let char : 'h . (char, 'h) Conversion.t =
      let name = "char" in
      let doc = "an octect" in
      let cdata = RawOpaqueData.char in
      let constants = [] in
      let constants_map = ED.Constants.Map.empty in
      let { Util.CData.cin = cin; isc; cout; name = c } = cdata in
      let ty = Conversion.TyName name in
      let embed ~depth:_  _ _ state x = (state, (ED.Term.CData (cin x)), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match R.deref_head ~depth t with
            | ED.Term.CData c when isc c -> (state, (cout c), [])
            | ED.Term.Const i as t when i < 0 ->
                (try (state, (ED.Constants.Map.find i constants_map), [])
                 with
                 | Not_found -> raise (Conversion.TypeErr (ty, depth, t)))
            | t -> raise (Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        let module R = (val !r) in
          let open R in
            if doc <> ""
            then
              (ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
               Format.fprintf fmt "@\n");
            Format.fprintf fmt
              "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
            List.iter
              (fun (c, _) ->
                 Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
              constants in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> Util.CData.pp fmt (cin x))
      }
    let in_stream_constants = [("std_in", (stdin, "stdin"))]
    let in_stream_cmap =
      List.fold_left
        (fun m ->
           fun (c, v) ->
             let c = ED.Global_symbols.declare_global_symbol c in
             ED.Constants.Map.add c v m) ED.Constants.Map.empty
        in_stream_constants
    let in_stream : 'h . ((in_channel * string), 'h) Conversion.t =
      let name = "in_stream" in
      let doc = "" in
      let cdata = RawOpaqueData.in_stream in
      let constants = in_stream_constants in
      let constants_map = in_stream_cmap in
      let { Util.CData.cin = cin; isc; cout; name = c } = cdata in
      let ty = Conversion.TyName name in
      let embed ~depth:_  _ _ state x = (state, (ED.Term.CData (cin x)), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match R.deref_head ~depth t with
            | ED.Term.CData c when isc c -> (state, (cout c), [])
            | ED.Term.Const i as t when i < 0 ->
                (try (state, (ED.Constants.Map.find i constants_map), [])
                 with
                 | Not_found -> raise (Conversion.TypeErr (ty, depth, t)))
            | t -> raise (Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        let module R = (val !r) in
          let open R in
            if doc <> ""
            then
              (ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
               Format.fprintf fmt "@\n");
            Format.fprintf fmt
              "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
            List.iter
              (fun (c, _) ->
                 Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
              constants in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> Util.CData.pp fmt (cin x))
      }
    let out_stream_constants =
      [("std_out", (stdout, "stdout")); ("std_err", (stderr, "stderr"))]
    let out_stream_cmap =
      List.fold_left
        (fun m ->
           fun (c, v) ->
             let c = ED.Global_symbols.declare_global_symbol c in
             ED.Constants.Map.add c v m) ED.Constants.Map.empty
        out_stream_constants
    let out_stream : 'h . ((out_channel * string), 'h) Conversion.t =
      let name = "out_stream" in
      let doc = "" in
      let cdata = RawOpaqueData.out_stream in
      let constants = out_stream_constants in
      let constants_map = out_stream_cmap in
      let { Util.CData.cin = cin; isc; cout; name = c } = cdata in
      let ty = Conversion.TyName name in
      let embed ~depth:_  _ _ state x = (state, (ED.Term.CData (cin x)), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match R.deref_head ~depth t with
            | ED.Term.CData c when isc c -> (state, (cout c), [])
            | ED.Term.Const i as t when i < 0 ->
                (try (state, (ED.Constants.Map.find i constants_map), [])
                 with
                 | Not_found -> raise (Conversion.TypeErr (ty, depth, t)))
            | t -> raise (Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        let module R = (val !r) in
          let open R in
            if doc <> ""
            then
              (ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
               Format.fprintf fmt "@\n");
            Format.fprintf fmt
              "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
            List.iter
              (fun (c, _) ->
                 Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
              constants in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> Util.CData.pp fmt (cin x))
      }
    let poly ty =
      let embed ~depth:_  _ _ state x = (state, x, []) in
      let readback ~depth  _ _ state t = (state, t, []) in
      {
        Conversion.embed = embed;
        readback;
        ty = (Conversion.TyName ty);
        pp = (fun fmt -> fun _ -> Format.fprintf fmt "<poly>");
        pp_doc = (fun fmt -> fun () -> ())
      }
    let any =
      let embed ~depth:_  _ _ state x = (state, x, []) in
      let readback ~depth  _ _ state t = (state, t, []) in
      {
        Conversion.embed = embed;
        readback;
        ty = (Conversion.TyName "any");
        pp = (fun fmt -> fun _ -> Format.fprintf fmt "<any>");
        pp_doc = (fun fmt -> fun () -> ())
      }
    let nominal =
      let embed ~depth:_  _ _ state x =
        let module R = (val !r) in
          let open R in
            if x < 0 then Util.type_error "not a bound variable";
            (state, (R.mkConst x), []) in
      let readback ~depth  _ _ state t =
        let module R = (val !r) in
          let open R in
            match deref_head ~depth t with
            | ED.Const i when i >= 0 -> (state, i, [])
            | _ -> Util.type_error "not a bound variable" in
      {
        Conversion.embed = embed;
        readback;
        ty = (TyName "nominal");
        pp = (fun fmt -> fun d -> Format.fprintf fmt "%d" d);
        pp_doc = (fun fmt -> fun () -> ())
      }
    let fresh_copy t depth =
      let module R = (val !r) in
        let open R in
          let open ED in
            let rec aux d t =
              match deref_head ~depth:(depth + d) t with
              | Lam t -> mkLam (aux (d + 1) t)
              | Const c as x ->
                  if (c < 0) || (c >= depth)
                  then x
                  else
                    raise
                      (let open Conversion in
                         TypeErr ((TyName "closed term"), (depth + d), x))
              | App (c, x, xs) ->
                  if (c < 0) || (c >= depth)
                  then mkApp c (aux d x) (List.map (aux d) xs)
                  else
                    raise
                      (let open Conversion in
                         TypeErr ((TyName "closed term"), (depth + d), x))
              | UVar _|AppUVar _ as x ->
                  raise
                    (let open Conversion in
                       TypeErr ((TyName "closed term"), (depth + d), x))
              | Arg _|AppArg _ -> assert false
              | Builtin (c, xs) -> mkBuiltin c (List.map (aux d) xs)
              | CData _ as x -> x
              | Cons (hd, tl) -> mkCons (aux d hd) (aux d tl)
              | Nil as x -> x
              | Discard as x -> x in
            ((aux 0 t), depth)
    let closed ty =
      let ty = let open Conversion in TyName ty in
      let embed ~depth  _ _ state (x, from) =
        let module R = (val !r) in
          let open R in (state, (R.hmove ~from ~to_:depth ?avoid:None x), []) in
      let readback ~depth  _ _ state t = (state, (fresh_copy t depth), []) in
      {
        Conversion.embed = embed;
        readback;
        ty;
        pp =
          (fun fmt ->
             fun (t, d) ->
               let module R = (val !r) in
                 let open R in R.Pp.uppterm d [] d ED.empty_env fmt t);
        pp_doc = (fun fmt -> fun () -> ())
      }
    let map_acc f s l =
      let rec aux acc extra s =
        function
        | [] -> (s, (List.rev acc), (let open List in concat (rev extra)))
        | x::xs ->
            let (s, x, gls) = f s x in aux (x :: acc) (gls :: extra) s xs in
      aux [] [] s l
    let embed_list d ~depth  h c s l =
      let module R = (val !r) in
        let open R in
          let (s, l, eg) = map_acc (d ~depth h c) s l in
          (s, (list_to_lp_list l), eg)
    let readback_list d ~depth  h c s t =
      let module R = (val !r) in
        let open R in map_acc (d ~depth h c) s (lp_list_to_list ~depth t)
    let list d =
      let pp fmt l =
        Format.fprintf fmt "[%a]"
          (Util.pplist d.Conversion.pp ~boxed:true "; ") l in
      {
        Conversion.embed = (embed_list d.Conversion.embed);
        readback = (readback_list d.Conversion.readback);
        ty = (TyApp ("list", (d.ty), []));
        pp;
        pp_doc = (fun fmt -> fun () -> ())
      }
    let ttc = ED.Global_symbols.declare_global_symbol "tt"
    let ffc = ED.Global_symbols.declare_global_symbol "ff"
    let readback_bool ~depth  h c s t =
      let module R = (val !r) in
        let open R in
          match R.deref_head ~depth t with
          | ED.Const c when c == ttc -> (s, true, [])
          | ED.Const c when c == ffc -> (s, false, [])
          | _ ->
              raise
                (let open Conversion in TypeErr ((TyName "bool"), depth, t))
    let embed_bool ~depth  h c s t =
      let module R = (val !r) in
        let open R in
          match t with
          | true -> (s, (R.mkConst ttc), [])
          | false -> (s, (R.mkConst ffc), [])
    let bool : 'c . (bool, #Conversion.ctx as 'c) Conversion.t =
      {
        Conversion.ty = (Conversion.TyName "bool");
        pp_doc =
          (fun fmt ->
             fun () ->
               ED.BuiltInPredicate.ADT.document_adt
                 "Boolean values: tt and ff since true and false are predicates"
                 (let open Conversion in TyName "bool")
                 [("tt", "", ["bool"]); ("ff", "", ["bool"])] fmt ());
        pp = (fun fmt -> fun b -> Format.fprintf fmt "%b" b);
        embed = embed_bool;
        readback = readback_bool
      }
    type diagnostic =
      | OK 
      | ERROR of string BuiltIn.ioarg 
    let mkOK = OK
    let mkERROR s = ERROR (Data s)
    let okc = ED.Global_symbols.declare_global_symbol "ok"
    let errorc = ED.Global_symbols.declare_global_symbol "error"
    let readback_diagnostic ~depth  h c s t =
      let module R = (val !r) in
        let open R in
          match R.deref_head ~depth t with
          | ED.Const c when c == okc -> (s, OK, [])
          | ED.App (c, x, []) when c == errorc ->
              (match R.deref_head ~depth x with
               | ED.UVar _|ED.AppUVar _|ED.Discard -> (s, (ERROR NoData), [])
               | ED.CData c when RawOpaqueData.is_string c ->
                   (s, (ERROR (Data (RawOpaqueData.to_string c))), [])
               | _ ->
                   raise
                     (let open Conversion in
                        TypeErr ((TyName "diagnostic"), depth, t)))
          | _ ->
              raise
                (let open Conversion in
                   TypeErr ((TyName "diagnostic"), depth, t))
    let embed_diagnostic ~depth  h c s t =
      let module R = (val !r) in
        let open R in
          match t with
          | OK -> (s, (R.mkConst okc), [])
          | ERROR (NoData) -> assert false
          | ERROR (Data d) ->
              (s, (ED.mkApp errorc (RawOpaqueData.of_string d) []), [])
    let diagnostic =
      {
        Conversion.ty = (TyName "diagnostic");
        pp_doc =
          (fun fmt ->
             fun () ->
               ED.BuiltInPredicate.ADT.document_adt
                 "Used in builtin variants that return Coq's error rather than failing"
                 (let open Conversion in TyName "diagnostic")
                 [("ok", "Success", ["diagnostic"]);
                 ("error", "Failure", ["string"; "diagnostic"])] fmt ());
        pp =
          (fun fmt ->
             function
             | OK -> Format.fprintf fmt "OK"
             | ERROR (NoData) -> Format.fprintf fmt "ERROR _"
             | ERROR (Data s) -> Format.fprintf fmt "ERROR %S" s);
        embed = embed_diagnostic;
        readback = readback_diagnostic
      }
  end
module AlgebraicData =
  struct
    include ED.BuiltInPredicate.ADT
    type name = string
    type doc = string
    let declare x =
      let module R = (val !r) in
        ED.BuiltInPredicate.ADT.adt ~look:R.deref_head
          ~mkinterval:R.mkinterval ~mkConst:R.mkConst
          ~alloc:FlexibleData.Elpi.make ~mkUnifVar:RawData.mkUnifVar x
  end
module BuiltInPredicate =
  struct
    include ED.BuiltInPredicate
    exception No_clause = ED.No_clause
    let mkData x = Data x
    let ioarg a =
      let open Conversion in
        {
          a with
          pp =
            (fun fmt ->
               function
               | Data x -> a.pp fmt x
               | NoData -> Format.fprintf fmt "_");
          embed =
            (fun ~depth ->
               fun hyps ->
                 fun csts ->
                   fun state ->
                     function
                     | Data x -> a.embed ~depth hyps csts state x
                     | NoData -> assert false);
          readback =
            (fun ~depth ->
               fun hyps ->
                 fun csts ->
                   fun state ->
                     fun t ->
                       let module R = (val !r) in
                         let open R in
                           match R.deref_head ~depth t with
                           | ED.Term.Arg _|ED.Term.AppArg _ -> assert false
                           | ED.Term.UVar _|ED.Term.AppUVar _|ED.Term.Discard
                               -> (state, NoData, [])
                           | _ ->
                               let (state, x, gls) =
                                 a.readback ~depth hyps csts state t in
                               (state, (mkData x), gls))
        }
    let ioarg_any =
      let open Conversion in
        {
          BuiltInData.any with
          pp =
            (fun fmt ->
               function
               | Data x -> BuiltInData.any.pp fmt x
               | NoData -> Format.fprintf fmt "_");
          embed =
            (fun ~depth ->
               fun _ ->
                 fun _ ->
                   fun state ->
                     function
                     | Data x -> (state, x, [])
                     | NoData -> assert false);
          readback =
            (fun ~depth ->
               fun _ ->
                 fun _ ->
                   fun state ->
                     fun t ->
                       let module R = (val !r) in
                         match R.deref_head ~depth t with
                         | ED.Term.Discard -> (state, NoData, [])
                         | _ -> (state, (Data t), []))
        }
    module Notation =
      struct
        let (!:) x = ((), (Some x))
        let (+!) a b = (a, (Some b))
        let (?:) x = ((), x)
        let (+?) a b = (a, b)
      end
  end
module Query =
  struct
    type name = string
    type 'f arguments = 'f ED.Query.arguments =
      | N: unit arguments 
      | D: ('a, Conversion.ctx) Conversion.t * 'a * 'x arguments -> 'x
      arguments 
      | Q: ('a, Conversion.ctx) Conversion.t * name * 'x arguments -> ('a *
      'x) arguments 
    type 'x t =
      | Query of {
      predicate: name ;
      arguments: 'x arguments } 
    let compile (state, p) loc (Query { predicate; arguments }) =
      let (state, predicate) =
        Compiler.Symbols.allocate_global_symbol_str state predicate in
      let q = ED.Query.Query { predicate; arguments } in
      Compiler.query_of_data state p loc q
  end
module State =
  struct
    include ED.State
    let declare ~name  ~pp  ~init  =
      declare ~name ~pp ~init ~clause_compilation_is_over:(fun x -> x)
        ~goal_compilation_is_over:(fun ~args:_ -> fun x -> Some x)
        ~compilation_is_over:(fun x -> Some x)
        ~execution_is_over:(fun x -> Some x)
  end
module RawQuery =
  struct
    let mk_Arg = Compiler.mk_Arg
    let is_Arg = Compiler.is_Arg
    let compile (state, p) f = Compiler.query_of_term state p f
  end
module Quotation =
  struct
    include Compiler
    let declare_backtick ~name  f =
      Compiler.CustomFunctorCompilation.declare_backtick_compilation name
        (fun s -> fun x -> f s (EA.Func.show x))
    let declare_singlequote ~name  f =
      Compiler.CustomFunctorCompilation.declare_singlequote_compilation name
        (fun s -> fun x -> f s (EA.Func.show x))
    let term_at ~depth  s x = Compiler.term_of_ast ~depth s x
    let quote_syntax_runtime s q =
      let module R = (val !r) in
        Compiler.quote_syntax (`Runtime R.mkConst) s q
    let quote_syntax_compiletime s q =
      let (s, l, t) = Compiler.quote_syntax `Compiletime s q in (s, l, t)
  end
module Utils =
  struct
    let lp_list_to_list ~depth  t =
      let module R = (val !r) in let open R in lp_list_to_list ~depth t
    let list_to_lp_list tl =
      let module R = (val !r) in let open R in list_to_lp_list tl
    let get_assignment =
      function
      | Elpi.Arg _ -> assert false
      | Elpi.Ref { ED.contents = t } ->
          let module R = (val !r) in if t == ED.dummy then None else Some t
    let move ~from  ~to_  t =
      let module R = (val !r) in
        let open R in R.hmove ~from ~to_ ?avoid:None t
    let beta ~depth  t args =
      let module R = (val !r) in
        let open R in R.deref_appuv ~from:depth ~to_:depth ?avoid:None args t
    let error = Util.error
    let type_error = Util.type_error
    let anomaly = Util.anomaly
    let warn = Util.warn
    let printf = Util.printf
    let eprintf = Util.eprintf
    let clause_of_term ?name  ?graft  ~depth  loc term =
      let open EA in
        let module Data = ED.Term in
          let module R = (val !r) in
            let open R in
              let rec aux d ctx t =
                match R.deref_head ~depth:d t with
                | Data.Const i when (i >= 0) && (i < depth) ->
                    error "program_of_term: the term is not closed"
                | Data.Const i when i < 0 -> Term.mkCon (ED.Constants.show i)
                | Data.Const i -> Util.IntMap.find i ctx
                | Data.Lam t ->
                    let s = "x" ^ (string_of_int d) in
                    let ctx = Util.IntMap.add d (Term.mkCon s) ctx in
                    Term.mkLam s (aux (d + 1) ctx t)
                | Data.App (c, x, xs) ->
                    let c = aux d ctx (R.mkConst c) in
                    let x = aux d ctx x in
                    let xs = List.map (aux d ctx) xs in
                    Term.mkApp loc (c :: x :: xs)
                | Data.Arg _|Data.AppArg _ -> assert false
                | Data.Cons (hd, tl) ->
                    let hd = aux d ctx hd in
                    let tl = aux d ctx tl in Term.mkSeq [hd; tl]
                | Data.Nil -> Term.mkNil
                | Data.Builtin (c, xs) ->
                    let c = aux d ctx (R.mkConst c) in
                    let xs = List.map (aux d ctx) xs in
                    Term.mkApp loc (c :: xs)
                | Data.CData x -> Term.mkC x
                | Data.UVar _|Data.AppUVar _ ->
                    error "program_of_term: the term contains uvars"
                | Data.Discard -> Term.mkCon "_" in
              let attributes =
                (match name with | Some x -> [Clause.Name x] | None -> []) @
                  (match graft with
                   | Some (`After, x) -> [Clause.After x]
                   | Some (`Before, x) -> [Clause.Before x]
                   | None -> []) in
              [Program.Clause
                 {
                   Clause.loc = loc;
                   attributes;
                   body = (aux depth Util.IntMap.empty term)
                 }]
    let map_acc = BuiltInData.map_acc
    module type Show  = Util.Show
    module type Show1  = Util.Show1
    module Map = Util.Map
    module Set = Util.Set
  end
module RawPp =
  struct
    let term depth fmt t =
      let module R = (val !r) in
        let open R in R.Pp.uppterm depth [] 0 ED.empty_env fmt t
    let constraints f c =
      let module R = (val !r) in
        let open R in
          Util.pplist ~boxed:true (R.pp_stuck_goal ?pp_ctx:None) "" f c
    let list = Util.pplist
    module Debug =
      struct
        let term depth fmt t =
          let module R = (val !r) in
            let open R in R.Pp.ppterm depth [] 0 ED.empty_env fmt t
        let show_term = ED.show_term
      end
  end
module PPX =
  struct
    module Doc =
      struct
        let comment = ED.BuiltInPredicate.pp_comment
        let kind fmt ty ~doc  =
          ED.BuiltInPredicate.ADT.document_kind fmt ty doc
        let constructor fmt ~name  ~doc  ~ty  ~args  =
          ED.BuiltInPredicate.ADT.document_constructor fmt name doc
            (List.map ED.Conversion.show_ty_ast (args @ [ty]))
        let adt ~doc  ~ty  ~args  =
          ED.BuiltInPredicate.ADT.document_adt doc ty
            (List.map
               (fun (n, s, a) ->
                  (n, s, (List.map ED.Conversion.show_ty_ast (a @ [ty]))))
               args)
        let show_ty_ast = ED.Conversion.show_ty_ast
      end
    let readback_int ~depth  h c s x =
      BuiltInData.int.Conversion.readback ~depth ((new Conversion.ctx) h#raw)
        c s x
    let readback_float ~depth  h c s x =
      BuiltInData.float.Conversion.readback ~depth
        ((new Conversion.ctx) h#raw) c s x
    let readback_string ~depth  h c s x =
      BuiltInData.string.Conversion.readback ~depth
        ((new Conversion.ctx) h#raw) c s x
    let readback_list = BuiltInData.readback_list
    let readback_loc ~depth  h c s x =
      BuiltInData.loc.Conversion.readback ~depth ((new Conversion.ctx) h#raw)
        c s x
    let readback_nominal ~depth  h c s x =
      BuiltInData.nominal.Conversion.readback ~depth
        ((new Conversion.ctx) h#raw) c s x
    let readback_bool ~depth  h c s x =
      BuiltInData.bool.Conversion.readback ~depth
        ((new Conversion.ctx) h#raw) c s x
    let readback_char ~depth  h c s x =
      BuiltInData.char.Conversion.readback ~depth
        ((new Conversion.ctx) h#raw) c s x
    let embed_int ~depth  h c s x =
      BuiltInData.int.Conversion.embed ~depth ((new Conversion.ctx) h#raw) c
        s x
    let embed_float ~depth  h c s x =
      BuiltInData.float.Conversion.embed ~depth ((new Conversion.ctx) h#raw)
        c s x
    let embed_string ~depth  h c s x =
      BuiltInData.string.Conversion.embed ~depth ((new Conversion.ctx) h#raw)
        c s x
    let embed_list = BuiltInData.embed_list
    let embed_loc ~depth  h c s x =
      BuiltInData.loc.Conversion.embed ~depth ((new Conversion.ctx) h#raw) c
        s x
    let embed_nominal ~depth  h c s x =
      BuiltInData.nominal.Conversion.embed ~depth
        ((new Conversion.ctx) h#raw) c s x
    let embed_bool ~depth  h c s x =
      BuiltInData.bool.Conversion.embed ~depth ((new Conversion.ctx) h#raw) c
        s x
    let embed_char ~depth  h c s x =
      BuiltInData.char.Conversion.embed ~depth ((new Conversion.ctx) h#raw) c
        s x
    type context_description =
      | C: ('a, 'k, 'c) Conversion.context -> context_description 
    let readback_context
      { Conversion.conv = conv; to_key; push; is_entry_for_nominal; init }
      ctx ~depth  hyps constraints state =
      let module CMap = RawData.Constants.Map in
        let filtered_hyps =
          List.fold_left
            (fun m ->
               fun hyp ->
                 match is_entry_for_nominal hyp with
                 | None -> m
                 | Some idx ->
                     (if CMap.mem idx m
                      then
                        Utils.type_error
                          "more than one context entry for the same nominal";
                      CMap.add idx hyp m)) CMap.empty hyps in
        let rec aux state gls i =
          if i = depth
          then (state, (List.concat (List.rev gls)))
          else
            if not (CMap.mem i filtered_hyps)
            then aux state gls (i + 1)
            else
              (let hyp = CMap.find i filtered_hyps in
               let hyp_depth = hyp.Data.hdepth in
               let (state, (nominal, t), gls_t) =
                 conv.Conversion.readback ~depth:hyp_depth ctx constraints
                   state hyp.Data.hsrc in
               assert (nominal = i);
               (let s = to_key ~depth:hyp_depth t in
                let state =
                  push ~depth:i state s
                    { Conversion.entry = t; depth = hyp_depth } in
                aux state (gls_t :: gls) (i + 1))) in
        let state = init state in aux state [] 0
  end

