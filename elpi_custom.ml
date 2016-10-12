(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)


open Elpi_runtime;;
open Elpi_util;;
open Elpi_runtime.Pp;;
open Elpi_runtime.Constants;;
module F = Elpi_ast.Func;;

let register_eval, lookup_eval =
 let (evals : ('a, term list -> term) Hashtbl.t)
   =
     Hashtbl.create 17 in
 (fun s -> Hashtbl.add evals (fst (funct_of_ast (F.from_string s)))),
 Hashtbl.find evals
;;

(* To avoid adding another primitive constant to the type term, we
   introduce bijective maps between {in,out}_streams and integers *)

(* The map stores pairs in_stream * char option, which is the lookahead *)
let add_in_stream,get_in_stream,set_lookahead =
 let fresh = ref (-1) in
 let streams = ref Elpi_ptmap.empty in
 (fun s -> incr fresh ; streams := Elpi_ptmap.add !fresh (s,None) !streams; !fresh),
 (fun i -> Elpi_ptmap.find i !streams),
 (fun i c ->
   try streams := Elpi_ptmap.add i (fst (Elpi_ptmap.find i !streams),c) !streams
   with Not_found -> anomaly "setting the lookahead for an unknown channel")

let add_out_stream,get_out_stream =
 let fresh = ref (-1) in
 let streams = ref Elpi_ptmap.empty in
 (fun s -> incr fresh ; streams := Elpi_ptmap.add !fresh s !streams ; !fresh),
 (fun i -> Elpi_ptmap.find i !streams)

let cstdin = add_in_stream stdin;;
let cstdout= add_out_stream stdout;;
let cstderr = add_out_stream stderr;;

(* Traverses the expression evaluating all custom evaluable functions *)
let rec eval depth =
 function
    Lam _
  | Custom _ -> error "Evaluation of a lambda abstraction or custom predicate"
  | Arg _
  | AppArg _ -> anomaly "Not a heap term"
  | App (hd,arg,args) ->
     let f =
      try lookup_eval hd
      with Not_found -> anomaly (show hd ^ " not evaluable") in
     let args = List.map (eval depth) (arg::args) in
     f args
  | UVar ({ contents = g }, from, args) when g != dummy ->
     eval depth (deref_uv ~from ~to_:depth args g)
  | AppUVar ({contents = t}, from, args) when t != dummy ->
     eval depth (deref_appuv ~from ~to_:depth args t)
  | UVar _
  | AppUVar _ -> error "Evaluation of a non closed term (maybe delay)"
  | Const hd ->
     let f =
      try lookup_eval hd
      with Not_found -> anomaly (show hd ^ " not evaluable") in
     f []
  | Nil | Cons _ -> assert false (* TODO? *)
  | CData _ as x -> x
;;

let rec deref_head depth = function
  | UVar ({ contents = g }, from, args) when g != dummy ->
     deref_head depth (deref_uv ~from ~to_:depth args g)
  | AppUVar ({contents = t}, from, args) when t != dummy ->
     deref_head depth (deref_appuv ~from ~to_:depth args t)
  | x -> x

let register_evals l f = List.iter (fun i -> register_eval i f) l;;

let _ =
  let open CData in
  register_eval "std_in" (function
   | [] -> CData (cint.cin cstdin)
   | _ -> type_error "Wrong arguments to stin") ;
  register_eval "std_out" (function
   | [] -> CData (cint.cin cstdout)
   | _ -> type_error "Wrong arguments to stout") ;
  register_eval "std_err" (function
   | [] -> CData (cint.cin cstderr)
   | _ -> type_error "Wrong arguments to sterr") ;
  register_evals [ "-" ; "i-" ; "r-" ] (function
   | [ CData x ; CData y ] when ty2 cint x y -> CData(morph2 cint (-) x y)
   | [ CData x ; CData y ] when ty2 cfloat x y -> CData(morph2 cfloat (-.) x y)
   | _ -> type_error "Wrong arguments to -/i-/r-") ;
  register_evals [ "+" ; "i+" ; "r+" ] (function
   | [ CData x ; CData y ] when ty2 cint x y -> CData(morph2 cint (+) x y)
   | [ CData x ; CData y ] when ty2 cfloat x y -> CData(morph2 cfloat (+.) x y)
   | _ -> type_error "Wrong arguments to +/i+/r+") ;
  register_eval "*" (function
   | [ CData x ; CData y ] when ty2 cint x y -> CData(morph2 cint ( * ) x y)
   | [ CData x ; CData y ] when ty2 cfloat x y -> CData(morph2 cfloat ( *.) x y)
   | _ -> type_error "Wrong arguments to *") ;
  register_eval "/" (function
   | [ CData x ; CData y ] when ty2 cfloat x y -> CData(morph2 cfloat ( /.) x y)
   | _ -> type_error "Wrong arguments to /") ;
  register_eval "mod" (function
   | [ CData x ; CData y ] when ty2 cint x y -> CData(morph2 cint (mod) x y)
   | _ -> type_error "Wrong arguments to mod") ;
  register_eval "div" (function
   | [ CData x ; CData y ] when ty2 cint x y -> CData(morph2 cint (/) x y)
   | _ -> type_error "Wrong arguments to div") ;
  register_eval "^" (function
   | [ CData x ; CData y ] when ty2 cstring x y ->
         CData(morph2 cstring
           (fun x y -> F.(from_string (show x ^ show y))) x y)
   | _ -> type_error "Wrong arguments to ^") ;
  register_evals [ "~" ; "i~" ; "r~" ] (function
   | [ CData x ] when cint.isc x -> CData(morph1 cint (~-) x)
   | [ CData x ] when cfloat.isc x -> CData(morph1 cfloat (~-.) x)
   | _ -> type_error "Wrong arguments to ~/i~/r~") ;
  register_evals [ "abs" ; "iabs" ; "rabs" ] (function
   | [ CData x ] when cint.isc x -> CData(map cint cint abs x)
   | [ CData x ] when cfloat.isc x -> CData(map cfloat cfloat abs_float x)
   | _ -> type_error "Wrong arguments to abs/iabs/rabs") ;
  register_eval "int_to_real" (function
   | [ CData x ] when cint.isc x -> CData(map cint cfloat float_of_int x)
   | _ -> type_error "Wrong arguments to int_to_real") ;
  register_eval "sqrt" (function
   | [ CData x ] when cfloat.isc x -> CData(map cfloat cfloat sqrt x)
   | _ -> type_error "Wrong arguments to sqrt") ;
  register_eval "sin" (function
   | [ CData x ] when cfloat.isc x -> CData(map cfloat cfloat sqrt x)
   | _ -> type_error "Wrong arguments to sin") ;
  register_eval "cos" (function
   | [ CData x ] when cfloat.isc x -> CData(map cfloat cfloat cos x)
   | _ -> type_error "Wrong arguments to cosin") ;
  register_eval "arctan" (function
   | [ CData x ] when cfloat.isc x -> CData(map cfloat cfloat atan x)
   | _ -> type_error "Wrong arguments to arctan") ;
  register_eval "ln" (function
   | [ CData x ] when cfloat.isc x -> CData(map cfloat cfloat log x)
   | _ -> type_error "Wrong arguments to ln") ;
  register_eval "floor" (function
   | [ CData x ] when cfloat.isc x ->
         CData(map cfloat cint (fun x -> int_of_float (floor x)) x)
   | _ -> type_error "Wrong arguments to floor") ;
  register_eval "ceil" (function
   | [ CData x ] when cfloat.isc x ->
         CData(map cfloat cint (fun x -> int_of_float (ceil x)) x)
   | _ -> type_error "Wrong arguments to ceil") ;
  register_eval "truncate" (function
   | [ CData x ] when cfloat.isc x -> CData(map cfloat cint truncate x)
   | _ -> type_error "Wrong arguments to truncate") ;
  register_eval "size" (function
   | [ CData x ] when cstring.isc x ->
         CData(map cstring cint (fun x -> String.length (F.show x)) x)
   | _ -> type_error "Wrong arguments to size") ;
  register_eval "chr" (function
   | [ CData x ] when cint.isc x ->
         CData(map cint cstring
           (fun x -> F.from_string (String.make 1 (char_of_int x))) x)
   | _ -> type_error "Wrong arguments to chr") ;
  register_eval "string_to_int" (function
   | [ CData x ] when cstring.isc x &&
                      String.length (F.show (cstring.cout x)) = 1 ->
       CData(map cstring cint (fun x -> int_of_char (F.show x).[0]) x)
   | _ -> type_error "Wrong arguments to string_to_int") ;
  register_eval "substring" (function
   | [ CData x ; CData i ; CData j ] when cstring.isc x && ty2 cint i j ->
       let x = cstring.cout x and i = cint.cout i and j = cint.cout j in
       if i >= 0 && j >= 0 && String.length (F.show x) >= i+j then
         CData(cstring.cin (F.from_string (String.sub (F.show x) i j)))
       else type_error "Wrong arguments to substring"
   | _ -> type_error "Wrong argument type to substring") ;
  register_eval "int_to_string" (function
   | [ CData x ] when cint.isc x ->
         CData(map cint cstring (fun x -> (F.from_string (string_of_int x))) x)
   | _ -> type_error "Wrong arguments to int_to_string") ;
  register_eval "real_to_string" (function
   | [ CData x ] when cfloat.isc x ->
         CData(map cfloat cstring (fun x -> F.from_string(string_of_float x)) x)
   | _ -> type_error "Wrong arguments to real_to_string")
;;

let really_input ic s ofs len =
  let rec unsafe_really_input read ic s ofs len =
    if len <= 0 then read else begin
      let r = input ic s ofs len in
      if r = 0
      then read
      else unsafe_really_input (read+r) ic s (ofs + r) (len - r)
    end
  in
  if ofs < 0 || len < 0 || ofs > String.length s - len
  then invalid_arg "really_input"
  else unsafe_really_input 0 ic s ofs len

type polyop = {
  p : 'a. 'a -> 'a -> bool;
  psym : string;
  pname : string;
}

let _ =
  let open CData in
  register_custom "$delay" (fun ~depth ~env p -> function
    | [t1; t2] ->
      (match is_flex t2 with
        | Some v2 -> delay_goal ~depth p ~goal:t1 ~on:[v2]; []
        | None ->
            let v2 =
              List.map (function
               | Some x -> x
               | None -> type_error
            "the second arg of $delay must be flexible or a list of flexibles")
              (List.map is_flex (lp_list_to_list t2)) in
            delay_goal ~depth p ~goal:t1 ~on:v2; [])
    | _ -> type_error "$delay takes 2 arguments"
    );
  register_custom "$constraint" (fun ~depth ~env p -> function
    | [t1; t2] ->
      (match is_flex t2 with
        | Some v2 -> declare_constraint ~depth p ~goal:t1 ~on:[v2]; []
        | None ->
            let v2 =
              List.map (function
               | Some x -> x
               | None -> type_error
            "the second arg of $constraint must be flexible or a list of flexibles")
              (List.map is_flex (lp_list_to_list t2)) in
            declare_constraint ~depth p ~goal:t1 ~on:v2; [])
    | _ -> type_error "$constraint takes 2 arguments"
    );
  register_custom "$dprint" (fun ~depth ~env _ args ->
    Format.fprintf Format.std_formatter "@[<hov 1>%a@]@\n%!"
     (pplist (ppterm depth [] 0 env) " ") args ;
    []) ;
  register_custom "$print" (fun ~depth ~env _ args ->
    Format.fprintf Format.std_formatter "@[<hov 1>%a@]@\n%!"
     (pplist (uppterm depth [] 0 env) " ") args ;
    []) ;
  register_custom "$counter" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
       let open CData in
       (match eval depth t1 with
           CData s when cstring.isc s ->
            (try
              let v = Elpi_trace.get_cur_step (F.show (cstring.cout s)) in
               [ App(eqc, t2, [CData (cint.cin v)]) ]
             with Not_found -> raise No_clause)
         | _ -> type_error "bad argument to $counter")
    | _ -> type_error "$counter takes 2 arguments") ;
  register_custom "$print_delayed" (fun ~depth ~env _ args ->
    print_delayed () ;
    []) ;
  register_custom "$is_flex" (fun ~depth ~env:_ _ args ->
    let rec is_flex = function
      | UVar ({contents=t},vardepth,args) when t != dummy ->
         is_flex (deref_uv ~from:vardepth ~to_:depth args t)
      | AppUVar ({contents=t},vardepth,args) when t != dummy ->
         is_flex (deref_appuv ~from:vardepth ~to_:depth args t)
      | UVar _ | AppUVar _ -> true
      | _ -> false in
    match args with
    | [t1] -> if is_flex t1 then [] else raise No_clause
    | _ -> type_error "$is_flex takes 1 argument") ;
  register_custom "$is_name" (fun ~depth ~env:_ _ args ->
    let rec is_name = function
      | UVar ({contents=t},vardepth,args) when t != dummy ->
         is_name (deref_uv ~from:vardepth ~to_:depth args t)
      | AppUVar ({contents=t},vardepth,args) when t != dummy ->
         is_name (deref_appuv ~from:vardepth ~to_:depth args t)
      | Const n when n >= 0 -> true
      | _ -> false in
    match args with
    | [t1] -> if is_name t1 then [] else raise No_clause
    | _ -> type_error "$is_name takes 1 argument") ;
  register_custom "$llam_unif" (fun ~depth ~env _ args ->
    match args with
    | [t1;t2] -> (try if llam_unify depth env depth t1 t2 then [] else raise No_clause with _ -> raise No_clause)
    | _ -> type_error "$llam_unif takes 2 argument") ;
  register_custom "$gettimeofday" (fun ~depth ~env:_ _ -> function
    | [t1] -> [ App (eqc, t1, [CData(cfloat.cin (Unix.gettimeofday ()))])]
    | _ -> type_error "$gettimeofday takes 1 argument") ;
  register_custom "$closed" (fun ~depth ~env:_ _ -> function
    | [t1] -> [ App (eqc, t1, [UVar(oref dummy,0,0)]) ]
    | _ -> type_error "$closed takes 1 argument") ;
  register_custom "$lt" (fun ~depth ~env:_ _ args ->
    let rec get_constant = function
      | Const c -> c
      | UVar ({contents=t},vardepth,args) when t != dummy ->
         get_constant (deref_uv ~from:vardepth ~to_:depth args t)
      | AppUVar ({contents=t},vardepth,args) when t != dummy ->
         get_constant (deref_appuv ~from:vardepth ~to_:depth args t)
      | _ -> error "$lt takes constants as arguments" in
    match args with
    | [t1; t2] ->
        let t1 = get_constant t1 in
        let t2 = get_constant t2 in
        let is_lt = if t1 < 0 && t2 < 0 then t2 < t1 else t1 < t2 in
        if not is_lt then raise No_clause else []
    | _ -> type_error "$lt takes 2 arguments") ;
(* FG: this should replace $lt *)
  register_custom "$level" (fun ~depth ~env:_ _ args ->
    let rec get_constant = function
      | Const c -> c
      | UVar ({contents=t},vardepth,args) when t != dummy ->
         get_constant (deref_uv ~from:vardepth ~to_:depth args t)
      | AppUVar ({contents=t},vardepth,args) when t != dummy ->
         get_constant (deref_appuv ~from:vardepth ~to_:depth args t)
      | _ -> error "$level takes a constant as first argument" in
    match args with
    | [t1; t2] ->
        let l1 = get_constant t1 in
        [ App (eqc, t2, [CData (cint.cin l1)])]
    | _ -> type_error "$level takes 2 arguments") ;
(* FG: end *)
  List.iter (fun { p; psym; pname } ->
  register_custom pname (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
        let t1 = eval depth t1 in
        let t2 = eval depth t2 in
        (match t1,t2 with
         | CData x, CData y ->
             if ty2 cint x y then let out = cint.cout in
               if p (out x) (out y) then [] else raise No_clause
             else if ty2 cfloat x y then let out = cfloat.cout in
               if p (out x) (out y) then [] else raise No_clause
             else if ty2 cstring x y then let out = cstring.cout in
               if p (out x) (out y) then [] else raise No_clause
             else 
           type_error ("Wrong arguments to " ^ psym ^ " (or to " ^ pname^ ")")
         | _ ->
           type_error ("Wrong arguments to " ^ psym ^ " (or to " ^ pname^ ")"))
    | _ -> type_error (psym ^ " (or " ^ pname ^ ") takes 2 arguments"))
  ) [ { p = (<);  psym = "<";  pname = "$lt_" } ;
      { p = (>);  psym = ">";  pname = "$gt_" } ;
      { p = (<=); psym = "=<"; pname = "$le_" } ;
      { p = (>=); psym = ">="; pname = "$ge_" } ] ;
  register_custom "$getenv" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when cstring.isc s ->
            (try
              let v = Sys.getenv (F.show (cstring.cout s)) in
               [ App(eqc, t2, [CData(cstring.cin (F.from_string v))]) ]
             with Not_found -> raise No_clause)
         | _ -> type_error "bad argument to getenv (or $getenv)")
    | _ -> type_error "getenv (or $getenv) takes 2 arguments") ;
  register_custom "$system" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when cstring.isc s ->
              [ App (eqc, t2, [CData (cint.cin (Sys.command (F.show (cstring.cout s))))]) ]
         | _ -> type_error "bad argument to system (or $system)")
    | _ -> type_error "system (or $system) takes 2 arguments") ;
  register_custom "$is" (fun ~depth ~env:_ _ -> function
    | [t1; t2] -> [ App (eqc, t1, [eval depth t2]) ]
    | _ -> type_error "is (or $is) takes 2 arguments") ;
  register_custom "$open_in" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when cstring.isc s ->
            (try
              let v = open_in (F.show (cstring.cout s)) in
              let vv = add_in_stream v in
               [ App(eqc, t2, [CData (cint.cin vv)]) ]
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to open_in (or $open_in)")
    | _ -> type_error "open_in (or $open_in) takes 2 arguments") ;
  register_custom "$open_out" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when cstring.isc s ->
            (try
              let v = open_out (F.show (cstring.cout s)) in
              let vv = add_out_stream v in
               [ App(eqc, t2, [CData (cint.cin vv)]) ]
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to open_out (or $open_out)")
    | _ -> type_error "open_out (or $open_out) takes 2 arguments") ;
  register_custom "$open_append" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when cstring.isc s ->
            (try
              let v =
               open_out_gen
                [Open_wronly; Open_append; Open_creat; Open_text] 0x664
                (F.show (cstring.cout s)) in
              let vv = add_out_stream v in
               [ App(eqc, t2, [CData (cint.cin vv)]) ]
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to open_append (or $open_append)")
    | _ -> type_error "open_append (or $open_append) takes 2 arguments") ;
  register_custom "$open_string" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when cstring.isc s ->
            (try
             let filename,outch = Filename.open_temp_file "elpi" "tmp" in
             output_string outch (F.show (cstring.cout s)) ;
             close_out outch ;
             let v = open_in filename in
             Sys.remove filename ;
             let vv = add_in_stream v in
              [ App(eqc, t2, [CData(cint.cin vv)]) ]
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to open_in (or $open_in)")
    | _ -> type_error "open_in (or $open_in) takes 2 arguments") ;
  register_custom "$close_in" (fun ~depth ~env:_ _ -> function
    | [t1] ->
       (match eval depth t1 with
           CData s when cint.isc s ->
            (try close_in (fst (get_in_stream (cint.cout s))); []
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to close_in (or $close_in)")
    | _ -> type_error "close_in (or $close_in) takes 1 argument") ;
  register_custom "$close_out" (fun ~depth ~env:_ _ -> function
    | [t1] ->
       (match eval depth t1 with
           CData s when cint.isc s ->
            (try close_out(get_out_stream (cint.cout s)); []
             with Sys_error msg->error msg)
         | _ -> type_error "bad argument to close_out (or $close_out)")
    | _ -> type_error "close_out (or $close_out) takes 1 argument") ;
  register_custom "$output" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
       (match eval depth t1, eval depth t2 with
           CData n, CData s when cint.isc n && cstring.isc s ->
            (try output_string (get_out_stream (cint.cout n))
              (F.show (cstring.cout s)) ; []
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to output (or $output)")
    | _ -> type_error "output (or $output) takes 2 arguments") ;
  register_custom "$term_to_string" (fun ~depth ~env _ -> function
    | [t1; t2] ->
       Format.fprintf Format.str_formatter "%a" (uppterm depth [] 0 env) t1 ;
       let s = Format.flush_str_formatter () in
       [App(eqc,t2,[CData(cstring.cin (F.from_string s))])]
    | _ -> type_error "term_to_string (or $term_to_string) takes 2 arguments");
  register_custom "$string_to_term" (fun ~depth ~env _ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when cstring.isc s ->
            (try
              let s = Elpi_parser.parse_goal (F.show (cstring.cout s)) in
              let t = term_of_ast ~depth s in
              [App (eqc, t2, [t])]
             with
                Stream.Error msg -> prerr_endline msg; raise No_clause
              | Elpi_ast.NotInProlog -> prerr_endline "Beta redexes not allowed"; raise No_clause)
         | _ -> type_error "bad argument to string_to_term (or $string_to_term)")
    | _ -> type_error "string_to_term (or $string_to_term) takes 2 arguments");
  register_custom "$flush" (fun ~depth ~env:_ _ -> function
    | [t1] ->
       (match eval depth t1 with
           CData n when cint.isc n ->
            (try flush (get_out_stream (cint.cout n)) ; []
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to flush (or $flush)")
    | _ -> type_error "flush (or $flush) takes 2 arguments") ;
  register_custom "$halt" (fun ~depth ~env:_ _ -> function
    | [] -> exit 0
    | _ -> type_error "halt (or $halt) takes 0 arguments") ;
  register_custom "$input" (fun ~depth ~env:_ _ -> function
    | [t1 ; t2 ; t3] ->
       (match eval depth t1, eval depth t2 with
           CData s, CData n when ty2 cint s n ->
            (try
              let n = cint.cout n in
              let s = cint.cout s in
              let ch,lookahead = get_in_stream s in
              let buf = String.make n ' ' in
              let start,n =
               match lookahead with
                  None -> 0,n
                | Some c -> Bytes.set buf 0 c ; 1,n-1 in
              let read = really_input ch buf start n in
              let str = String.sub buf 0 (read + start) in
              set_lookahead s None ;
              [App (eqc, t3, [CData (cstring.cin (F.from_string str))])]
             with 
              Sys_error msg -> error msg)
         | _ -> type_error "bad argument to input (or $input)")
    | _ -> type_error "input (or $input) takes 3 arguments") ;
  register_custom "$input_line" (fun ~depth ~env:_ _ -> function
    | [t1 ; t2] ->
       (match eval depth t1 with
           CData n when cint.isc n ->
            (try
              let s = cint.cout n in
              let ch,lookahead = get_in_stream s in
              let str = try input_line ch with End_of_file -> "" in
              set_lookahead s None ;
              let str =
               match lookahead with
                  None -> str
                | Some c -> String.make 1 c ^ str in
              [App (eqc, t2, [CData (cstring.cin (F.from_string str))])]
             with 
              Sys_error msg -> error msg)
         | _ -> type_error "bad argument to input_line (or $input_line)")
    | _ -> type_error "input_line (or $input_line) takes 2 arguments") ;
  register_custom "$lookahead" (fun ~depth ~env:_ _ -> function
    | [t1 ; t2] ->
       (match eval depth t1 with
           CData n when cint.isc n ->
            (try
              let s = cint.cout n in
              let ch,lookahead = get_in_stream s in
              let c =
               match lookahead with
                  Some c -> String.make 1 c
                | None ->
                   (try
                     let c = input_char ch in
                     set_lookahead s (Some c) ;
                     String.make 1 c
                    with End_of_file -> "")
              in
              [App (eqc, t2, [CData (cstring.cin (F.from_string c))])]
             with 
              Sys_error msg -> error msg)
         | _ -> type_error "bad argument to lookahead (or $lookahead)")
    | _ -> type_error "lookahead (or $lookahead) takes 2 arguments") ;
  register_custom "$readterm" (fun ~depth ~env:_ _ -> function
    | [t1 ; t2] ->
       (match eval depth t1 with
           CData n when cint.isc n ->
            (try
              let s = cint.cout n in
              let ch,lookahead = get_in_stream s in
              let strm = Stream.of_channel ch in
              let strm =
               match lookahead with
                  Some c -> Stream.icons c strm
                | None -> strm in
              let t3 = Elpi_parser.parse_goal_from_stream strm in
              let t3 = term_of_ast ~depth t3 in
              [App (eqc, t2, [t3])]
             with 
                Sys_error msg -> error msg
              | Stream.Error msg -> prerr_endline msg; raise No_clause
              | Elpi_ast.NotInProlog -> prerr_endline "Beta redexes not allowed"; raise No_clause)
         | _ -> type_error "bad argument to readterm (or $readterm)")
    | _ -> type_error "readterm (or $readterm) takes 2 arguments") ;
  register_custom "$print_ast" (fun ~depth ~env:_ _ args -> 
    List.iter (Format.eprintf "%a" pp_term) args; []
  );
  register_custom "$eof" (fun ~depth ~env:_ _ -> function
    | [t1] ->
       (match eval depth t1 with
           CData n when cint.isc n ->
            (try
              let s = cint.cout n in
              let ch,lookahead = get_in_stream s in
              match lookahead with
                 Some c -> raise No_clause
               | None ->
                  (try
                    let c = input_char ch in
                    set_lookahead s (Some c) ;
                    raise No_clause
                   with End_of_file -> [])
             with 
              Sys_error msg -> error msg)
         | _ -> type_error "bad argument to eof (or $eof)")
    | _ -> type_error "eof (or $eof) takes 1 argument") ;

  register_custom "$is_cdata" (fun ~depth ~env:_ _ -> function
    | [t1;t2] ->
       (match deref_head depth t1 with
       | CData n -> [ App(eqc, t2, [
                snd (Elpi_runtime.Constants.funct_of_ast (F.from_string (CData.name n)))])]
       | _ -> raise No_clause)
    | _ -> type_error "$is_cdata") ;


  register_custom "$rex_match" (fun ~depth ~env:_ _ -> function
    | [t1;t2] ->
       (match deref_head depth t1, deref_head depth t2 with
       | CData rex, CData subj when cstring.isc rex && cstring.isc subj ->
           let rex = Str.regexp (Elpi_ast.Func.show (cstring.cout rex)) in
           let subj = Elpi_ast.Func.show (cstring.cout subj) in
           if Str.string_match rex subj 0 then []
           else raise No_clause
       | _ -> type_error "$rex_match")
    | _ -> type_error "$rex_match") ;

  register_custom "$rex_replace" (fun ~depth ~env:_ _ -> function
          | [t1;t2;t3;t4] ->
       (match deref_head depth t1, deref_head depth t2,  deref_head depth t3 with
       | CData rex, CData repl, CData subj when List.for_all cstring.isc [rex; repl; subj] ->
           let rex = Str.regexp (Elpi_ast.Func.show (cstring.cout rex)) in
           let repl = Elpi_ast.Func.show (cstring.cout repl) in
           let subj = Elpi_ast.Func.show (cstring.cout subj) in
           [ App(eqc, CData (cstring.cin (F.from_string (Str.global_replace rex repl subj))), [t4]) ]
       | _ -> type_error "$rex_replace not 3 strings")
    | _ -> type_error "$rex_replace not 4 args") ;

;;

let () =
  let uty = CustomConstraints.declare_constraint
    ~name:"universes"
    ~pp:(fun _ _ -> ())
    ~empty:UGraph.initial_universes in
  let { CData.cin = in_lvl; isc = is_lvl; cout = out_lvl } as clvl =
    CData.(declare {
    data_name = "universe level";
    data_pp = (fun f x -> Format.fprintf f "%s" (Univ.Level.to_string x));
    data_eq = (fun x y -> UGraph.check_eq (CustomConstraints.read uty)
      Univ.Universe.(make x) Univ.Universe.(make y));
    data_hash = Univ.Level.hash;
  }) in
  let open CData in
  let c = ref 0 in
  register_custom "$univ_eq" (fun ~depth ~env:_ _ -> function
    | [t1; t2] ->
        let t1 = eval depth t1 in
        let t2 = eval depth t2 in
        (match t1,t2 with
         | CData x, CData y when ty2 clvl x y ->
             let x = clvl.cout x and y = clvl.cout y in
             CustomConstraints.update uty (UGraph.enforce_constraint (x,Univ.Eq,y));
             []
         | _ -> type_error ("Wrong arguments to univ_eq"))
    | _ -> type_error ("Wrong arguments to univ_eq"));
  register_custom "$mk_univ" (fun ~depth ~env:_ _ -> function
    | [t1] ->
                    incr c;
                    let l = Univ.Level.make "foo" !c in
                    CustomConstraints.update uty (UGraph.add_universe l false);

                    [ App(eqc, t1, [CData (clvl.cin l)]) ]
    | _ -> type_error ("Wrong arguments to mk_univ"))

;;


        
