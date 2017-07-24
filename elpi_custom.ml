(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Elpi_API
open Extend
open Data
open Constants
open Utils
open CustomPredicate

let register_eval, lookup_eval =
 let (evals : ('a, term list -> term) Hashtbl.t)
   =
     Hashtbl.create 17 in
 (fun s -> Hashtbl.add evals (from_stringc s)),
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
  | UVar ({ contents = g }, from, ano) when g != dummy ->
     eval depth (deref_uv ~from ~to_:depth ~ano g)
  | AppUVar ({contents = t}, from, args) when t != dummy ->
     eval depth (deref_appuv ~from ~to_:depth ~args t)
  | UVar _
  | AppUVar _ -> error "Evaluation of a non closed term (maybe delay)"
  | Const hd ->
     let f =
      try lookup_eval hd
      with Not_found -> anomaly (show hd ^ " not evaluable") in
     f []
  | (Nil | Cons _ as x) -> type_error ("Lists cannot be evaluated: " ^ Pp.Raw.show_term x)
  | CData _ as x -> x
;;

let register_evals l f = List.iter (fun i -> register_eval i f) l;;

let _ =
  let open CData in
  register_eval "std_in" (function
   | [] -> C.(of_int cstdin)
   | _ -> type_error "Wrong arguments to stin") ;
  register_eval "std_out" (function
   | [] -> C.(of_int cstdout)
   | _ -> type_error "Wrong arguments to stout") ;
  register_eval "std_err" (function
   | [] -> C.(of_int cstderr)
   | _ -> type_error "Wrong arguments to sterr") ;
  register_evals [ "-" ; "i-" ; "r-" ] (function
   | [ CData x ; CData y ] when ty2 C.int x y -> CData(morph2 C.int (-) x y)
   | [ CData x ; CData y ] when ty2 C.float x y -> CData(morph2 C.float (-.) x y)
   | _ -> type_error "Wrong arguments to -/i-/r-") ;
  register_evals [ "+" ; "i+" ; "r+" ] (function
   | [ CData x ; CData y ] when ty2 C.int x y -> CData(morph2 C.int (+) x y)
   | [ CData x ; CData y ] when ty2 C.float x y -> CData(morph2 C.float (+.) x y)
   | _ -> type_error "Wrong arguments to +/i+/r+") ;
  register_eval "*" (function
   | [ CData x ; CData y ] when ty2 C.int x y -> CData(morph2 C.int ( * ) x y)
   | [ CData x ; CData y ] when ty2 C.float x y -> CData(morph2 C.float ( *.) x y)
   | _ -> type_error "Wrong arguments to *") ;
  register_eval "/" (function
   | [ CData x ; CData y ] when ty2 C.float x y -> CData(morph2 C.float ( /.) x y)
   | _ -> type_error "Wrong arguments to /") ;
  register_eval "mod" (function
   | [ CData x ; CData y ] when ty2 C.int x y -> CData(morph2 C.int (mod) x y)
   | _ -> type_error "Wrong arguments to mod") ;
  register_eval "div" (function
   | [ CData x ; CData y ] when ty2 C.int x y -> CData(morph2 C.int (/) x y)
   | _ -> type_error "Wrong arguments to div") ;
  register_eval "^" (function
   | [ CData x ; CData y ] when ty2 C.string x y ->
         C.of_string (C.to_string x ^ C.to_string y)
   | _ -> type_error "Wrong arguments to ^") ;
  register_evals [ "~" ; "i~" ; "r~" ] (function
   | [ CData x ] when C.is_int x -> CData(morph1 C.int (~-) x)
   | [ CData x ] when C.is_float x -> CData(morph1 C.float (~-.) x)
   | _ -> type_error "Wrong arguments to ~/i~/r~") ;
  register_evals [ "abs" ; "iabs" ; "rabs" ] (function
   | [ CData x ] when C.is_int x -> CData(map C.int C.int abs x)
   | [ CData x ] when C.is_float x -> CData(map C.float C.float abs_float x)
   | _ -> type_error "Wrong arguments to abs/iabs/rabs") ;
  register_eval "int_to_real" (function
   | [ CData x ] when C.is_int x -> CData(map C.int C.float float_of_int x)
   | _ -> type_error "Wrong arguments to int_to_real") ;
  register_eval "sqrt" (function
   | [ CData x ] when C.is_float x -> CData(map C.float C.float sqrt x)
   | _ -> type_error "Wrong arguments to sqrt") ;
  register_eval "sin" (function
   | [ CData x ] when C.is_float x -> CData(map C.float C.float sqrt x)
   | _ -> type_error "Wrong arguments to sin") ;
  register_eval "cos" (function
   | [ CData x ] when C.is_float x -> CData(map C.float C.float cos x)
   | _ -> type_error "Wrong arguments to cosin") ;
  register_eval "arctan" (function
   | [ CData x ] when C.is_float x -> CData(map C.float C.float atan x)
   | _ -> type_error "Wrong arguments to arctan") ;
  register_eval "ln" (function
   | [ CData x ] when C.is_float x -> CData(map C.float C.float log x)
   | _ -> type_error "Wrong arguments to ln") ;
  register_eval "floor" (function
   | [ CData x ] when C.is_float x ->
         CData(map C.float C.int (fun x -> int_of_float (floor x)) x)
   | _ -> type_error "Wrong arguments to floor") ;
  register_eval "ceil" (function
   | [ CData x ] when C.is_float x ->
         CData(map C.float C.int (fun x -> int_of_float (ceil x)) x)
   | _ -> type_error "Wrong arguments to ceil") ;
  register_eval "truncate" (function
   | [ CData x ] when C.is_float x -> CData(map C.float C.int truncate x)
   | _ -> type_error "Wrong arguments to truncate") ;
  register_eval "size" (function
   | [ CData x ] when C.is_string x ->
         C.of_int (String.length (C.to_string x))
   | _ -> type_error "Wrong arguments to size") ;
  register_eval "chr" (function
   | [ CData x ] when C.is_int x ->
         C.of_string (String.make 1 (char_of_int (C.to_int x)))
   | _ -> type_error "Wrong arguments to chr") ;
  register_eval "string_to_int" (function
   | [ CData x ] when C.is_string x && String.length (C.to_string x) = 1 ->
       C.of_int (int_of_char (C.to_string x).[0])
   | _ -> type_error "Wrong arguments to string_to_int") ;
  register_eval "substring" (function
   | [ CData x ; CData i ; CData j ] when C.is_string x && ty2 C.int i j ->
       let x = C.to_string x and i = C.to_int i and j = C.to_int j in
       if i >= 0 && j >= 0 && String.length x >= i+j then
         C.of_string (String.sub x i j)
       else type_error "Wrong arguments to substring"
   | _ -> type_error "Wrong argument type to substring") ;
  register_eval "int_to_string" (function
   | [ CData x ] when C.is_int x ->
         C.of_string (string_of_int (C.to_int x))
   | _ -> type_error "Wrong arguments to int_to_string") ;
  register_eval "real_to_string" (function
   | [ CData x ] when C.is_float x ->
         C.of_string (string_of_float (C.to_float x))
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

(* constant x occurs in term t with level d? *)
let occurs x d t =
   let rec aux = function
     | Const c                          -> c = x
     | Lam t                            -> aux t
     | App (c, v, vs)                   -> c = x || aux v || auxs vs
     | UVar ({contents = t}, dt, n)     -> if t == dummy then x < dt+n else
                                           (x < dt && aux t) || (dt <= x && x < dt+n)
     | AppUVar ({contents = t}, dt, vs) -> if t == dummy then auxs vs else
                                           (x < dt && aux t) || auxs vs
     | Arg _
     | AppArg _                         -> anomaly "Not a heap term"
     | Custom (_, vs)                   -> auxs vs
     | Cons (v1, v2)                    -> aux v1 || aux v2
     | Nil
     | CData _                          -> false
   and auxs = function
     | []      -> false
     | t :: ts -> aux t || auxs ts
   in
   x < d && aux t

type polyop = {
  p : 'a. 'a -> 'a -> bool;
  psym : string;
  pname : string;
}

let _ =
  declare_full "$delay" (fun ~depth ~env s c -> function
    | [t1; t2] ->
      (match is_flex ~depth t2 with
        | Some v2 -> s.delay `Goal ~goal:t1 ~on:[v2]; [], c 
        | None ->
            let v2 =
              List.map (function
               | Some x -> x
               | None -> type_error
            "the second arg of $delay must be flexible or a list of flexibles")
              (List.map (is_flex ~depth) (lp_list_to_list ~depth t2)) in
            s.delay `Goal ~goal:t1 ~on:v2; [], c)
    | _ -> type_error "$delay takes 2 arguments"
    );
  declare_full "$constraint" (fun ~depth ~env s c -> function
    | [t1; t2] ->
      (match is_flex ~depth t2 with
        | Some v2 -> s.delay `Constraint ~goal:t1 ~on:[v2]; [],c
        | None ->
            let v2 =
              List.map (function
               | Some x -> x
               | None -> type_error
            "the second arg of $constraint must be flexible or a list of flexibles")
              (List.map (is_flex ~depth) (lp_list_to_list ~depth t2)) in
            s.delay `Constraint ~goal:t1 ~on:v2; [],c)
    | _ -> type_error "$constraint takes 2 arguments"
    );
  declare "$dprint" (fun ~depth ~env args ->
    Format.fprintf Format.std_formatter "@[<hov 1>%a@]@\n%!"
     (Pp.list (Pp.Raw.term depth [] 0 env) " ") args ;
    []) ;
  declare "$print" (fun ~depth ~env args ->
    Format.fprintf Format.std_formatter "@[<hov 1>%a@]@\n%!"
     (Pp.list (Pp.term depth [] 0 env) " ") args ;
    []) ;
  declare "$deref" (fun ~depth ~env args ->
    List.iter (fun x -> ignore (is_flex ~depth x)) args;
    []) ;
  declare "$counter" (fun ~depth ~env:_ -> function
    | [t1; t2] ->
       let open CData in
       (match eval depth t1 with
           CData s when C.is_string s ->
            (try
              let v = Elpi_trace.get_cur_step (C.to_string s) in
               [ App(eqc, t2, [C.(of_int v)]) ]
             with Not_found -> raise No_clause)
         | _ -> type_error "bad argument to $counter")
    | _ -> type_error "$counter takes 2 arguments") ;
  declare_full "$print_constraints" (fun ~depth ~env s c _ ->
    s.print `Constraints Format.err_formatter ;
    [],c) ;
  declare_full "$print_delayed" (fun ~depth ~env s c _ ->
    s.print `All Format.err_formatter;
    [],c) ;
  declare "$is_flex" (fun ~depth ~env:_ args ->
    match args with
    | [t1] -> if is_flex ~depth t1 <> None then [] else raise No_clause
    | _ -> type_error "$is_flex takes 1 argument") ;
  declare "$is_same_flex" (fun ~depth ~env:_ args ->
    match args with
    | [t1;t2] ->
       (match is_flex ~depth t1, is_flex ~depth t2 with
           Some p1, Some p2 when p1==p2 -> []
         | _,_ -> raise No_clause)
    | _ -> type_error "$is_same_flex takes 2 argument") ;
  declare "$is_name" (fun ~depth ~env:_ args ->
    let is_name x = match deref_head ~depth x with
      | Const n when n >= 0 -> true
      | _ -> false in
    match args with
    | [t1] -> if is_name t1 then [] else raise No_clause
    | _ -> type_error "$is_name takes 1 argument") ;
  declare "$names" (fun ~depth ~env:_ args ->
    let rec mk_local_vars a l =
      if l < 0 then a else mk_local_vars (Cons (Const l, a)) (pred l)
    in
    match args with
    | [t1] -> [App(eqc, t1, [mk_local_vars Nil (pred depth)])]
    | _    -> type_error "$names takes 1 argument") ;
  declare "$occurs" (fun ~depth ~env:_ args ->
    let occurs_in t2 t =
      match deref_head ~depth t with
      | Const n -> occurs n depth t2
      | _       -> false in
    match args with
    | [t1; t2] -> if occurs_in t2 t1 then [] else raise No_clause
    | _ -> type_error "$occurs takes 2 arguments") ;
  declare "$gettimeofday" (fun ~depth ~env:_ -> function
    | [t1] -> [ App (eqc, t1, [C.of_float (Unix.gettimeofday ())])]
    | _ -> type_error "$gettimeofday takes 1 argument") ;
  declare "$closed" (fun ~depth ~env:_ -> function
    | [t1] -> [ App (eqc, t1, [UVar(oref dummy,0,0)]) ]
    | _ -> type_error "$closed takes 1 argument") ;
  declare "$lt" (fun ~depth ~env:_ args ->
    let get_constant x = match deref_head ~depth x with
      | Const c -> c
      | _ -> error "$lt takes constants as arguments" in
    match args with
    | [t1; t2] ->
        let t1 = get_constant t1 in
        let t2 = get_constant t2 in
        let is_lt = if t1 < 0 && t2 < 0 then t2 < t1 else t1 < t2 in
        if not is_lt then raise No_clause else []
    | _ -> type_error "$lt takes 2 arguments") ;
(* FG: this should replace $lt *)
  declare "$level" (fun ~depth ~env:_ args ->
          let get_constant x = match deref_head ~depth x with
      | Const c -> c
      | _ -> error "$level takes a constant as first argument" in
    match args with
    | [t1; t2] ->
        let l1 = get_constant t1 in
        [ App (eqc, t2, [C.(of_int l1)])]
    | _ -> type_error "$level takes 2 arguments") ;
(* FG: end *)
  List.iter (fun { p; psym; pname } ->
  declare pname (fun ~depth ~env:_ -> function
    | [t1; t2] ->
        let open CData in
        let t1 = eval depth t1 in
        let t2 = eval depth t2 in
        (match t1,t2 with
         | CData x, CData y ->
             if ty2 C.int x y then let out = C.to_int in
               if p (out x) (out y) then [] else raise No_clause
             else if ty2 C.float x y then let out = C.to_float in
               if p (out x) (out y) then [] else raise No_clause
             else if ty2 C.string x y then let out = C.to_string in
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
  declare "$getenv" (fun ~depth ~env:_ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when C.is_string s ->
            (try
              let v = Sys.getenv (C.to_string s) in
               [ App(eqc, t2, [C.of_string v]) ]
             with Not_found -> raise No_clause)
         | _ -> type_error "bad argument to getenv (or $getenv)")
    | _ -> type_error "getenv (or $getenv) takes 2 arguments") ;
  declare "$system" (fun ~depth ~env:_ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when C.is_string s ->
              [ App (eqc, t2, [C.(of_int (Sys.command (C.to_string s)))]) ]
         | _ -> type_error "bad argument to system (or $system)")
    | _ -> type_error "system (or $system) takes 2 arguments") ;
  declare "$is" (fun ~depth ~env:_ -> function
    | [t1; t2] -> [ App (eqc, t1, [eval depth t2]) ]
    | _ -> type_error "is (or $is) takes 2 arguments") ;
  declare "$open_in" (fun ~depth ~env:_ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when C.is_string s ->
            (try
              let v = open_in (C.to_string s) in
              let vv = add_in_stream v in
               [ App(eqc, t2, [C.(of_int vv)]) ]
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to open_in (or $open_in)")
    | _ -> type_error "open_in (or $open_in) takes 2 arguments") ;
  declare "$open_out" (fun ~depth ~env:_ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when C.is_string s ->
            (try
              let v = open_out (C.to_string s) in
              let vv = add_out_stream v in
               [ App(eqc, t2, [C.(of_int vv)]) ]
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to open_out (or $open_out)")
    | _ -> type_error "open_out (or $open_out) takes 2 arguments") ;
  declare "$open_append" (fun ~depth ~env:_ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when C.is_string s ->
            (try
              let v =
               open_out_gen
                [Open_wronly; Open_append; Open_creat; Open_text] 0x664
                (C.to_string s) in
              let vv = add_out_stream v in
               [ App(eqc, t2, [C.(of_int vv)]) ]
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to open_append (or $open_append)")
    | _ -> type_error "open_append (or $open_append) takes 2 arguments") ;
  declare "$open_string" (fun ~depth ~env:_ -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when C.is_string s ->
            (try
             let filename,outch = Filename.open_temp_file "elpi" "tmp" in
             output_string outch (C.to_string s) ;
             close_out outch ;
             let v = open_in filename in
             Sys.remove filename ;
             let vv = add_in_stream v in
              [ App(eqc, t2, [C.of_int vv]) ]
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to open_in (or $open_in)")
    | _ -> type_error "open_in (or $open_in) takes 2 arguments") ;
  declare "$close_in" (fun ~depth ~env:_ -> function
    | [t1] ->
       (match eval depth t1 with
           CData s when C.is_int s ->
            (try close_in (fst (get_in_stream (C.to_int s))); []
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to close_in (or $close_in)")
    | _ -> type_error "close_in (or $close_in) takes 1 argument") ;
  declare "$close_out" (fun ~depth ~env:_ -> function
    | [t1] ->
       (match eval depth t1 with
           CData s when C.is_int s ->
            (try close_out(get_out_stream (C.to_int s)); []
             with Sys_error msg->error msg)
         | _ -> type_error "bad argument to close_out (or $close_out)")
    | _ -> type_error "close_out (or $close_out) takes 1 argument") ;
  declare "$output" (fun ~depth ~env:_ -> function
    | [t1; t2] ->
       (match eval depth t1, eval depth t2 with
           CData n, CData s when C.is_int n && C.is_string s ->
            (try output_string (get_out_stream (C.to_int n))
              (C.to_string s) ; []
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to output (or $output)")
    | _ -> type_error "output (or $output) takes 2 arguments") ;
  declare "$term_to_string" (fun ~depth ~env -> function
    | [t1; t2] ->
       Format.fprintf Format.str_formatter "%a" (Pp.term depth [] 0 env) t1 ;
       let s = Format.flush_str_formatter () in
       [App(eqc,t2,[C.of_string s])]
    | _ -> type_error "term_to_string (or $term_to_string) takes 2 arguments");
  declare "$string_to_term" (fun ~depth ~env -> function
    | [t1; t2] ->
       (match eval depth t1 with
           CData s when C.is_string s ->
            (try
              let s = Parse.goal (C.to_string s) in
              let t = Compile.term_at ~depth (Ast.term_of_query s) in
              [App (eqc, t2, [t])]
             with
                Stream.Error msg -> prerr_endline msg; raise No_clause
              | Elpi_ast.NotInProlog _ -> prerr_endline "Beta redexes not allowed"; raise No_clause)
         | _ -> type_error "bad argument to string_to_term (or $string_to_term)")
    | _ -> type_error "string_to_term (or $string_to_term) takes 2 arguments");
  declare "$flush" (fun ~depth ~env:_ -> function
    | [t1] ->
       (match eval depth t1 with
           CData n when C.is_int n ->
            (try flush (get_out_stream (C.to_int n)) ; []
             with Sys_error msg -> error msg)
         | _ -> type_error "bad argument to flush (or $flush)")
    | _ -> type_error "flush (or $flush) takes 2 arguments") ;
  declare "$halt" (fun ~depth ~env:_ -> function
    | [] -> exit 0
    | _ -> type_error "halt (or $halt) takes 0 arguments") ;
  declare "$input" (fun ~depth ~env:_ -> function
    | [t1 ; t2 ; t3] ->
       (match eval depth t1, eval depth t2 with
           CData s, CData n when CData.ty2 C.int s n ->
            (try
              let n = C.to_int n in
              let s = C.to_int s in
              let ch,lookahead = get_in_stream s in
              let buf = String.make n ' ' in
              let start,n =
               match lookahead with
                  None -> 0,n
                | Some c -> Bytes.set buf 0 c ; 1,n-1 in
              let read = really_input ch buf start n in
              let str = String.sub buf 0 (read + start) in
              set_lookahead s None ;
              [App (eqc, t3, [C.(of_string str)])]
             with 
              Sys_error msg -> error msg)
         | _ -> type_error "bad argument to input (or $input)")
    | _ -> type_error "input (or $input) takes 3 arguments") ;
  declare "$input_line" (fun ~depth ~env:_ -> function
    | [t1 ; t2] ->
       (match eval depth t1 with
           CData n when C.is_int n ->
            (try
              let s = C.to_int n in
              let ch,lookahead = get_in_stream s in
              let str = try input_line ch with End_of_file -> "" in
              set_lookahead s None ;
              let str =
               match lookahead with
                  None -> str
                | Some c -> String.make 1 c ^ str in
              [App (eqc, t2, [C.of_string str])]
             with 
              Sys_error msg -> error msg)
         | _ -> type_error "bad argument to input_line (or $input_line)")
    | _ -> type_error "input_line (or $input_line) takes 2 arguments") ;
  declare "$lookahead" (fun ~depth ~env:_ -> function
    | [t1 ; t2] ->
       (match eval depth t1 with
           CData n when C.is_int n ->
            (try
              let s = C.to_int n in
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
              [App (eqc, t2, [C.of_string c])]
             with 
              Sys_error msg -> error msg)
         | _ -> type_error "bad argument to lookahead (or $lookahead)")
    | _ -> type_error "lookahead (or $lookahead) takes 2 arguments") ;
  declare "$readterm" (fun ~depth ~env:_ -> function
    | [t1 ; t2] ->
       (match eval depth t1 with
           CData n when C.is_int n ->
            (try
              let s = C.to_int n in
              let ch,lookahead = get_in_stream s in
              let strm = Stream.of_channel ch in
              let strm =
               match lookahead with
                  Some c -> Stream.icons c strm
                | None -> strm in
              let t3 = Parse.goal_from_stream strm in
              let t3 = Compile.term_at ~depth (Ast.term_of_query t3) in
              [App (eqc, t2, [t3])]
             with 
                Sys_error msg -> error msg
              | Stream.Error msg -> prerr_endline msg; raise No_clause
              | Elpi_ast.NotInProlog _ -> prerr_endline "Beta redexes not allowed"; raise No_clause)
         | _ -> type_error "bad argument to readterm (or $readterm)")
    | _ -> type_error "readterm (or $readterm) takes 2 arguments") ;
  declare "$eof" (fun ~depth ~env:_ -> function
    | [t1] ->
       (match eval depth t1 with
           CData n when C.is_int n ->
            (try
              let s = C.to_int n in
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

  declare "$is_cdata" (fun ~depth ~env:_ -> function
    | [t1;t2] ->
       (match deref_head depth t1 with
       | CData n -> [ App(eqc, t2, [
               Elpi_runtime.(App(Constants.ctypec,C.of_string (CData.name n),[]))])]
       | _ -> raise No_clause)
    | _ -> type_error "$is_cdata") ;


  declare "$rex_match" (fun ~depth ~env:_ -> function
    | [t1;t2] ->
       (match deref_head depth t1, deref_head depth t2 with
       | CData rex, CData subj when C.is_string rex && C.is_string subj ->
           let rex = Str.regexp (C.to_string rex) in
           let subj = C.to_string subj in
           if Str.string_match rex subj 0 then []
           else raise No_clause
       | _ -> type_error "$rex_match")
    | _ -> type_error "$rex_match") ;

  declare "$rex_replace" (fun ~depth ~env:_ -> function
    | [t1;t2;t3;t4] ->
       (match deref_head depth t1, deref_head depth t2,  deref_head depth t3 with
       | CData rex, CData repl, CData subj when List.for_all C.is_string [rex; repl; subj] ->
           let rex = Str.regexp (C.to_string rex) in
           let repl = C.to_string repl in
           let subj = C.to_string subj in
           [ App(eqc, C.of_string (Str.global_replace rex repl subj), [t4]) ]
       | _ -> type_error "$rex_replace not 3 strings")
    | _ -> type_error "$rex_replace not 4 args") ;

   declare "$match_frozen" (fun ~depth ~env:_ -> function
     | [t1;t2] ->
       (match deref_head depth t1 with (* TODO: c is_frozen *)
       | App(_,x,xs) -> [App (eqc, t2, [list_to_lp_list (x :: xs)])]
       | Const _ -> [App (eqc, t2, [list_to_lp_list []])]
       | _ -> type_error "not a frozen")
       | [t1;t2;t3] ->
       (match deref_head depth t1 with (* TODO: c is_frozen *)
       | App(c,x,xs) -> [App (eqc, t2, [of_dbl c]);
                         App (eqc, t3, [list_to_lp_list (x :: xs)])]
       | Const _ as c -> [App (eqc, t2, [c]);
                          App (eqc, t3, [list_to_lp_list []])]
       | _ -> type_error "not a frozen")
     | _ -> type_error "$matc_frozen takes two args") ;
   
   declare "$quote_syntax" (fun ~depth ~env:_ -> function
       | [f;s;r1;r2] ->
       (match deref_head depth f, deref_head depth s with
       | CData file, CData query when C.is_string file && C.is_string query ->
           let file, query = C.to_string file, C.to_string query in
           let ap = Parse.program ~no_pervasives:false [file] in
           let aq = Parse.goal query in
           let p = Elpi_API.Compile.program [ap] in
           let q = Elpi_API.Compile.query p aq in
           let qp, qq = Compile.quote_syntax p q in
           [ App (eqc, r1, [qp]); App (eqc, r2 , [qq]) ]
       | _ -> type_error "$quote_syntax string string P Q")
     | _ -> type_error "$matc_frozen takes 4 arguments") ;
   


;;

let { CData.cin = safe_in; isc = is_safe ; cout = safe_out } = CData.declare {
  CData.data_name = "safe";
  data_pp = (fun fmt (id,l,d) ->
     Format.fprintf fmt "[safe %d: %a]_%d" id
       (Pp.list (Pp.term 0 [] 0 Elpi_data.empty_env) ";") !l d);
  data_eq = (fun (id1, _,_) (id2,_,_) -> id1 == id2);
  data_hash = (fun (id,_,_) -> id);
}

let fresh_copy t max_db depth =
  let rec aux d = function
    | Lam t -> Lam(aux (d+1) t)
    | Const c as x ->
        if c < max_db then x
        else if c - depth <= d then of_dbl (max_db + c - depth)
        else raise No_clause (* restriction *)
    | App (c,x,xs) ->
        let x = aux d x in
        let xs = List.map (aux d) xs in
        if c < max_db then App(c,x,xs)
        else if c - depth <= d then App(max_db + c - depth,x,xs)
        else raise No_clause (* restriction *)
    | (Arg _ | AppArg _) ->
        type_error "$stash takes only heap terms"
    | (UVar (r,_,_) | AppUVar(r,_,_)) when r.contents == dummy ->
        type_error "$stash takes only ground terms"
    | UVar(r,vd,ano) ->
        aux d (deref_uv ~from:vd ~to_:(depth+d) ~ano r.contents)
    | AppUVar(r,vd,args) ->
        aux d (deref_appuv ~from:vd ~to_:(depth+d) ~args r.contents)
    | Custom (c,xs) -> Custom(c,List.map (aux d) xs)
    | CData _ as x -> x
    | Cons (hd,tl) -> Cons(aux d hd, aux d tl)
    | Nil as x -> x
  in
    aux 0 t

let () =
   let safeno = ref 0 in

   declare "$new_safe" (fun ~depth ~env:_ -> function
     | [t] -> 
         incr safeno;
         [App (eqc, t, [CData (safe_in (!safeno,ref [],depth))]) ]
     | _ -> type_error "$new_safe takes one arg");

   declare "$stash" (fun ~depth ~env:_ -> function
     | [t1;t2] ->
          (match deref_head depth t1 with
          | CData c when is_safe c ->
              let _,l, ld = safe_out c in
              l := fresh_copy t2 ld depth :: !l;
              []
          | _ -> type_error "$stash takes a safe")
     | _ -> type_error "$stash takes two args");

   declare "$open_safe" (fun ~depth ~env:_ -> function
     | [t1;t2] ->
          (match deref_head depth t1 with
          | CData c when is_safe c ->
              let _,l, ld = safe_out c in
              [App (eqc, t2, [list_to_lp_list (List.rev !l)]) ]
          | _ -> type_error "$stash takes a safe")
     | _ -> type_error "$stash takes two args");

;;

