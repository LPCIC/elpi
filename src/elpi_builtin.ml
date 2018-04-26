(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_API
open Extend
open Data
open Constants
open Utils
open BuiltInPredicate
open Notation

module Str = Re_str

let { CData.cin = istream_in; isc = is_istream ; cout = istream_out } as in_stream = CData.declare {
  CData.data_name = "in_stream";
  data_pp = (fun fmt (_,d) -> Format.fprintf fmt "<in_stream:%s>" d);
  data_eq = (fun (x,_) (y,_) -> x = y);
  data_hash = (fun (x,_) -> Hashtbl.hash x);
  data_hconsed = false;
}
let in_stream =
  let constants =
    Map.empty |> Map.add (from_stringc "std_in") (stdin,"stdin") in
  data_of_cdata ~name:"@in_stream" ~constants in_stream

let { CData.cin = ostream_in; isc = is_ostream ; cout = ostream_out } as out_stream = CData.declare {
  CData.data_name = "out_stream";
  data_pp = (fun fmt (_,d) -> Format.fprintf fmt "<out_stream:%s>" d);
  data_eq = (fun (x,_) (y,_) -> x = y);
  data_hash = (fun (x,_) -> Hashtbl.hash x);
  data_hconsed = false;
}
let out_stream =
  let constants =
    Map.empty
    |> Map.add (from_stringc "std_out") (stdout,"stdout")
    |> Map.add (from_stringc "std_err") (stderr,"stderr") in
  data_of_cdata ~name:"@out_stream" ~constants out_stream

let register_eval, lookup_eval =
 let (evals : ('a, view list -> term) Hashtbl.t)
   =
     Hashtbl.create 17 in
 (fun s -> Hashtbl.add evals (from_stringc s)),
 Hashtbl.find evals
;;

(* Traverses the expression evaluating all custom evaluable functions *)
let rec eval depth t =
  match look ~depth t with
  | Lam _ -> type_error "Evaluation of a lambda abstraction"
  | Builtin _ -> type_error "Evaluation of built-in predicate"
  | Arg _
  | AppArg _ -> anomaly "Not a heap term"
  | App (hd,arg,args) ->
     let f =
      try lookup_eval hd
      with Not_found ->
        function
        | [] -> assert false
        | x::xs -> mkApp hd (kool x) (List.map kool xs)  in
     let args = List.map (fun x -> look ~depth (eval depth x)) (arg::args) in
     f args
  | UVar _
  | AppUVar _ -> error "Evaluation of a non closed term (maybe delay)"
  | Const hd as x ->
     let f =
      try lookup_eval hd
      with Not_found -> fun _ -> kool x in
     f []
  | (Nil | Cons _ as x) ->
      type_error ("Lists cannot be evaluated: " ^ Pp.Raw.show_term (kool x))
  | Discard -> type_error "_ cannot be evaluated"
  | CData _ as x -> kool x
;;

let register_evals l f = List.iter (fun i -> register_eval i f) l;;

let _ =
  let open CData in
  register_evals [ "-" ; "i-" ; "r-" ] (function
   | [ CData x; CData y ] when ty2 C.int x y -> mkCData(morph2 C.int (-) x y)
   | [ CData x; CData y ] when ty2 C.float x y -> mkCData(morph2 C.float (-.) x y)
   | _ -> type_error "Wrong arguments to -/i-/r-") ;
  register_evals [ "+" ; "i+" ; "r+" ] (function
   | [ CData x; CData y ] when ty2 C.int x y -> mkCData(morph2 C.int (+) x y)
   | [ CData x; CData y ] when ty2 C.float x y -> mkCData(morph2 C.float (+.) x y)
   | _ -> type_error "Wrong arguments to +/i+/r+") ;
  register_eval "*" (function
   | [ CData x; CData y ] when ty2 C.int x y -> mkCData(morph2 C.int ( * ) x y)
   | [ CData x; CData y] when ty2 C.float x y -> mkCData(morph2 C.float ( *.) x y)
   | _ -> type_error "Wrong arguments to *") ;
  register_eval "/" (function
   | [ CData x; CData y] when ty2 C.float x y -> mkCData(morph2 C.float ( /.) x y)
   | _ -> type_error "Wrong arguments to /") ;
  register_eval "mod" (function
   | [ CData x; CData y ] when ty2 C.int x y -> mkCData(morph2 C.int (mod) x y)
   | _ -> type_error "Wrong arguments to mod") ;
  register_eval "div" (function
   | [ CData x; CData y ] when ty2 C.int x y -> mkCData(morph2 C.int (/) x y)
   | _ -> type_error "Wrong arguments to div") ;
  register_eval "^" (function
   | [ CData x; CData y ] when ty2 C.string x y ->
         C.of_string (C.to_string x ^ C.to_string y)
   | _ -> type_error "Wrong arguments to ^") ;
  register_evals [ "~" ; "i~" ; "r~" ] (function
   | [ CData x ] when C.is_int x -> mkCData(morph1 C.int (~-) x)
   | [ CData x ] when C.is_float x -> mkCData(morph1 C.float (~-.) x)
   | _ -> type_error "Wrong arguments to ~/i~/r~") ;
  register_evals [ "abs" ; "iabs" ; "rabs" ] (function
   | [ CData x ] when C.is_int x -> mkCData(map C.int C.int abs x)
   | [ CData x ] when C.is_float x -> mkCData(map C.float C.float abs_float x)
   | _ -> type_error "Wrong arguments to abs/iabs/rabs") ;
  register_eval "int_to_real" (function
   | [ CData x ] when C.is_int x -> mkCData(map C.int C.float float_of_int x)
   | _ -> type_error "Wrong arguments to int_to_real") ;
  register_eval "sqrt" (function
   | [ CData x ] when C.is_float x -> mkCData(map C.float C.float sqrt x)
   | _ -> type_error "Wrong arguments to sqrt") ;
  register_eval "sin" (function
   | [ CData x ] when C.is_float x -> mkCData(map C.float C.float sqrt x)
   | _ -> type_error "Wrong arguments to sin") ;
  register_eval "cos" (function
   | [ CData x ] when C.is_float x -> mkCData(map C.float C.float cos x)
   | _ -> type_error "Wrong arguments to cosin") ;
  register_eval "arctan" (function
   | [ CData x ] when C.is_float x -> mkCData(map C.float C.float atan x)
   | _ -> type_error "Wrong arguments to arctan") ;
  register_eval "ln" (function
   | [ CData x ] when C.is_float x -> mkCData(map C.float C.float log x)
   | _ -> type_error "Wrong arguments to ln") ;
  register_eval "floor" (function
   | [ CData x ] when C.is_float x ->
         mkCData(map C.float C.int (fun x -> int_of_float (floor x)) x)
   | _ -> type_error "Wrong arguments to floor") ;
  register_eval "ceil" (function
   | [ CData x ] when C.is_float x ->
         mkCData(map C.float C.int (fun x -> int_of_float (ceil x)) x)
   | _ -> type_error "Wrong arguments to ceil") ;
  register_eval "truncate" (function
   | [ CData x ] when C.is_float x -> mkCData(map C.float C.int truncate x)
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
  if ofs < 0 || len < 0 || ofs > Bytes.length s - len
  then invalid_arg "really_input"
  else unsafe_really_input 0 ic s ofs len

(* constant x occurs in term t with level d? *)
let occurs x d t =
   let rec aux t = match unsafe_look t with
     | Const c                          -> c = x
     | Lam t                            -> aux t
     | App (c, v, vs)                   -> c = x || aux v || auxs vs
     | UVar (t, dt, n)     ->
         begin match get_assignment t with
         | None -> x < dt+n
         | Some t -> (x < dt && aux t) || (dt <= x && x < dt+n)
         end
     | AppUVar (t, dt, vs) ->
         begin match get_assignment t with
         | None -> auxs vs
         | Some t -> (x < dt && aux t) || auxs vs
         end
     | Arg _
     | AppArg _                         -> anomaly "Not a heap term"
     | Builtin (_, vs)                   -> auxs vs
     | Cons (v1, v2)                    -> aux v1 || aux v2
     | Nil
     | Discard
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


(** Core built-in ********************************************************* *)

let core_builtins = [

  LPDoc " == Core builtins =====================================";

  LPDoc " -- Logic --";

  LPCode "pred true.";
  LPCode "true.";

  LPCode "pred fail.";
  LPCode "pred false.";

  LPCode "pred (=) o:A, o:A.";
  LPCode "X = X.";

  LPCode "(A ; _) :- A.";
  LPCode "(_ ; B) :- B.";

  LPCode "kind list type -> type.";
  LPCode "type (::) X -> list X -> list X.";
  LPCode "type ([]) list X.";
  LPCode "type (:-) prop -> prop -> prop.";
  LPCode "type (:-) prop -> list prop -> prop.";
  LPCode "type (,) variadic prop prop.";
  LPCode "type uvar A.";
  LPCode "type (as) A -> A -> A.";
  LPCode "type (=>) prop -> prop -> prop.";
  LPCode "type (=>) list prop -> prop -> prop.";

  LPDoc " -- Control --";

  (* This is not implemented here, since the API had no access to the
   * choice points *)
  LPCode "external pred !. % The cut operator";

  LPCode "pred not i:prop.";
  LPCode "not X :- X, !, fail.";
  LPCode "not _.";

  (* These are not implemented here since the API has no access to the
   * store of syntactic constraints *)
  LPCode ("% [declare_constraint C Key] declares C with Key (a variable or\n" ^
          "% a list of variables).\n"^
          "external pred declare_constraint i:any, i:any.");
  LPCode "external pred print_constraints. % prints all constraints";

  MLCode(Pred("halt", Easy "halts the program",
  (fun ~depth -> error "halt")),
  DocAbove);

  LPCode "stop :- halt.";

  LPDoc " -- Evaluation --";

  MLCode(Pred("is_",
    Out(poly "A", "Out",
    In(poly "A",  "Expr",
    Easy          "unifies Out with the value of Expr")),
  (fun _ t ~depth -> !:(eval depth t))),
  DocAbove);

  LPCode "pred (is) o:A, i:A.";
  LPCode "X is Y :- is_ X Y.";

  LPCode "type (-) A -> A -> A.";

  LPCode "type (^) string -> string -> string.";

  LPCode "type (+) int -> int -> int.";
  LPCode "type (+) float -> float -> float.";

  LPCode "type (*) int -> int -> int.";
  LPCode "type (*) float -> float -> float.";
    
  LPDoc " -- Arithmetic tests --";

  ] @ List.map (fun { p; psym; pname } ->

  MLCode(Pred(pname,
    In(poly "A","X",
    In(poly "A","Y",
    Easy     ("checks if X " ^ psym ^ " Y. Works for string, int and float"))),
  (fun t1 t2 ~depth ->
     let open CData in
     let t1 = look ~depth (eval depth t1) in
     let t2 = look ~depth (eval depth t2) in
     match t1, t2 with
     | CData x, CData y ->
          if ty2 C.int x y then let out = C.to_int in
            if p (out x) (out y) then () else raise No_clause
          else if ty2 C.float x y then let out = C.to_float in
            if p (out x) (out y) then () else raise No_clause
          else if ty2 C.string x y then let out = C.to_string in
            if p (out x) (out y) then () else raise No_clause
          else 
        type_error ("Wrong arguments to " ^ psym ^ " (or to " ^ pname^ ")")
     (* HACK: grundlagen.elpi uses the "age" of constants *)
     | Const t1, Const t2 ->
        let is_lt = if t1 < 0 && t2 < 0 then p t2 t1 else p t1 t2 in
        if not is_lt then raise No_clause else ()
     | _ -> type_error ("Wrong arguments to " ^psym^ " (or to " ^pname^ ")"))),
  DocAbove))

    [ { p = (<);  psym = "<";  pname = "lt_" } ;
      { p = (>);  psym = ">";  pname = "gt_" } ;
      { p = (<=); psym = "=<"; pname = "le_" } ;
      { p = (>=); psym = ">="; pname = "ge_" } ]

  @ [

  LPCode "X  < Y  :- lt_ X Y.";
  LPCode "X i< Y  :- lt_ X Y.";
  LPCode "X r< Y  :- lt_ X Y.";
  LPCode "X s< Y  :- lt_ X Y.";
  LPCode "X  > Y  :- gt_ X Y.";
  LPCode "X i> Y  :- gt_ X Y.";
  LPCode "X r> Y  :- gt_ X Y.";
  LPCode "X s> Y  :- gt_ X Y.";
  LPCode "X  =< Y :- le_ X Y.";
  LPCode "X i=< Y :- le_ X Y.";
  LPCode "X r=< Y :- le_ X Y.";
  LPCode "X s=< Y :- le_ X Y.";
  LPCode "X  >= Y :- ge_ X Y.";
  LPCode "X i>= Y :- ge_ X Y.";
  LPCode "X r>= Y :- ge_ X Y.";
  LPCode "X s>= Y :- ge_ X Y.";

  ]
;;

(** Standard lambda Prolog I/O built-in *********************************** *)

let io_builtins = [

  LPDoc " == I/O builtins =====================================";

  LPDoc " -- I/O --";

  LPCode "macro @in_stream :- ctype \"in_stream\".";
  LPCode "macro @out_stream :- ctype \"out_stream\".";
  LPCode "type std_in @in_stream.";
  LPCode "type std_out @out_stream.";
  LPCode "type std_err @out_stream.";
     
  MLCode(Pred("open_in",
    In(string,     "FileName",
    Out(in_stream, "InStream",
    Easy           "opens FileName for input")),
  (fun s _ ~depth ->
     try !:(open_in s,s)
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("open_out",
    In(string,      "FileName",
    Out(out_stream, "OutStream",
    Easy            "opens FileName for output")),
  (fun s _ ~depth ->
     try !:(open_out s,s)
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("open_append",
    In(string,      "FileName",
    Out(out_stream, "OutStream",
    Easy            "opens FileName for output in append mode")),
  (fun s _ ~depth ->
     let flags = [Open_wronly; Open_append; Open_creat; Open_text] in
     try !:(open_out_gen flags 0x664 s,s)
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("close_in",
    In(in_stream, "InStream",
    Easy          "closes input stream InStream"),
  (fun (i,_) ~depth ->
     try close_in i
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("close_out",
    In(out_stream, "OutStream",
    Easy           "closes output stream OutStream"),
  (fun (o,_) ~depth ->
     try close_out o
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("output",
    In(out_stream, "OutStream",
    In(string,     "Data",
    Easy           "writes Data to OutStream")),
  (fun (o,_) s ~depth ->
     try output_string o s
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("flush",
    In(out_stream, "OutStream",
    Easy           "flush all output not yet finalized to OutStream"),
  (fun (o,_) ~depth ->
     try flush o
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("input",
    In(in_stream, "InStream",
    In(int,       "Bytes",
    Out(string,   "Data",
    Easy          "reads Bytes from InStream"))),
  (fun (i,_) n _ ~depth ->
     let buf = Bytes.make n ' ' in
     try
       let read = really_input i buf 0 n in
       let str = Bytes.sub buf 0 read in
       !:(Bytes.to_string str)
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("input_line",
    In(in_stream, "InStream",
    Out(string,   "Line",
    Easy          "reads a full line from InStream")),
  (fun (i,_) _ ~depth ->
     try !:(input_line i)
     with
     | End_of_file -> !:""
     | Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("eof",
    In(in_stream, "InStream",
    Easy          "checks if no more data can be read from InStream"),
  (fun (i,_) ~depth ->
     try
       let pos = pos_in i in
       let _ = input_char i in
       Pervasives.seek_in i pos;
       raise No_clause
     with
     | End_of_file -> ()
     | Sys_error msg -> error msg)),
  DocAbove);

  LPDoc " -- System --";

  MLCode(Pred("gettimeofday",
    Out(float, "T",
    Easy       "sets T to the number of seconds elapsed since 1/1/1970"),
  (fun _ ~depth -> !:(Unix.gettimeofday ()))),
  DocAbove);

  MLCode(Pred("getenv",
    In(string,  "VarName",
    Out(string, "Out",
    Easy      ("unifies Out with the value of VarName in the process' "^
               "environment. Fails if no such environment variable exists"))),
  (fun s _ ~depth ->
     try !:(Sys.getenv s)
     with Not_found -> raise No_clause)),
  DocAbove);

  MLCode(Pred("system",
    In(string, "Command",
    Out(int,   "RetVal",
    Easy       "executes Command and sets RetVal to the exit code")),
  (fun s _ ~depth -> !:(Sys.command s))),
  DocAbove);

  LPDoc " -- Debugging --";

  MLCode(Pred("term_to_string",
    In(any,     "T",
    Out(string, "S",
    Easy        "prints T to S")),
  (fun t _ ~depth ->
     let b = Buffer.create 1024 in
     let fmt = Format.formatter_of_buffer b in
     Format.fprintf fmt "%a" (Pp.term depth) t ;
     Format.pp_print_flush fmt ();
       !:(Buffer.contents b))),
  DocAbove);

  ]
;;

(** Standard lambda Prolog built-in ************************************** *)

let lp_builtins = [

  LPDoc "== Lambda Prolog builtins =====================================";

  LPDoc " -- Extra I/O --";

  MLCode(Pred("open_string",
    In(string,     "DataIn",
    Out(in_stream, "InStream",
    Easy           "opens DataIn as an input stream")),
  (fun data _ ~depth ->
     try
       let filename, outch = Filename.open_temp_file "elpi" "tmp" in
       output_string outch data;
       close_out outch ;
       let v = open_in filename in
       Sys.remove filename ;
       !:(v,"<string>")
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("lookahead",
    In(in_stream, "InStream",
    Out(string,   "NextChar",
    Easy          "peeks one byte from InStream")),
  (fun (i,_) _ ~depth ->
     try
       let pos = pos_in i in
       let c = input_char i in
       Pervasives.seek_in i pos;
       !:(String.make 1 c)
     with
     | End_of_file -> !:""
     | Sys_error msg -> error msg)),
  DocAbove);

  LPDoc " -- Hacks --";

  MLCode(Pred("string_to_term",
    In(string, "S",
    Out(any,   "T",
    Easy       "parses a term T from S")),
  (fun s _ ~depth ->
     try
       let t = Parse.goal s in
       let t = Compile.term_at ~depth t in
       !:t
     with
     | Stream.Error _ -> raise No_clause
     | Elpi_ast.NotInProlog _ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("readterm",
    In(in_stream, "InStream",
    Out(any,      "T",
    Easy          "reads T from InStream")),
  (fun (i,_) _ ~depth ->
     try
       let strm = Stream.of_channel i in
       let t = Parse.goal_from_stream strm in
       let t = Compile.term_at ~depth t in
       !:t
     with 
     | Sys_error msg -> error msg
     | Stream.Error _ -> raise No_clause
     | Elpi_ast.NotInProlog _ -> raise No_clause)),
  DocAbove);

  LPCode "printterm S T :- term_to_string T T1, output S T1.";
  LPCode "read S :- flush std_out, input_line std_in X, string_to_term X S.";

  ]
;;

(** ELPI specific built-in ************************************************ *)

let elpi_builtins = [

  LPDoc "== Elpi builtins =====================================";

  MLCode(Pred("dprint",
    VariadicIn(any, "prints raw terms (debugging)"),
  (fun args ~depth _ { custom_constraints = cc } ->
     Format.fprintf Format.std_formatter "@[<hov 1>%a@]@\n%!"
       (Pp.list (Pp.Raw.term depth) " ") args ;
     cc, ())),
  DocAbove);

  MLCode(Pred("print",
    VariadicIn(any,"prints terms"),
  (fun args ~depth _ { custom_constraints = cc } ->
     Format.fprintf Format.std_formatter "@[<hov 1>%a@]@\n%!"
       (Pp.list (Pp.term depth) " ") args ;
     cc, ())),
  DocAbove);

  MLCode(Pred("counter",
    In (string,"Name",
    Out(int,   "Value",
    Easy       "reads the Value of a trace point Name")),
  (fun s _ ~depth:_ -> !:(Elpi_trace.get_cur_step s))),
  DocAbove);


  MLCode(Pred("rex_match",
    In(string, "Rex",
    In(string, "Subject",
    Easy      ("checks if Subject matches Rex. "^
               "Matching is based on OCaml's Str library"))),
  (fun rex subj ~depth ->
     let rex = Str.regexp rex in
     if Str.string_match rex subj 0 then () else raise No_clause)),
  DocAbove);

  MLCode(Pred("rex_replace",
    In(string,  "Rex",
    In(string,  "Replacement",
    In(string,  "Subject",
    Out(string, "Out",
    Easy   ("Out is obtained by replacing all occurrences of Rex with "^
            "Replacement in Subject. See also OCaml's Str.global_replace"))))),
  (fun rex repl subj _ ~depth ->
     let rex = Str.regexp rex in
     !:(Str.global_replace rex repl subj))),
  DocAbove);

   MLCode(Pred("quote_syntax",
     In(string, "FileName",
     In(string, "QueryText",
     Out(list (poly "A"), "QuotedProgram",
     Out(poly "A",        "QuotedQuery",
     Easy    ("quotes the program from FileName and the QueryText. "^
              "See elpi_quoted_syntax.elpi for the syntax tree"))))),
   (fun f s _ _ ~depth ->
      let ap = Parse.program [f] in
      let aq = Parse.goal s in
      let p = Elpi_API.Compile.(program dummy_header [ap]) in
      let q = Elpi_API.Compile.query p aq in
      let qp, qq = Compile.quote_syntax q in
      !: qp +! qq)),
  DocAbove);

  ]
;;

(** ELPI specific NON-LOGICAL built-in *********************************** *)

let ctype : string data = {
  to_term = (fun s -> mkApp Constants.ctypec (C.of_string s) []);
  of_term = (fun ~depth t ->
     match look ~depth t with
     | App(c,s,[]) when c == Constants.ctypec ->
         begin match look ~depth s with
         | CData c when C.is_string c -> Data (C.to_string c)
         | (UVar _ | AppUVar _) -> Flex t
         | Discard -> Discard
         | _ -> raise (TypeErr t) end
     | (UVar _ | AppUVar _) -> Flex t
     | Discard -> Discard
     | _ -> raise (TypeErr t));
   ty = "ctype"
}
   
let { CData.cin = safe_in; isc = is_safe ; cout = safe_out } as safe = CData.declare {
  CData.data_name = "safe";
  data_pp = (fun fmt (id,l,d) ->
     Format.fprintf fmt "[safe %d: %a]_%d" id
       (Pp.list (Pp.term 0) ";") !l d);
  data_eq = (fun (id1, _,_) (id2,_,_) -> id1 == id2);
  data_hash = (fun (id,_,_) -> id);
  data_hconsed = false;
}
let safe = data_of_cdata "@safe" safe

let fresh_copy t max_db depth =
  let rec aux d t =
    match look ~depth:(depth + d) t with
    | Lam t -> mkLam (aux (d+1) t)
    | Const c as x ->
        if c < max_db then kool x
        else if c - depth <= d then mkConst (max_db + c - depth)
        else raise No_clause (* restriction *)
    | App (c,x,xs) ->
        let x = aux d x in
        let xs = List.map (aux d) xs in
        if c < max_db then mkApp c x xs
        else if c - depth <= d then mkApp (max_db + c - depth) x xs
        else raise No_clause (* restriction *)
    | (Arg _ | AppArg _) ->
        type_error "stash takes only heap terms"
    | (UVar (r,_,_) | AppUVar(r,_,_)) ->
        type_error "stash takes only ground terms"
    | Builtin (c,xs) -> mkBuiltin c (List.map (aux d) xs)
    | CData _ as x -> kool x
    | Cons (hd,tl) -> mkCons (aux d hd) (aux d tl)
    | Nil as x -> kool x
    | Discard as x -> kool x
  in
    aux 0 t

let safeno = ref 0

let fresh_int = ref 0

let elpi_nonlogical_builtins = [ 

  LPDoc "== Elpi nonlogical builtins =====================================";

  LPCode "kind ctype type.";
  LPCode "type ctype string -> ctype.";
  LPCode "macro @safe :- ctype \"safe\".";

  MLCode(Pred("var",
    In(any,   "any term",
    Easy       "checks if the term is a variable"),
  (fun t1 ~depth ->
     match look ~depth t1 with
     | UVar _ | AppUVar _ -> ()
     | _ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("same_var",
    In(poly "A",   "first term",
    In(poly "A",   "second term",
    Easy       "checks if the two terms are the same variable")),
  (fun t1 t2 ~depth ->
     match look ~depth t1, look ~depth t2 with
     | (UVar(p1,_,_) | AppUVar(p1,_,_)),
       (UVar(p2,_,_) | AppUVar(p2,_,_)) when p1 == p2 -> ()
     | _,_ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("name",
    In(any, "T",
    Easy     "checks if T is a eigenvariable"),
  (fun x ~depth ->
    match look ~depth x with
    | Const n when n >= 0 -> ()
    | _ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("names",
    Out(list any, "list of eigenvariables in order of age (young first)",
    Easy           "generates the list of eigenvariable"),
  (fun _ ~depth -> !:(List.init depth mkConst))),
  DocNext);

  MLCode(Pred("occurs",
    In(poly "A", "a constant (global or eigenvariable)",
    In(poly "A", "a term", 
    Easy     "checks if the constant occurs in the term")),
  (fun t1 t2 ~depth ->
     let occurs_in t2 t =
       match look ~depth t with
       | Const n -> occurs n depth t2
       | _ -> error "The second argument of occurs must be a constant" in
     if occurs_in t2 t1 then () else raise No_clause)),
  DocNext);

  MLCode(Pred("closed_term",
    Out(any, "T",
    Easy      "unify T with a variable that has no eigenvariables in scope"),
  (fun _ ~depth -> !:(mkUVar (fresh_uvar_body ()) 0 0))),
  DocAbove);

  MLCode(Pred("is_cdata",
    In(any,     "T",
    Out(ctype,  "Ctype",
    Easy        "checks if T is primitive of type Ctype, eg (ctype \"int\")")),
  (fun t _ ~depth ->
     match look ~depth t with
     | CData n -> !:(CData.name n)
     | _ -> raise No_clause)),
  DocAbove);

  LPCode "primitive? X S :- is_cdata X (ctype S).";

  MLCode(Pred("new_int",
     Out(int, "N",
     Easy     "unifies N with a different int every time it is called"),
   (fun _ ~depth ->
      incr fresh_int;
      !: !fresh_int)),
  DocAbove);

   MLCode(Pred("new_safe",
     Out(safe, "Safe",
     Easy      "creates a safe: a store that persists across backtracking"),
   (fun _ ~depth -> incr safeno; !:(!safeno,ref [],depth))),
  DocAbove);

   MLCode(Pred("stash_in_safe",
     In(safe,  "Safe",
     In(any,   "Data",
     Easy      "stores Data in the Safe")),
   (fun (_,l,ld) t ~depth -> l := fresh_copy t ld depth :: !l)),
  DocAbove);

   MLCode(Pred("open_safe",
     In(safe, "Safe",
     Out(list any, "Data",
     Easy          "retrieves the Data stored in Safe")),
   (fun (_,l,ld) _ ~depth -> !:(List.rev !l))),
  DocAbove);

]
;;

let std_declarations =
  core_builtins @ io_builtins @ lp_builtins @ elpi_builtins @ elpi_nonlogical_builtins

let std_builtins =
  builtin_of_declaration std_declarations

