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

module Str = Re.Str

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

(*
let none = Constants.from_string "none"
let somec = Constants.from_stringc "some"

let option = fun a -> 
  let ty = TyApp("option",a.ty,[]) in {
  embed = (fun ~depth h s -> function
    | None -> s.state, none, []
    | Some x ->
        let s, x, e = a.embed ~depth h s x in
        s, mkApp somec x [], e);
  readback = (fun ~depth h s t ->
    match look ~depth t with
    | Const _ as x when kool x == none -> s.state, None
    | App(k,x,[]) when k == somec ->
      let s, x = a.readback  ~depth h s x in
      s, (Some x)
    | _ -> raise (TypeErr(ty,t)));
  ty;
}
*)

let bool_adt = {
  adt_ty = TyName "bool";
  adt_doc = "Boolean values: tt and ff since true and false are predicates";
  constructors = [
    K("tt",N,
      true,
      (fun ~ok ~ko -> function true ->  ok | _ -> ko ()));
    K("ff",N,
      false,
      (fun ~ok ~ko -> function false -> ok | _ -> ko ()));
  ]
}
let bool = adt bool_adt

let pair_adt a b = {
  adt_ty = TyApp ("pair",a.ty,[b.ty]);
  adt_doc = "Pair: the constructor is pr, since ',' is for conjunction";
  constructors = [
    K("pr",A(a,A(b,N)),
      (fun a b -> (a,b)),
      (fun ~ok ~ko:_ -> function (a,b) -> ok a b));
  ]
}
let pair a b = adt (pair_adt a b)

let option_adt a = {
  adt_ty = TyApp("option",a.ty,[]);
  adt_doc = "The option type (aka Maybe)";
  constructors = [
    K("none",N,
      None,
      (fun ~ok ~ko -> function None -> ok | _ -> ko ())); 
    K("some",A(a,N),
      (fun x -> Some x),
      (fun ~ok ~ko -> function Some x -> ok x | _ -> ko ())); 
  ]
}
let option a = adt (option_adt a)

(*
let tt = Constants.from_string "tt"
let ff = Constants.from_string "ff"

let bool = let ty  = TyName "bool" in {
  embed = (fun ~depth h { state } b ->
      if b then state, tt, [] else state, ff, []);
  readback = (fun ~depth h { state } t ->
    match look ~depth t with
    | Const _ as x when kool x == tt -> state, true
    | Const _ as x when kool x == ff -> state, false
    | _ -> raise (TypeErr(ty,t)));
  ty;
}

let prc = Constants.from_stringc "pr"

let pair a b =
  let ty = TyApp ("pair",a.ty,[b.ty]) in {
  embed = (fun ~depth h s (x,y) ->
    let state, x, g1 = a.embed ~depth h s x in
    let state, y, g2 = b.embed ~depth h { s with state } y in
    state, mkApp prc x [y], g1 @ g2);
  readback = (fun ~depth h s t ->
    match look ~depth t with
    | App(k,x,[y]) when k == prc ->
        let state, x = a.readback ~depth h s x in
        let state, y = b.readback ~depth h { s with state } y in
        state, (x,y)
    | _ -> raise (TypeErr(ty,t)));
  ty;
}
*)


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

  LPCode "pred (;) o:prop, o:prop.";
  LPCode "(A ; _) :- A.";
  LPCode "(_ ; B) :- B.";

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
  LPCode ("% [declare_constraint C Keys] declares C with Keys (a list of variables).\n"^
          "external pred declare_constraint i:any, i:list any.");
  LPCode "external pred print_constraints. % prints all constraints";

  MLCode(Pred("halt", VariadicIn(any, "halts the program and print the terms"),
  (fun args ~depth _ _ ->
     if args = [] then error "halt"
     else
       let b = Buffer.create 80 in
       let fmt = Format.formatter_of_buffer b in
       Format.fprintf fmt "%a%!" (Pp.list (Pp.term depth) " ") args;
       error (Buffer.contents b))),
  DocAbove);

  LPCode "type stop variadic any prop.";
  LPCode "stop :- halt.";
  LPCode "stop A :- halt A.";
  LPCode "stop A B :- halt A B.";
  LPCode "stop A B C :- halt A B C.";

  LPDoc " -- Evaluation --";

  MLCode(Pred("calc",
    In(poly "A",  "Expr",
    Out(poly "A", "Out",
    Easy          "unifies Out with the value of Expr. It can be used in tandem with spilling, eg [f {calc (N + 1)}]")),
  (fun t _ ~depth -> !:(eval depth t))),
  DocAbove);

  LPCode "pred (is) o:A, i:A.";
  LPCode "X is Y :- calc Y X.";

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

  LPCode "type (<), (>), (=<), (>=) A -> A -> prop.";
  LPCode "X  > Y  :- gt_ X Y.";
  LPCode "X  < Y  :- lt_ X Y.";
  LPCode "X  =< Y :- le_ X Y.";
  LPCode "X  >= Y :- ge_ X Y.";

  LPCode "type (i<), (i>), (i=<), (i>=) int -> int -> prop.";
  LPCode "X i< Y  :- lt_ X Y.";
  LPCode "X i> Y  :- gt_ X Y.";
  LPCode "X i=< Y :- le_ X Y.";
  LPCode "X i>= Y :- ge_ X Y.";

  LPCode "type (r<), (r>), (r=<), (r>=) float -> float -> prop.";
  LPCode "X r< Y  :- lt_ X Y.";
  LPCode "X r> Y  :- gt_ X Y.";
  LPCode "X r=< Y :- le_ X Y.";
  LPCode "X r>= Y :- ge_ X Y.";

  LPCode "type (s<), (s>), (s=<), (s>=) string -> string -> prop.";
  LPCode "X s< Y  :- lt_ X Y.";
  LPCode "X s> Y  :- gt_ X Y.";
  LPCode "X s=< Y :- le_ X Y.";
  LPCode "X s>= Y :- ge_ X Y.";

  LPDoc " -- Standard data types (supported in the FFI) --";

  LPCode "kind list type -> type.";
  LPCode "type (::) X -> list X -> list X.";
  LPCode "type ([]) list X.";

  MLADT bool_adt;

  MLADT (pair_adt (poly "A") (poly "B"));

  LPCode "pred fst  i:pair A B, o:A.";
  LPCode "fst (pr A _) A.";
  LPCode "pred snd  i:pair A B, o:B.";
  LPCode "snd (pr _ B) B.";

  MLADT (option_adt (poly "A"));

(*
  LPCode "kind pair type -> type -> type.";
  LPCode "type pr   A -> B -> pair A B.";
  LPCode "kind bool type.";
  LPCode "type tt bool.";
  LPCode "type ff bool.";
  LPCode "kind option type -> type.";
  LPCode "type some A -> option A.";
  LPCode "type none option A.";
*)

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
       let loc = Ast.Loc.initial "(string_of_term)" in
       let t = Parse.goal loc s in
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
  (fun (i,source_name) _ ~depth ->
     try
       let loc = Ast.Loc.initial source_name in
       let strm = Stream.of_channel i in
       let t = Parse.goal_from_stream loc strm in
       let t = Compile.term_at ~depth t in
       !:t
     with 
     | Sys_error msg -> error msg
     | Stream.Error _ -> raise No_clause
     | Elpi_ast.NotInProlog _ -> raise No_clause)),
  DocAbove);

  LPCode "pred printterm i:@out_stream, i:A.";
  LPCode "printterm S T :- term_to_string T T1, output S T1.";

  LPCode "pred read o:A.";
  LPCode "read S :- flush std_out, input_line std_in X, string_to_term X S.";

  ]
;;

(** ELPI specific built-in ************************************************ *)

let elpi_builtins = [

  LPDoc "== Elpi builtins =====================================";

  MLCode(Pred("dprint",
    VariadicIn(any, "prints raw terms (debugging)"),
  (fun args ~depth _ { state = cc } ->
     Format.fprintf Format.std_formatter "@[<hov 1>%a@]@\n%!"
       (Pp.list (Pp.Raw.term depth) " ") args ;
     cc, ())),
  DocAbove);

  MLCode(Pred("print",
    VariadicIn(any,"prints terms"),
  (fun args ~depth _ { state = cc } ->
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
      let loc = Ast.Loc.initial "(quote_syntax)" in
      let aq = Parse.goal loc s in
      let p =
        Elpi_API.Compile.(program ~flags:default_flags dummy_header [ap]) in
      let q = Elpi_API.Compile.query p aq in
      let qp, qq = Compile.quote_syntax q in
      !: qp +! qq)),
  DocAbove);

  ]
;;

(** ELPI specific NON-LOGICAL built-in *********************************** *)

let ctype : string data =
  let ty = TyName "ctype" in {
  embed = (fun ~depth:_ _ { state } x ->
    state, mkApp Constants.ctypec (C.of_string x) [], []);
  readback = (fun ~depth _ { state } t ->
     match look ~depth t with
     | App(c,s,[]) when c == Constants.ctypec ->
         begin match look ~depth s with
         | CData c when C.is_string c -> state, C.to_string c
         | _ -> raise (TypeErr(ty,t)) end
     | _ -> raise (TypeErr(ty,t)));
  ty;
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

(* factor the code of name and constant *)
let name_or_constant name condition = (); fun x out ~depth _ { state } ->
  let len = List.length out in
  if len != 0 && len != 2 then
    type_error (name^" only supports 1 or 3 arguments");
  state,
  match x with
  | NoData -> raise No_clause
  | Data x ->
      match look ~depth x with
      | Discard -> assert false
      | Const n when condition n ->
          if out = [] then !: x +? None
          else !: x +! [Some x; Some mkNil]
      | App(n,y,ys) when condition n ->
          if out = [] then !: x +? None
          else !: x +! [Some (mkConst n); Some (list_to_lp_list (y::ys))]
      | UVar _ | AppUVar _ ->
          (* We build the application *)
          begin match out with
          | [] -> raise No_clause
          | [Data hd; Data args] ->
              begin match look ~depth hd, lp_list_to_list ~depth args with
              | Const n, [] when condition n ->
                  !: (mkConst n) +! [Some hd; Some args]
              | Const n, x :: xs when condition n ->
                  !: (mkApp n x xs) +! [Some hd; Some args]
              | _ -> raise No_clause end
          | _ -> raise No_clause
          end
      | _ -> raise No_clause
;;

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
    InOut(any, "T",
    VariadicInOut(any,"checks if T is a eigenvariable. When used with tree arguments it relates an applied name with its head and argument list.")),
  (name_or_constant "name" (fun x -> x >= 0))),
  DocAbove);

  MLCode(Pred("constant",
    InOut(any, "T",
    VariadicInOut(any,"checks if T is a (global) constant.  When used with tree arguments it relates an applied constant with its head and argument list.")),
  (name_or_constant "constant" (fun x -> x < 0))),
  DocAbove);

  MLCode(Pred("names",
    Out(list any, "list of eigenvariables in order of age (young first)",
    Easy           "generates the list of eigenvariable"),
  (* XXX 4.06: (fun _ ~depth -> !:(List.init depth mkConst))), *)
  (fun _ ~depth ->
     let rec list_init i n f =
       if i >= n then [] else
       f i :: list_init (i+1) n f in
     !:(list_init 0 depth mkConst))),
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

  LPCode "pred primitive? i:A, i:string.";
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

  LPCode {|
% [if C T E] picks the first success of C then runs T (never E).
% if C has no success it runs E.
pred if i:prop, i:prop, i:prop.
if B T _ :- B, !, T.
if _ _ E :- E.  |}

]
;;

let elpi_stdlib = [ 

  LPCode {|

% == stdlib =======================================================

% Conventions:
% - all predicates declare a mode with some input arguments, unless...
% - predicates whose name ends with R are relations (work in any direction,
%   that is all arguments are in ouput mode)
% - predicates whose name ends with ! do contain a cut and generate only the
%   first result
% - all errors given by this library end up calling fatal-error[-w-data],
%   override it in order to handle them differently
% - all debug prints by this library end up calling debug-print, override it
%   in order to handle them differently

namespace std {

pred fatal-error i:string.
:name "default-fatal-error"
fatal-error Msg :- stop Msg.

pred fatal-error-w-data i:string, i:A.
:name "default-fatal-error-w-data"
fatal-error-w-data Msg Data :- stop Msg ":" Data.

pred debug-print i:string, i:A.
:name "default-debug-print"
debug-print Msg Data :- print Msg Data.

%  -- Errors, Debugging, Hacks --

pred ignore-failure! i:prop.
ignore-failure! P :- P, !.
ignore-failure! _.

% [assert! C M] takes the first success of C or fails with message M 
pred assert! i:prop, i:string.
assert! Cond Msg :- (Cond ; fatal-error-w-data Msg Cond), !.

% [spy P] traces the call to P, printing all success and the final failure
pred spy i:prop.
spy P :- counter "run" NR, if (not(NR = 0)) (debug-print "run=" NR) true,
         debug-print "----<<---- enter: " P,
         P,
         debug-print "---->>---- exit: " P.
spy P :- debug-print "---->>---- fail: " P, fail.

% [spy! P] traces the first call to P without leaving a choice point
pred spy! i:prop.
spy! P :- counter "run" NR, if (not(NR = 0)) (debug-print "run=" NR) true,
         debug-print "----<<---- enter: " P,
         P,
         debug-print "---->>---- exit: " P, !.
spy! P :- debug-print "---->>---- fail: " P, fail.

% to silence the type checker
pred unsafe-cast o:A, o:B.
unsafe-cast X X.

% -- List processing --

pred length i:list A, o:int.
length [_|L] N :- length L N1, N is N1 + 1.
length []    0.

pred rev i:list A, o:list A.
rev L RL  :- rev.aux L []  RL.
rev.aux [X|XS] ACC R :- rev.aux XS [X|ACC] R.
rev.aux [] L L.

pred last i:list A, o:A.
last [] _ :- fatal-error "last on empty list".
last [X] X :- !.
last [_|XS] R :- last XS R.

pred append i:list A, i:list A, o:list A.
append [X|XS] L [X|L1] :- append XS L L1 .
append [] L L .

pred appendR o:list A, o:list A, o:list A.
appendR [X|XS] L [X|L1] :- appendR XS L L1 .
appendR [] L L .

pred take i:int, i:list A, o:list A.
take 0 _ [] :- !.
take N [X|XS] [X|L] :- !, N1 is N - 1, take N1 XS L.
take _ _ _ :- fatal-error "take run out of list items".

pred drop i:int, i:list A, o:list A.
drop 0 L L :- !.
drop N [_|XS] L :- !, N1 is N - 1, drop N1 XS L.
drop _ _ _ :- fatal-error "drop run out of list items".

pred drop-last i:int, i:list A, o:list A.
drop-last N L R :-
  length L M, I is M - N, take I L R.

pred split-at i:int, i:list A, o:list A, o:list A.
split-at 0 L [] L :- !.
split-at N [X|XS] [X|LN] LM :- !, N1 is N - 1, split-at N1 XS LN LM.
split-at _ _ _ _ :- fatal-error "split-at run out of list items".

pred fold i:list B, i:A, i:(B -> A -> A -> prop), o:A.
fold [] A _ A.
fold [X|XS] A F R :- F X A A1, fold XS A1 F R.

pred fold2 i:list C, i:list B, i:A, i:(C -> B -> A -> A -> prop), o:A.
fold2 [] [_|_] _ _ _ :- fatal-error "fold2 on lists of different length".
fold2 [_|_] [] _ _ _ :- fatal-error "fold2 on lists of different length".
fold2 [] [] A _ A.
fold2 [X|XS] [Y|YS] A F R :- F X Y A A1, fold2 XS YS A1 F R.

pred map i:list A, i:(A -> B -> prop), o:list B.
map [] _ [].
map [X|XS] F [Y|YS] :- F X Y, map XS F YS.

pred map-i i:list A, i:(int -> A -> B -> prop), o:list B.
map-i L F R :- map-i.aux L 0 F R.
map-i.aux [] _ _ [].
map-i.aux [X|XS] N F [Y|YS] :- F N X Y, M is N + 1, map-i.aux XS M F YS.

pred map2 i:list A, i:list B, i:(A -> B -> C -> prop), o:list C.
map2 [] [_|_] _ _ :- fatal-error "map2 on lists of different length".
map2 [_|_] [] _ _ :- fatal-error "map2 on lists of different length".
map2 [] [] _ [].
map2 [X|XS] [Y|YS] F [Z|ZS] :- F X Y Z, map2 XS YS F ZS.

pred map2_filter i:list A, i:list B, i:(A -> B -> C -> prop), o:list C.
map2_filter [] [_|_] _ _ :- fatal-error "map2_filter on lists of different length".
map2_filter [_|_] [] _ _ :- fatal-error "map2_filter on lists of different length".
map2_filter [] [] _ [].
map2_filter [X|XS] [Y|YS] F [Z|ZS] :- F X Y Z, !, map2_filter XS YS F ZS.
map2_filter [_|XS] [_|YS] F ZS :- map2_filter XS YS F ZS.

% [nth N L X] picks in X the N-th element of L (L must be of length > N)
pred nth i:int, i:list A, o:A.
nth 0 [X|_] X :- !.
nth N [_|XS] R :- !, N1 is N - 1, nth N1 XS R.
nth _ _ _ :- fatal-error "nth run out of list items".

% [lookup L K V] sees L as a map from K to V
pred lookup i:list (pair A B), i:A, o:B.
lookup [pr X Y|_] X Y.
lookup [_|LS]       X Y :- lookup LS X Y.

% [lookup! L K V] sees L as a map from K to V, stops at the first binding
pred lookup! i:list (pair A B), i:A, o:B.
lookup! [pr X Y|_] X Y :- !.
lookup! [_|LS]       X Y :- lookup! LS X Y.

% [mem L X] succeeds once if X occurs inside L 
pred mem i:list A, i:A.
mem [X|_] X :- !.
mem [_|L] X :- mem L X.

pred exists i:list A, i:(A -> prop).
exists [X|_] P :- P X.
exists [_|L] P :- exists L P.

pred exists2 i:list A, i:list B, i:(A -> B -> prop).
exists2 [] [_|_] _ :- fatal-error "exists2 on lists of different length".
exists2 [_|_] [] _ :- fatal-error "exists2 on lists of different length".
exists2 [X|_] [Y|_] P :- P X Y.
exists2 [_|L] [_|M] P :- exists2 L M P.

pred forall i:list A, i:(A -> prop).
forall [] _.
forall [X|L] P :- P X, forall L P.

pred forall2 i:list A, i:list B, i:(A -> B -> prop).
forall2 [] [_|_] _ :- fatal-error "forall2 on lists of different length".
forall2 [_|_] [] _ :- fatal-error "forall2 on lists of different length".
forall2 [X|XS] [Y|YS] P :- P X Y, forall2 XS YS P.
forall2 [] [] _.

pred filter i:list A, i:(A -> prop), o:list A.
filter []    _ [].
filter [X|L] P R :- if (P X) (R = X :: L1) (R = L1), filter L P L1.

pred zip i:list A, i:list B, o:list (pair A B).
zip [_|_] [] _ :- fatal-error "zip on lists of different length".
zip [] [_|_] _ :- fatal-error "zip on lists of different length".
zip [X|LX] [Y|LY] [pr X Y|LR] :- zip LX LY LR.
zip [] [] [].

pred unzip i:list (pair A B), o:list A, o:list B.
unzip [] [] [].
unzip [pr X Y|L] [X|LX] [Y|LY] :- unzip L LX LY.

pred flatten i:list (list A), o:list A.
flatten [X|LS] R :- flatten LS LS', append X LS' R.
flatten []     [].

pred null i:list A.
null [].

pred iota i:int, o:list int.
iota N L :- iota.aux 0 N L.
iota.aux X X [] :- !.
iota.aux N X [N|R] :- M is N + 1, iota.aux M X R.

%  -- Misc --

pred flip i:(A -> B -> prop), i:B, i:A.
flip P X Y :- P Y X.

pred time i:prop, o:float.
time P T :- gettimeofday Before, P, gettimeofday After, T is After - Before.

pred do! i:list prop.
do! [].
do! [P|PS] :- P, !, do! PS.

pred spy-do! i:list prop.
spy-do! L :- map L (x\y\y = spy x) L1, do! L1.

pred any->string i:A, o:string.
any->string X Y :- term_to_string X Y.

} % namespace std |}
]
;;


let std_declarations =
  core_builtins @ io_builtins @ lp_builtins @ elpi_builtins @ elpi_nonlogical_builtins @ elpi_stdlib

let std_builtins =
  builtin_of_declaration ~file_name:"builtin.elpi" std_declarations

