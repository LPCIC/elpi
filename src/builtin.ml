(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util

open API
open RawData
open Utils
open BuiltInPredicate
open Notation

module Str = Re.Str

let in_stream_decl = {
  OpaqueData.name = "in_stream";
  pp = (fun fmt (_,d) -> Format.fprintf fmt "<in_stream:%s>" d);
  compare = (fun (_,s1) (_,s2) -> String.compare s1 s2);
  hash = (fun (x,_) -> Hashtbl.hash x);
  hconsed = false;
  constants = ["std_in",(stdin,"stdin")];
  doc = "";
}
let in_stream = OpaqueData.declare in_stream_decl

let out_stream_decl = {
  OpaqueData.name = "out_stream";
  pp = (fun fmt (_,d) -> Format.fprintf fmt "<out_stream:%s>" d);
  compare = (fun (_,s1) (_,s2) -> String.compare s1 s2);
  hash = (fun (x,_) -> Hashtbl.hash x);
  hconsed = false;
  doc = "";
  constants = ["std_out",(stdout,"stdout");"std_err",(stderr,"stderr")];
}
let out_stream = OpaqueData.declare out_stream_decl

type process = {
  stdin : out_channel * string;
  stdout : in_channel * string;
  stderr : in_channel * string;
}
let process = AlgebraicData.declare {
  AlgebraicData.ty = TyName "unix.process";
  doc = "gathers the standard file descriptors or a process";
  pp = (fun fmt { stdin; stdout; stderr }  ->
    Format.fprintf fmt "{ stdin = %a; stdout = %a; stderr = %a }"
      out_stream_decl.OpaqueData.pp stdin
      in_stream_decl.OpaqueData.pp stdout
      in_stream_decl.OpaqueData.pp stderr
    );
  constructors = [
    K("unix.process","",A(out_stream,A(in_stream,A(in_stream,N))),
      B (fun stdin stdout stderr -> { stdin; stdout; stderr }),
      M (fun ~ok ~ko:_ { stdin; stdout; stderr } -> ok stdin stdout stderr ))
  ]
}|> ContextualConversion.(!<)

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
   let rec aux d t = match look ~depth:d t with
     | Const c                          -> c = x
     | Lam t                            -> aux (d+1) t
     | App (c, v, vs)                   -> c = x || aux d v || auxs d vs
     | UnifVar (_, l)                   -> auxs d l
     | Builtin (_, vs)                  -> auxs d vs
     | Cons (v1, v2)                    -> aux d v1 || aux d v2
     | Nil
     | CData _                          -> false
   and auxs d = function
     | []      -> false
     | t :: ts -> aux d t || auxs d ts
   in
   x < d && aux d t

type polyop = {
  p : 'a. 'a -> 'a -> bool;
  psym : string;
  pname : string;
}

let bool = AlgebraicData.declare {
  AlgebraicData.ty = TyName "bool";
  doc = "Boolean values: tt and ff since true and false are predicates";
  pp = (fun fmt b -> Format.fprintf fmt "%b" b);
  constructors = [
    K("tt","",N,
      B true,
      M (fun ~ok ~ko -> function true ->  ok | _ -> ko ()));
    K("ff","",N,
      B false,
      M (fun ~ok ~ko -> function false -> ok | _ -> ko ()));
  ]
}|> ContextualConversion.(!<)

let pair a b = let open AlgebraicData in declare {
  ty = TyApp ("pair",a.Conversion.ty,[b.Conversion.ty]);
  doc = "Pair: the constructor is pr, since ',' is for conjunction";
  pp = (fun fmt o -> Format.fprintf fmt "%a" (Util.pp_pair a.Conversion.pp b.Conversion.pp) o);
  constructors = [
    K("pr","",A(a,A(b,N)),
      B (fun a b -> (a,b)),
      M (fun ~ok ~ko:_ -> function (a,b) -> ok a b));
  ]
} |> ContextualConversion.(!<)

let option a = let open AlgebraicData in declare {
  ty = TyApp("option",a.Conversion.ty,[]);
  doc = "The option type (aka Maybe)";
  pp = (fun fmt o -> Format.fprintf fmt "%a" (Util.pp_option a.Conversion.pp) o);
  constructors = [
    K("none","",N,
      B None,
      M (fun ~ok ~ko -> function None -> ok | _ -> ko ())); 
    K("some","",A(a,N),
      B (fun x -> Some x),
      M (fun ~ok ~ko -> function Some x -> ok x | _ -> ko ())); 
  ]
} |> ContextualConversion.(!<)

type diagnostic = OK | ERROR of string ioarg
let mkOK = OK
let mkERROR s = ERROR (mkData s)

let diagnostic = let open API.AlgebraicData in declare {
  ty = TyName "diagnostic";
  doc = "Used in builtin variants that return Coq's error rather than failing";
  pp = (fun fmt -> function
    | OK -> Format.fprintf fmt "OK"
    | ERROR NoData -> Format.fprintf fmt "ERROR _"
    | ERROR (Data s) -> Format.fprintf fmt "ERROR %S" s);
  constructors = [
    K("ok","Success",N,
      B mkOK,
      M (fun ~ok ~ko -> function OK -> ok | _ -> ko ()));
    K("error","Failure",A(BuiltInPredicate.ioarg BuiltInData.string,N),
      B (fun s -> ERROR s),
      M (fun ~ok ~ko -> function ERROR s -> ok s | _ -> ko ()));
    K("uvar","",A(FlexibleData.uvar,N),
      B (fun _ -> assert false),
      M (fun ~ok ~ko _ -> ko ()))
  ]
} |> ContextualConversion.(!<)

let unix_error_to_diagnostic e f a =
  mkERROR (Printf.sprintf "%s: %s" (if a <> "" then f ^ " " ^ a else f) (Unix.error_message e))

let cmp = let open AlgebraicData in declare {
  ty = TyName "cmp";
  doc = "Result of a comparison";
  pp = (fun fmt i -> Format.fprintf fmt "%d" i);
  constructors = [
    K("eq", "", N, B 0,   M(fun ~ok ~ko i -> if i == 0 then ok else ko ()));
    K("lt", "", N, B ~-1, M(fun ~ok ~ko i -> if i < 0  then ok else ko ()));
    K("gt", "", N, B 1,   M(fun ~ok ~ko i -> if i > 0  then ok else ko ()))
  ]
} |> ContextualConversion.(!<)


type 'a unspec = Given of 'a | Unspec

let unspecC data = let open API.ContextualConversion in let open API.RawData in {
  ty = data.ty;
  pp_doc = data.pp_doc;
  pp = (fun fmt -> function
    | Unspec -> Format.fprintf fmt "Unspec"
    | Given x -> Format.fprintf fmt "Given %a" data.pp x);
  embed = (fun ~depth hyps constraints state -> function
     | Given x -> data.embed ~depth hyps constraints state x
     | Unspec -> state, mkDiscard, []);
  readback = (fun ~depth hyps constraints state x ->
      match look ~depth x with
      | UnifVar _ -> state, Unspec, []
      | t ->
        let state, x, gls = data.readback ~depth hyps constraints state (kool t) in
        state, Given x, gls)
}
let unspec d = API.ContextualConversion.(!<(unspecC (!> d)))

(** Core built-in ********************************************************* *)

let core_builtins = let open BuiltIn in let open ContextualConversion in [

  LPDoc "File generated by elpi -document-builtins, do not edit";

  LPDoc " == Core builtins =====================================";

  LPDoc " -- Logic --";

  LPCode "func true.";
  LPCode "true.";

  LPCode "func fail.";
  LPCode "func false.";

  LPCode "external func (=) -> A, A. % unification";
  LPCode "external func pattern_match A -> A. % matching";

  (* LPCode "external func (pi) i:(func i:A)."; *)
  LPCode "external func (pi) (func A).";
  LPCode "external func (sigma) (func A).";
  
  MLData BuiltInData.int;
  MLData BuiltInData.string;
  MLData BuiltInData.float;

  LPCode "pred (;) i:prop, i:prop.";
  LPCode "(A ; _) :- A.";
  LPCode "(_ ; B) :- B.";

  LPCode "external symbol (:-)  : fprop -> fprop -> fprop.";
  LPCode "external symbol (:-)  : fprop -> list prop -> fprop.";
  LPCode "external symbol (,)   : variadic fprop fprop.";
  LPCode "external symbol uvar  : A = \"core\".";
  LPCode "external symbol (as)  : A -> A -> A = \"core\".";
  LPCode "external symbol (=>)  : prop -> fprop -> fprop.";
  LPCode "external symbol (=>)  : list prop -> fprop -> fprop."; (* HACS in TC to handle this*)
  LPCode "external symbol (==>) : prop -> fprop -> fprop.";
  LPCode "external symbol (==>) : list prop -> fprop -> fprop.";

  LPDoc " -- Control --";

  (* This is not implemented here, since the API had no access to the
   * choice points *)
  LPCode "external func !. % The cut operator";

  LPCode "func not prop.";
  LPCode "not X :- X, !, fail.";
  LPCode "not _.";

  (* These are not implemented here since the API has no access to the
   * store of syntactic constraints *)
  LPCode ("% [declare_constraint C Key1 Key2...] declares C blocked\n"^
          "% on Key1 Key2 ... (variables, or lists thereof).\n"^
          "external type declare_constraint any -> any -> variadic any fprop.");
  MLCode(Pred("print_constraints",
    Full(raw_ctx,"prints all constraints"),
    (fun ~depth _ constraints state ->
      Util.printf "@[<hov 0>%a@]@\n%!" RawPp.constraints constraints;
      state, (), []
      )),DocAbove);
  MLCode(Pred("halt", VariadicIn(unit_ctx, !> BuiltInData.any, "halts the program and print the terms"),
  (fun args ~depth _ _ ->
     if args = [] then error "halt"
     else
       let b = Buffer.create 80 in
       let fmt = Format.formatter_of_buffer b in
       Format.fprintf fmt "%a%!" (RawPp.list (RawPp.term depth) " ") args;
       error (Buffer.contents b))),
  DocAbove);

  LPCode "func stop.";
  LPCode "stop :- halt.";

  ] @ Calc.calc @ [

  LPDoc " -- Arithmetic tests --";

  ] @ List.map (fun { p; psym; pname } ->

  MLCode(Pred(pname,
    In(BuiltInData.poly "A","X",
    In(BuiltInData.poly "A","Y",
    Read(unit_ctx,("checks if X " ^ psym ^ " Y. Works for string, int and float")))),
  (fun t1 t2 ~depth _ _ state ->
     let open RawOpaqueData in
     let t1 = look ~depth (Calc.eval ~depth state t1) in
     let t2 = look ~depth (Calc.eval ~depth state t2) in
     match t1, t2 with
     | CData x, CData y ->
          if ty2 int x y then let out = to_int in
            if p (out x) (out y) then () else raise No_clause
          else if ty2 float x y then let out = to_float in
            if p (out x) (out y) then () else raise No_clause
          else if ty2 string x y then let out = to_string in
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

  @ 
  let build_symb (spref, ty) = 
    let op_l = ["gt_";"lt_"; "le_"; "ge_"] in
    let sym_l = List.map (fun x -> spref ^ x) [">";"<"; "=<"; ">="] in
    let buildLPCode s op = LPCode (Printf.sprintf "pred (%s) i:%s, i:%s.\nX %s Y :- %s X Y." s ty ty s op) in
    List.map2 buildLPCode sym_l op_l in
  let symbs = ["", "A"; "i", "int"; "r", "float"; "s", "string"] in
  List.flatten (List.map build_symb symbs) @
  [

  LPDoc " -- Standard data types (supported in the FFI) --";

  LPCode "kind list type -> type.";
  LPCode "type (::) X -> list X -> list X.";
  LPCode "type ([]) list X.";

  MLData bool;

  MLData (pair (BuiltInData.poly "A") (BuiltInData.poly "B"));

  LPCode "func fst  pair A B -> A.";
  LPCode "fst (pr A _) A.";
  LPCode "func snd  pair A B -> B.";
  LPCode "snd (pr _ B) B.";

  LPCode {|
kind triple type -> type -> type -> type.
type triple A -> B -> C -> triple A B C.

func triple_1 triple A B C -> A.
triple_1 (triple A _ _) A.

func triple_2 triple A B C -> B.
triple_2 (triple _ B _) B.

func triple_3 triple A B C -> C.
triple_3 (triple _ _ C) C.
 
|};

  MLData (option (BuiltInData.poly "A"));

  MLData cmp;

  MLData diagnostic;

  ]
;;

(** Standard lambda Prolog I/O built-in *********************************** *)

let io_builtins = let open BuiltIn in let open BuiltInData in [

  LPDoc " == I/O builtins =====================================";

  LPDoc " -- I/O --";

  MLData (in_stream);

  MLData (out_stream);
     
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
     try !:(open_out_gen flags 0o664 s,s)
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
       Stdlib.seek_in i pos;
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
    Out(option string, "Value",
    Easy      ("Like Sys.getenv"))),
  (fun s _ ~depth ->
     try !:(Some (Sys.getenv s))
     with Not_found -> !: None)),
  DocAbove);

  MLCode(Pred("system",
    In(string, "Command",
    Out(int,   "RetVal",
    Easy       "executes Command and sets RetVal to the exit code")),
  (fun s _ ~depth -> !:(Sys.command s))),
  DocAbove);

  LPDoc " -- Unix --";

  MLData process;

  MLCode(Pred("unix.process.open",
    In(unspec string, "Executable",
    In(unspec @@ list string, "Arguments",
    In(unspec (list string), "Environment",
    Out(process, "P",
    Out(diagnostic, "Diagnostic",
    Easy {|OCaml's Unix.open_process_args_full.
Note that the first argument is the executable name (as in argv[0]).
If Executable is omitted it defaults to the first element of Arguments.
Environment can be left unspecified, defaults to the current process environment.
This API only works reliably since OCaml 4.12.|}))))),
    (fun cmd args env _ _ ~depth ->
      try
        let env =
          match env with
          | Given l -> Array.of_list l
          | Unspec -> Unix.environment () in
        let cmd, args =
          match cmd, args with
          | Given x, Unspec -> x, [x]
          | Given x, Given [] -> x, [x]
          | Given x, Given args -> x, args
          | Unspec, Given (x::_ as args) -> x, args
          | _ -> type_error "unix.process.open: no executable and no argumnts" in
        let (out,in_,err) as full = Unix.open_process_args_full cmd (Array.of_list args) env in
        let pid = Unix.process_full_pid full in
        let name_fd s = Printf.sprintf "%s of process %d (%s)" s pid cmd in
        !: { stdin = (in_,name_fd "stdin"); stdout = (out,name_fd "stdout"); stderr = (err,name_fd "stderr") } +! mkOK
      with Unix.Unix_error(e,f,a) -> ?: None +! (unix_error_to_diagnostic e f a))),
  DocAbove);

  MLCode(Pred("unix.process.close",
    In(process, "P",
    Out(diagnostic, "Diagnostic",
    Easy            "OCaml's Unix.close_process_full")),
    (fun { stdin = (out,_); stdout = (in_,_); stderr = (err,_) } _ ~depth ->
      match Unix.close_process_full (in_,out,err) with
      | Unix.WEXITED 0 -> !: mkOK
      | Unix.WEXITED i -> !: (mkERROR (Printf.sprintf "exited: %d" i))
      | Unix.WSIGNALED i -> !: (mkERROR (Printf.sprintf "signaled: %d" i))
      | Unix.WSTOPPED i -> !: (mkERROR (Printf.sprintf "stopped: %d" i))
      | exception Unix.Unix_error(e,f,a) -> !: (unix_error_to_diagnostic e f a))),
  DocAbove);

  LPDoc " -- Debugging --";

  MLCode(Pred("term_to_string",
    InOut(ioarg_any,     "T",
    Out(string, "S",
    Easy        "prints T to S")),
  (fun t _ ~depth ->
     match t with
     | NoData -> ?: None +! "_"
     | Data t ->
     let b = Buffer.create 1024 in
     let fmt = Format.formatter_of_buffer b in
     Format.fprintf fmt "%a" (RawPp.term depth) t ;
     Format.pp_print_flush fmt ();
     ?: None +! (Buffer.contents b))),
  DocAbove);

  ]
;;

(** Standard lambda Prolog built-in ************************************** *)

let lp_builtins = let open BuiltIn in let open BuiltInData in [

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
       Stdlib.seek_in i pos;
       !:(String.make 1 c)
     with
     | End_of_file -> !:""
     | Sys_error msg -> error msg)),
  DocAbove);

  LPCode "pred printterm i:out_stream, i:A.";
  LPCode "printterm S T :- term_to_string T T1, output S T1.";

  ]
;;

(** ELPI specific built-in ************************************************ *)

let elpi_builtins = let open BuiltIn in let open BuiltInData in let open ContextualConversion in [

  LPDoc "== Elpi builtins =====================================";

  MLCode(Pred("dprint",
    VariadicIn(unit_ctx, !> any, "prints raw terms (debugging)"),
  (fun args ~depth _ _ state ->
    Util.printf "@[<hov 1>%a@]@\n%!"
       (RawPp.list (RawPp.Debug.term depth) " ") args ;
     state, ())),
  DocAbove);

  MLCode(Pred("print",
    VariadicIn(unit_ctx, !> any,"prints terms"),
  (fun args ~depth _ _ state ->
     Util.printf "@[<hov 1>%a@]@\n%!"
       (RawPp.list (RawPp.term depth) " ") args ;
     state, ())),
  DocAbove);

  LPCode {|% Deprecated, use trace.counter
func counter string -> int.
counter C N :- trace.counter C N.|};

  MLData loc;

  MLCode(Pred("loc.fields",
    In(loc, "Loc",
    Out(string, "File",
    Out(int, "StartChar",
    Out(int, "StopChar",
    Out(int, "Line",
    Out(int, "LineStartsAtChar",
    Easy "Decomposes a loc into its fields")))))),
  (fun { source_name; source_start; source_stop; line; line_starts_at; } _ _ _ _ _ ~depth:_ ->
     !: source_name +! source_start +! source_stop +! line +! line_starts_at )),
  DocAbove);

  LPDoc "== Regular Expressions =====================================";

  MLCode(Pred("rex.match",
    In(string, "Rex",
    In(string, "Subject",
    Easy      ("checks if Subject matches Rex. "^
               "Matching is based on OCaml's Str library"))),
  (fun rex subj ~depth ->
     let rex = Str.regexp rex in
     if Str.string_match rex subj 0 then () else raise No_clause)),
  DocAbove);

  MLCode(Pred("rex.replace",
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

  MLCode(Pred("rex.split",
    In(string,  "Rex",
    In(string,  "Subject",
    Out(list string, "Out",
    Easy   ("Out is obtained by splitting Subject at all occurrences of Rex. "^
            "See also OCaml's Str.split")))),
  (fun rex subj _ ~depth ->
     let rex = Str.regexp rex in
     !:(Str.split rex subj))),
  DocAbove);

    LPCode {|% Deprecated, use rex.match
func rex_match string, string.
rex_match Rx S :- rex.match Rx S.|};

  LPCode {|% Deprecated, use rex.replace
func rex_replace string, string, string -> string.
rex_replace Rx R S O :- rex.replace Rx R S O.|};

  LPCode {|% Deprecated, use rex.split
func rex_split string, string -> list string.
rex_split Rx S L :- rex.split Rx S L.|};


]
;;

(** ELPI specific NON-LOGICAL built-in *********************************** *)
   
let safe = OpaqueData.declare {
  OpaqueData.name = "safe";
  pp = (fun fmt (id,l) ->
     Format.fprintf fmt "[safe %d: %a]" id
       (RawPp.list (fun fmt (t,d) -> RawPp.term d fmt t) ";") !l);
  compare = (fun (id1, _) (id2,_) -> Util.Int.compare id1 id2);
  hash = (fun (id,_) -> id);
  hconsed = false;
  doc = "Holds data across bracktracking; can only contain closed terms";
  constants = [];
}

let safeno = ref 0

let fresh_int = ref 0

(* factor the code of name and constant *)
let name_or_constant name condition = (); fun x out ~depth _ _ state ->
  let len = List.length out in
  if len != 0 && len != 2 then
    type_error (name^" only supports 1 or 3 arguments");
  state,
  match x with
  | NoData -> raise No_clause
  | Data x ->
      match look ~depth x with
      | Const n when condition n ->
          if out = [] then !: x +? None
          else !: x +! [Some x; Some mkNil]
      | App(n,y,ys) when condition n ->
          if out = [] then !: x +? None
          else !: x +! [Some (mkConst n); Some (list_to_lp_list (y::ys))]
      | UnifVar _ ->
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

let rec same_term ~depth t1 t2 =
  match look ~depth t1, look ~depth t2 with
  | UnifVar(b1,xs), UnifVar(b2,ys) -> FlexibleData.Elpi.equal b1 b2 && same_term_list ~depth xs ys
  | App(c1,x,xs), App(c2,y,ys) -> c1 == c2 && same_term ~depth x y && same_term_list ~depth xs ys
  | Const c1, Const c2 -> c1 == c2
  | Cons(x,xs), Cons(y,ys) -> same_term ~depth x y && same_term ~depth xs ys
  | Nil, Nil -> true
  | Lam x, Lam y -> same_term ~depth:(depth+1) x y
  | Builtin(c1,xs),Builtin(c2,ys) -> c1 == c2 && same_term_list ~depth xs ys
  | CData d1, CData d2 -> RawOpaqueData.equal d1 d2
  | _ -> false
and same_term_list ~depth xs ys =
  match xs, ys with
  | [], [] -> true
  | x::xs, y::ys -> same_term ~depth x y && same_term_list ~depth xs ys
  | _ -> false

let elpi_nonlogical_builtins = let open BuiltIn in let open BuiltInData in let open ContextualConversion in [ 

  LPDoc "== Elpi nonlogical builtins =====================================";

  MLCode(Pred("var",
    InOut(ioarg_any, "V",
    VariadicInOut(unit_ctx, !> (ioarg_any),"checks if the term V is a variable. When used with tree arguments it relates an applied variable with its head and argument list.")),
  (fun x out ~depth _ _ state ->
    let len = List.length out in
    if len != 0 && len != 2 then
      type_error ("var only supports 1 or 3 arguments");
    let is_var x =
      match look ~depth x with
      | UnifVar(v,a) -> v,a
      | _ -> raise No_clause in
    state,
    match x, out with
    | Data x, [] -> let _ = is_var x in ?: None +? None
    | Data x, [NoData; NoData] -> let _ = is_var x in ?: None +? None
    | Data x, [NoData; Data args] -> let _, a = is_var x in ?: None +! [None; Some (list_to_lp_list a)]
    | Data x, [Data var; NoData] -> let v, _ = is_var x in ?: None +! [Some (mkUnifVar v ~args:[] state); None]
    | Data x, [Data y; Data args] ->
        let vx, ax = is_var x in
        let vy, ay = is_var y in
        begin match look ~depth args with
        | UnifVar _ ->
          ?: None +! [Some (mkUnifVar vx ~args:[] state); Some (list_to_lp_list ax)]
        | _ ->
          !: (mkUnifVar vy ~args:(ay @ lp_list_to_list ~depth args) state)
          +! [Some (mkUnifVar vx ~args:[] state); Some (list_to_lp_list ax)]
        end
    | _ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("prune",
  Out(any, "V",
  In(list any, "L",
  Full (unit_ctx, "V is pruned to L (V is unified with a variable that only sees the list of names L)"))),
    (fun _ l ~depth _ _ state ->
      if not (List.for_all (fun t -> match look ~depth t with
        | Const n -> n >= 0
        | _ -> false) l) then
      type_error ("prune only accepts a list of names");
      let state, u = FlexibleData.Elpi.make state in
      state, !: (mkUnifVar u ~args:l state), [])),
  DocAbove);

  MLCode(Pred("distinct_names",
  In(list any, "L",
  Easy "checks if L is a list of distinct names. If L is the scope of a unification variable (its arguments, as per var predicate) then distinct_names L checks that such variable is in the Miller pattern fragment (L_\\lambda)"),
    (fun l ~depth ->
      let _ = List.fold_left (fun seen t ->
        match look ~depth t with
        | Const n when n >= 0 ->
            if not (Util.IntSet.mem n seen) then Util.IntSet.add n seen
            else raise No_clause
        | _ -> raise No_clause) Util.IntSet.empty l in
      ())),
  DocAbove);

  MLCode(Pred("same_var",
    In(poly "A",   "V1",
    In(poly "A",   "V2",
    Easy       "checks if the two terms V1 and V2 are the same variable, ignoring the arguments of the variables")),
  (fun t1 t2 ~depth ->
     match look ~depth t1, look ~depth t2 with
     | UnifVar(p1,_), UnifVar (p2,_) when FlexibleData.Elpi.equal p1 p2 -> ()
     | _,_ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("same_term",
    In(poly "A",   "T1",
    In(poly "A",   "T2",
    Easy {|checks if the two terms T1 and T2 are syntactically equal (no unification). It behaves differently than same_var since it recursively compares the arguments of the variables|})),
  (fun t1 t2 ~depth ->
     if same_term ~depth t1 t2 then () else raise No_clause)),
  DocAbove);

  LPCode {|
% Infix notation for same_term
func (==) A, A.
X == Y :- same_term X Y.
|};

  MLCode(Pred("cmp_term",
    In(any, "A",
    In(any, "B",
    Out(cmp,"Cmp",
    Easy "Compares A and B. Only works if A and B are ground."))),
  (fun t1 t2 _ ~depth -> !: (Utils.cmp_term ~depth t1 t2))),
  DocAbove);

  MLCode(Pred("name",
    InOut(ioarg_any, "T",
    VariadicInOut(unit_ctx, !> (ioarg any),"checks if T is a eigenvariable. When used with tree arguments it relates an applied name with its head and argument list.")),
  (name_or_constant "name" (fun x -> x >= 0))),
  DocAbove);

  MLCode(Pred("constant",
    InOut(ioarg_any, "T",
    VariadicInOut(unit_ctx, !> (ioarg any),"checks if T is a (global) constant.  When used with tree arguments it relates an applied constant with its head and argument list.")),
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
    In(any, "an atom, that is a global constant or a bound name (aka eigenvariable)",
    In(any, "a term",
    Easy     "checks if the atom occurs in the term")),
  (fun t1 t2 ~depth ->
     let occurs_in t2 t =
       match look ~depth t with
       | Const n -> occurs n depth t2
       | _ -> error "The second argument of occurs must be an atom" in
     if occurs_in t2 t1 then () else raise No_clause)),
  DocNext);

  MLCode(Pred("closed_term",
    Out(any, "T",
    Full (unit_ctx, "unify T with a variable that has no eigenvariables in scope")),
  (fun _ ~depth _ _ state ->
      let state, k = FlexibleData.Elpi.make state in
      state, !:(mkUnifVar k ~args:[] state), [])),
  DocAbove);

  MLCode(Pred("ground_term",
    In(any, "T",
    Easy ("Checks if T contains unification variables")),
  (fun t ~depth -> Utils.check_ground ~depth t)),
  DocAbove);

  MLCode(Pred("is_cdata",
    In(any,     "T",
    Out(string,  "Ctype",
    Easy        "checks if T is primitive of type Ctype, eg \"int\"")),
  (fun t _ ~depth ->
     match look ~depth t with
     | CData n -> !:(RawOpaqueData.name n)
     | _ -> raise No_clause)),
  DocAbove);

  LPCode "func primitive? any, string.";
  LPCode "primitive? X S :- is_cdata X S.";

  MLCode(Pred("new_int",
     Out(int, "N",
     Easy     "unifies N with a different int every time it is called. Values of N are guaranteed to be incresing."),
   (fun _ ~depth ->
      incr fresh_int;
      if !fresh_int < 0 then anomaly "new_int: reached max_int";
      !: !fresh_int)),
  DocAbove);

  LPDoc  {|[findall_solution P L] finds all the solved instances of P and puts them in L in the order in which they are found. Instances can contain eigenvariables and unification variables. P may or may not be instantiated. Instances should be found in L.|};
  LPCode "external func findall_solutions prop -> list prop.";

  MLData safe;

   MLCode(Pred("new_safe",
     Out(safe, "Safe",
     Easy      "creates a safe: a store that persists across backtracking"),
   (fun _ ~depth -> incr safeno; !:(!safeno,ref []))),
  DocAbove);

   MLCode(Pred("stash_in_safe",
     In(safe,  "Safe",
     In(closed "A",   "Data",
     Easy      "stores Data in the Safe")),
   (fun (_,l) t ~depth -> l := t :: !l)),
  DocAbove);

   MLCode(Pred("open_safe",
     In(safe, "Safe",
     Out(list (closed "A"), "Data",
     Easy          "retrieves the Data stored in Safe")),
   (fun (_,l) _ ~depth -> !:(List.rev !l))),
  DocAbove);

  LPCode {|
% [if C T E] picks the first success of C then runs T (never E).
% if C has no success it runs E.
func if prop, fprop, fprop.
if B T _ :- B, !, T.
if _ _ E :- E.

% [if2 C1 B1 C2 B2 E] like if but with 2 then branches (and one else branch).
func if2 prop, fprop, prop, fprop, fprop.
if2 G1 P1 _  _  _ :- G1, !, P1.
if2 _  _  G2 P2 _ :- G2, !, P2.
if2 _  _  _  _  E :- !, E. |};

  MLCode(Pred("random.init",
     In(int, "Seed",
     Easy     "Initialize OCaml's PRNG with the given Seed"),
   (fun seed ~depth:_ -> Random.init seed)),
  DocAbove);

  MLCode(Pred("random.self_init",
     Easy     "Initialize OCaml's PRNG with some seed",
   (fun ~depth:_ -> Random.self_init ())),
  DocAbove);

  MLCode(Pred("random.int",
     In(int, "Bound",
     Out(int, "N",
     Easy     "unifies N with a random int between 0 and Bound (excluded)")),
   (fun bound _ ~depth -> !: (Random.int bound))),
  DocAbove);

]
;;

let elpi_stdlib_src = let open BuiltIn in [ 

  LPCode Builtin_stdlib.code

]

let ocaml_set_conv ~name (type a) (type b)
   (alpha : a Conversion.t) (module Set : Util.Set.S with type elt = a and type t = b) =
 
let set = OpaqueData.declare {
  OpaqueData.name;
  doc = "";
  pp = (fun fmt m -> Format.fprintf fmt "%a" Set.pp m );
  compare = (fun m1 m2 -> Set.compare m1 m2);
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
} in

let set = { set with Conversion.ty = Conversion.(TyName name) } in

let open BuiltIn in let open BuiltInData in 

set,
[
  LPCode ("kind "^name^" type.");

  MLCode(Pred(name^".empty",
    Out(set,"A",
    Easy "The empty set"),
    (fun _ ~depth -> !: Set.empty)),
  DocAbove);

  MLCode(Pred(name^".mem",
    In(alpha,"Elem",
    In(set,"A",
    Easy "Checks if Elem is in a")),
    (fun s m ~depth ->
      if Set.mem s m then () else raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".add",
    In(alpha,"Elem",
    In(set,"A",
    Out(set,"B",
    Easy "B is A union {Elem}"))),
    (fun s m _ ~depth -> !: (Set.add s m))),
  DocAbove);

  MLCode(Pred(name^".remove",
    In(alpha,"Elem",
    In(set,"A",
    Out(set,"B",
    Easy "B is A \\ {Elem}"))),
    (fun s m _ ~depth -> !: (Set.remove s m))),
  DocAbove);

    MLCode(Pred(name^".union",
    In(set,"A",
    In(set,"B",
    Out(set,"X",
    Easy "X is A union B"))),
    (fun a b _ ~depth -> !: (Set.union a b))),
    DocAbove);

   MLCode(Pred(name^".inter",
    In(set,"A",
    In(set,"B",
    Out(set,"X",
    Easy "X is A intersection B"))),
    (fun a b _ ~depth -> !: (Set.inter a b))),
  DocAbove);

  MLCode(Pred(name^".diff",
    In(set,"A",
    In(set,"B",
    Out(set,"X",
    Easy "X is A \\ B"))),
    (fun a b _ ~depth -> !: (Set.diff a b))),
  DocAbove);

  MLCode(Pred(name^".equal",
    In(set,"A",
    In(set,"B",
    Easy "tests A and B for equality")),
    (fun a b ~depth -> if Set.equal a b then () else raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".subset",
    In(set,"A",
    In(set,"B",
    Easy "tests if A is a subset of B")),
    (fun a b ~depth -> if Set.subset a b then () else raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".elements",
    In(set,"M",
    Out(list alpha,"L",
    Easy "L is M transformed into list")),
    (fun m _ ~depth -> !: (Set.elements m))),
  DocAbove);

  MLCode(Pred(name^".choose",
    In(set,"M",
    Out(alpha,"X",
    Easy "X is an element of M")),
    (fun m _ ~depth -> !: (try Set.choose m with Not_found -> raise No_clause))),
  DocAbove);

  MLCode(Pred(name^".min",
    In(set,"M",
    Out(alpha,"X",
    Easy "X is the smallest element of M")),
    (fun m _ ~depth -> !: (try Set.min_elt m with Not_found -> raise No_clause))),
  DocAbove);

  MLCode(Pred(name^".max",
    In(set,"M",
    Out(alpha,"X",
    Easy "X is the bigger of M")),
    (fun m _ ~depth -> !: (try Set.max_elt m with Not_found -> raise No_clause))),
  DocAbove);

  MLCode(Pred(name^".cardinal",
    In(set,"M",
    Out(int,"N",
    Easy "N is the number of elements of M")),
    (fun m _ ~depth -> !: (Set.cardinal m))),
  DocAbove);

  MLCode(Pred(name^".filter",
    In(set,"M",
    In(HOAdaptors.pred1 alpha,"F",
    Out(set,"M1",
    FullHO(ContextualConversion.unit_ctx, "Filter M w.r.t. the predicate F")))),
    (fun m f _ ~once ~depth _ _ state ->

      let state, m, gls = HOAdaptors.filter1 ~once ~depth ~filter:Set.filter f m state in
      
      state, !: m, gls
    )),
  DocAbove);

  MLCode(Pred(name^".map",
    In(set,"M",
    In(HOAdaptors.pred2 alpha alpha,"F",
    Out(set,"M1",
    FullHO(ContextualConversion.unit_ctx, "Map M w.r.t. the predicate F")))),
    (fun m f _ ~once ~depth _ _ state ->

      let state, m, gls = HOAdaptors.map1 ~once ~depth ~map:Set.map f m state in
      
      state, !: m, gls
    )),
  DocAbove);

  MLCode(Pred(name^".fold",
    In(set,"M",
    In(poly "A","Acc",
    In(HOAdaptors.pred2a alpha "A","F",
    Out(poly "A","Acc1",
    FullHO(ContextualConversion.unit_ctx, "fold M w.r.t. the predicate F"))))),
    (fun m a f _ ~once ~depth _ _ state ->

      let state, a, gls = HOAdaptors.fold1 ~once ~depth ~fold:Set.fold f m a state in
      
      state, !: a, gls
    )),
  DocAbove);


  MLCode(Pred(name^".partition",
  In(set,"M",
  In(HOAdaptors.pred1 alpha,"F",
  Out(set,"M1",
  Out(set,"M2",
  FullHO(ContextualConversion.unit_ctx, "Partitions M w.r.t. the predicate F, M1 is where F holds"))))),
  (fun m f _ _ ~once ~depth _ _ state ->

    let state, (m1, m2), gls = HOAdaptors.filter1 ~once ~depth ~filter:Set.partition f m state in
    
    state, !: m1 +! m2, gls
  )),
  DocAbove);


] 
;;
let ocaml_set ~name c m = snd (ocaml_set_conv ~name c m)

let ocaml_map ~name (type a)
   (alpha : a Conversion.t) (module Map : Util.Map.S with type key = a) =
 
let closed_A = BuiltInData.closed "A" in
let closed_B = BuiltInData.closed "B" in

let map = OpaqueData.declare {
  OpaqueData.name;
  doc = "";
  pp = (fun fmt m -> Format.fprintf fmt "%a" (Map.pp closed_A.pp) m );
  compare = (fun m1 m2 -> Map.compare Stdlib.compare m1 m2);
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
} in

let map a = { map with
  Conversion.ty = Conversion.(TyApp(name,TyName a,[])) } in

let open BuiltIn in let open BuiltInData in 

[
  LPDoc ("CAVEAT: the type parameter of "^name^" must be a closed term");
  LPCode ("kind "^name^" type -> type.");

  MLCode(Pred(name^".empty",
    Out(map "A","M",
    Easy "The empty map"),
    (fun _ ~depth -> !: Map.empty)),
  DocAbove);

  MLCode(Pred(name^".mem",
    In(alpha,"S",
    In(map "A","M",
    Easy "Checks if S is bound in M")),
    (fun s m ~depth ->
      if Map.mem s m then () else raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".add",
    In(alpha,"S",
    In(closed_A,"V",
    In(map "A","M",
    Out(map "A","M1",
    Easy "M1 is M where V is bound to S")))),
    (fun s l m _ ~depth -> !: (Map.add s l m))),
  DocAbove);

  MLCode(Pred(name^".remove",
    In(alpha,"S",
    In(map "A","M",
    Out(map "A","M1",
    Easy "M1 is M where S is unbound"))),
    (fun s m _ ~depth -> !: (Map.remove s m))),
  DocAbove);

  MLCode(Pred(name^".find",
    In(alpha,"S",
    In(map "A","M",
    Out(closed_A,"V",
    Easy "V is the binding of S in M"))),
    (fun s m _ ~depth ->
       try !: (Map.find s m)
       with Not_found -> raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".bindings",
    In(map "A","M",
    Out(list (pair alpha (closed_A)),"L",
    Easy "L is M transformed into an associative list")),
    (fun m _ ~depth -> !: (Map.bindings m))),
  DocAbove);

  MLCode(Pred(name^".filter",
    In(map "A","M",
    In(HOAdaptors.pred2 alpha closed_A,"F",
    Out(map "A","M1",
    FullHO(ContextualConversion.unit_ctx, "Filter M w.r.t. the predicate F")))),
    (fun m f _ ~once ~depth _ _ state ->

      let state, m, gls = HOAdaptors.filter2 ~once ~depth ~filter:Map.filter f m state in
      
      state, !: m, gls
    )),
  DocAbove);

  MLCode(Pred(name^".map",
    In(map "A","M",
    In(HOAdaptors.pred3 alpha closed_A closed_B,"F",
    Out(map "B","M1",
    FullHO(ContextualConversion.unit_ctx, "Map M w.r.t. the predicate F")))),
    (fun m f _ ~once ~depth _ _ state ->

      let state, m, gls = HOAdaptors.map2 ~once ~depth ~map:Map.mapi f m state in
      
      state, !: m, gls
    )),
  DocAbove);


  MLCode(Pred(name^".fold",
    In(map "A","M",
    In(poly "C","Acc",
    In(HOAdaptors.pred3a alpha closed_A "C","F",
    Out(poly "C","Acc1",
    FullHO(ContextualConversion.unit_ctx, "fold M w.r.t. the predicate F"))))),
    (fun m a f _ ~once ~depth _ _ state ->

      let state, a, gls = HOAdaptors.fold2 ~once ~depth ~fold:Map.fold f m a state in
      
      state, !: a, gls
    )),
  DocAbove);

] 
;;

module LocMap : Util.Map.S with type key = Ast.Loc.t = Util.Map.Make(Ast.Loc)

let elpi_map =  let open BuiltIn in [
  
    LPCode Builtin_map.code
    
]

let elpi_set =  let open BuiltIn in [
  
    LPCode Builtin_set.code
    
]

let string_set, string_set_decl = ocaml_set_conv ~name:"std.string.set" BuiltInData.string (module API.Compile.StrSet)
let int_set, int_set_decl = ocaml_set_conv ~name:"std.int.set"    BuiltInData.int    (module API.Utils.IntSet)
let loc_set, loc_set_decl = ocaml_set_conv ~name:"std.loc.set"    BuiltInData.loc    (module API.Utils.LocSet) 

let elpi_stdlib =
  elpi_stdlib_src @
  let open BuiltIn in
  let open BuiltInData in [
  MLCode(Pred("std.string.concat",
     In(string, "Separator",
     In(list string, "Items",
     Out(string, "Result",
     Easy     "concatenates Items interspersing Separator"))),
   (fun sep l _ ~depth:_ -> !: (String.concat sep l))),
  DocAbove);
  ] @
  ocaml_map ~name:"std.string.map" BuiltInData.string (module Util.StrMap) @ 
  ocaml_map ~name:"std.int.map"    BuiltInData.int    (module Util.IntMap) @ 
  ocaml_map ~name:"std.loc.map"    BuiltInData.loc    (module LocMap) @ 
  string_set_decl @ 
  int_set_decl @ 
  loc_set_decl @
  []
;;

let ocaml_runtime = let open BuiltIn in let open BuiltInData in [

  LPDoc "== Elpi runtime builtins =====================================";

  MLCode(Pred("trace.counter",
    In (string,"Name",
    Out(int,   "Value",
    Easy       "reads the Value of a trace point Name")),
  (fun s _ ~depth:_ -> !:(Trace_ppx_runtime.Runtime.get_cur_step ~runtime_id:0 s))),
  DocAbove);

  MLCode(Pred("gc.get",
    Out(int,"MinorHeapSize",
    Out(int,"MajorHeapIncrement",
    Out(int,"SpaceOverhead",
    Out(int,"Verbose",
    Out(int,"MaxOverhead",
    Out(int,"StackLimit",
    Out(int,"AllocationPolicy",
    Out(int,"WindowSize",
    Easy "Reads the current settings of the garbage collector. See also OCaml's Gc.control type documentation.")))))))),
  (fun _ _ _ _ _ _ _ _ ~depth:_ ->
    let { Gc.minor_heap_size; major_heap_increment; space_overhead; verbose; max_overhead; stack_limit; allocation_policy; window_size; _ } = Gc.get () in
    !: minor_heap_size +! major_heap_increment +! space_overhead +! verbose +! max_overhead +! stack_limit +! allocation_policy +! window_size)),
   DocAbove);

  MLCode(Pred("gc.set",
    In(unspec int,"MinorHeapSize",
    In(unspec int,"MajorHeapIncrement",
    In(unspec int,"SpaceOverhead",
    In(unspec int,"Verbose",
    In(unspec int,"MaxOverhead",
    In(unspec int,"StackLimit",
    In(unspec int,"AllocationPolicy",
    In(unspec int,"WindowSize",
    Easy "Writes the current settings of the garbage collector. Any parameter left unspecificed (eg _) is not changed. See also OCaml's Gc.control type documentation.")))))))),
   (fun minor_heap_size major_heap_increment space_overhead verbose max_overhead stack_limit allocation_policy window_size ~depth:_ ->
     let c = Gc.get () in
     let c = match minor_heap_size with Unspec -> c | Given x -> { c with minor_heap_size = x } in
     let c = match major_heap_increment with Unspec -> c | Given x -> { c with major_heap_increment = x } in
     let c = match space_overhead with Unspec -> c | Given x -> { c with space_overhead = x } in
     let c = match verbose with Unspec -> c | Given x -> { c with verbose = x } in
     let c = match max_overhead with Unspec -> c | Given x -> { c with max_overhead = x } in
     let c = match stack_limit with Unspec -> c | Given x -> { c with stack_limit = x } in
     let c = match allocation_policy with Unspec -> c | Given x -> { c with allocation_policy = x } in
     let c = match window_size with Unspec -> c | Given x -> { c with window_size = x } in
     Gc.set c)),
   DocAbove);

  MLCode(Pred("gc.minor",  Easy "See OCaml's Gc.minor documentation.",     (fun ~depth:_ -> Gc.minor ())),     DocAbove);
  MLCode(Pred("gc.major",  Easy "See OCaml's Gc.major documentation.",     (fun ~depth:_ -> Gc.major ())),     DocAbove);
  MLCode(Pred("gc.full",   Easy "See OCaml's Gc.full_major documentation.",(fun ~depth:_ -> Gc.full_major ())),DocAbove);
  MLCode(Pred("gc.compact",Easy "See OCaml's Gc.compact documentation.",   (fun ~depth:_ -> Gc.compact ())),   DocAbove);

  MLCode(Pred("gc.stat",
    Out(float,"MinorWords",
    Out(float,"PromotedWords",
    Out(float,"MajorWords",
    Out(int,"MinorCollections",
    Out(int,"MajorCollections",
    Out(int,"HeapWords",
    Out(int,"HeapChunks",
    Out(int,"LiveWords",
    Out(int,"LiveBlocks",
    Out(int,"FreeWords",
    Out(int,"FreeBlocks",
    Out(int,"LargestFree",
    Out(int,"Fragments",
    Out(int,"Compactions",
    Out(int,"TopHeapWords",
    Out(int,"StackSize",
    Easy "See OCaml's Gc.stat documentation.")))))))))))))))),
  (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ~depth:_ ->
    let { Gc.minor_words; promoted_words; major_words; minor_collections; major_collections; heap_words; heap_chunks; live_words; live_blocks; free_words; free_blocks; largest_free; fragments; compactions; top_heap_words; stack_size; _ } = Gc.stat () in
    !: minor_words +! promoted_words +! major_words +! minor_collections +! major_collections +! heap_words +! heap_chunks +! live_words +! live_blocks +! free_words +! free_blocks +! largest_free +! fragments +! compactions +! top_heap_words +! stack_size)),
  DocAbove);

  MLCode(Pred("gc.quick-stat",
    Out(float,"MinorWords",
    Out(float,"PromotedWords",
    Out(float,"MajorWords",
    Out(int,"MinorCollections",
    Out(int,"MajorCollections",
    Out(int,"HeapWords",
    Out(int,"HeapChunks",
    Out(int,"Compactions",
    Out(int,"TopHeapWords",
    Out(int,"StackSize",
    Easy "See OCaml's Gc.quick_stat documentation.")))))))))),
  (fun _ _ _ _ _ _ _ _ _ _ ~depth:_ ->
    let { Gc.minor_words; promoted_words; major_words; minor_collections; major_collections; heap_words; heap_chunks; compactions; top_heap_words; stack_size; _ } = Gc.quick_stat () in
    !: minor_words +! promoted_words +! major_words +! minor_collections +! major_collections +! heap_words +! heap_chunks +! compactions +! top_heap_words +! stack_size)),
  DocAbove);

]

let std_declarations =
  core_builtins @ io_builtins @ lp_builtins @ elpi_builtins @ elpi_nonlogical_builtins @ elpi_stdlib @ elpi_map @ elpi_set @ ocaml_runtime

let std_builtins =
  BuiltIn.declare ~file_name:"builtin.elpi" std_declarations
