module type ASTFuncT =
  sig
    type t
    val compare : t -> t -> int
    val pp : t -> string
    val eq : t -> t -> bool
    val truef : t
    val andf : t
    val orf : t
    val implf : t
    val cutf : t
    val pif : t
    val sigmaf : t
    val eqf : t
    val isf : t
    val from_string : string -> t
  end;;

module ASTFuncS : ASTFuncT = 
  struct
    type t = string
    let compare = String.compare

    (* Hash consing *)
    let from_string =
     let h = Hashtbl.create 37 in
     function x ->
      try Hashtbl.find h x
      with Not_found -> Hashtbl.add h x x ; x

    let pp n = n
    let eq = (==)
    let truef = from_string "true"
    let andf = from_string ","
    let orf = from_string ";"
    let implf = from_string "=>"
    let cutf = from_string "!"
    let pif = from_string "pi"
    let sigmaf = from_string "sigma"
    let eqf = from_string "="
    let isf = from_string "is"

  end;;

(* Note: Appl(",",[]) is allowed in r.h.s. of clauses to represent
   axioms. Const "true" would not work because the definition of true
   would become true :- true. *)

type term =
   Const of ASTFuncS.t
 | Custom of ASTFuncS.t
 | App of term * term list
 | Lam of ASTFuncS.t * term
 | String of ASTFuncS.t
 | Int of int

(* TODO: to be moved elsewhere, obviously *)
module type Implementation =
 sig
  type query
  type program
  val query_of_ast : term -> query
  val program_of_ast : (term * term) list -> program
  val msg : query -> string
  val execute_once : program -> query -> bool
  val execute_loop : program -> query -> unit
  val pp_prolog : (term * term) list -> unit
 end

let mkConj = function [f] -> f | l -> App(Const ASTFuncS.andf,l)
(* TODO: Bug here: mkConj2 should be right associative!
   But what is the difference??? *)
let mkConj2 = mkConj
let mkDisj  = function [f] -> f | l -> App(Const ASTFuncS.orf, l)
let mkImpl f1 f2 = App(Const ASTFuncS.implf,[f1;f2])
let mkTrue = Const ASTFuncS.truef
let mkCut = Const ASTFuncS.cutf
let mkEq l r = App(Const ASTFuncS.eqf,[l;r]) 
let mkLam x t = Lam (ASTFuncS.from_string x,t)
let mkPi x t = App(Const ASTFuncS.pif,[mkLam x t])
let mkSigma x t = App(Const ASTFuncS.sigmaf,[mkLam x t])
let mkNil = Const (ASTFuncS.from_string "nil")
let mkString str = String (ASTFuncS.from_string str)
let mkInt i = Int i
let mkSeq l =
 let rec aux =
  function
    [] -> assert false
  | [e] -> e
  | hd::tl -> App(Const (ASTFuncS.from_string "::"),[hd;aux tl])
 in
  aux l
let mkIs x f = App(Const ASTFuncS.isf,[x;f])

exception NotInProlog;;

type formula = term
type program = (term * term) list
type goal = term

let mkClause lhs rhs = lhs,rhs

let true_clause = mkTrue, mkConj []

let eq_clause =
 let v = Const (ASTFuncS.from_string "X") in
  mkEq v v, mkConj []

let or_clauses =
 let v1 = Const (ASTFuncS.from_string "A") in
 let v2 = Const (ASTFuncS.from_string "B") in
  [ mkDisj [v1;v2], v1
  ; mkDisj [v1;v2], v2 ]

let mkApp =
 function
    App(c,l1)::l2 -> App(c,l1@l2)
  | (Custom _ | Const _) as c::l2 -> App(c,l2)
  | _ -> raise NotInProlog

(*let uvmap = ref [];;
let reset () = uvmap := []*)

let fresh_uv_names = ref (-1);;

let mkFreshUVar () = incr fresh_uv_names; Const (ASTFuncS.from_string ("_" ^ string_of_int !fresh_uv_names))
let mkCon c = Const (ASTFuncS.from_string c)
let mkCustom c = Custom (ASTFuncS.from_string c)

let parsed = ref [];;

let parse_one e filename =
 let filename =
  if Sys.file_exists filename then filename
  else if Filename.check_suffix filename ".elpi" then
   (* Backward compatibility with Teyjus *) 
   Filename.chop_extension filename ^ ".mod"
  else if Filename.check_suffix filename ".mod" then
   (* Backward compatibility with Teyjus *) 
   Filename.chop_extension filename ^ ".elpi"
  else raise (Failure ("file not found: " ^ filename)) in
 if List.mem filename !parsed then begin
  Printf.eprintf "already loaded %s\n%!" filename;
  []
 end else begin
  Printf.eprintf "loading %s\n%!" filename;
  parsed := filename::!parsed ;
  let ch = open_in filename in
  try let res = Grammar.Entry.parse e (Stream.of_channel ch) in close_in ch;res
  with Ploc.Exc(l,(Token.Error msg | Stream.Error msg)) ->
    close_in ch;
    let last = Ploc.last_pos l in
    let ctx_len = 70 in
    let ctx =
      let start = max 0 (last - ctx_len) in
      let s = String.make 101 '\007' in
      let ch = open_in filename in
      (try really_input ch s 0 100 with End_of_file -> ());
      close_in ch;
      let last = String.index s '\007' in
      "…" ^ String.sub s start last ^ "…" in
    raise (Stream.Error(Printf.sprintf "%s\nnear: %s" msg ctx))
  | Ploc.Exc(_,e) -> close_in ch; raise e
 end

let parse e filenames = List.concat (List.map (parse_one e) filenames)

let parse_string e s =
  try Grammar.Entry.parse e (Stream.of_string s)
  with Ploc.Exc(l,(Token.Error msg | Stream.Error msg)) ->
    let last = Ploc.last_pos l in
    let ctx_len = 70 in
    let ctx =
      let start = max 0 (last - ctx_len) in
      let len = min 100 (min (String.length s - start) last) in
      "…" ^ String.sub s start len ^ "…" in
    raise (Stream.Error(Printf.sprintf "%s\nnear: %s" msg ctx))
  | Ploc.Exc(_,e) -> raise e

let rec number = lexer [ '0'-'9' number | '0'-'9' ]
let rec ident =
  lexer [ [ 'a'-'z' | 'A'-'Z' | '\'' | '_' | '-' | '+' | '0'-'9' ] ident | ]

let rec string = lexer [ '"' | _ string ]

(*
let lvl_name_of s =
  match Str.split (Str.regexp_string "^") s with
  | [ x ] -> Name.make x, 0
  | [ x;l ] -> Name.make x, int_of_string l
  | _ -> raise (Token.Error ("<name> ^ <number> expected.  Got: " ^ s))
*)

let tok = lexer
  [ 'A'-'Z' ident -> "CONSTANT", $buf 
  | 'a'-'z' ident -> "CONSTANT", $buf
  | number -> "INTEGER", $buf
  | "->" -> "ARROW", $buf
  | '-' number -> "INTEGER", $buf
  | '_' -> "FRESHUV", "_"
  |  ":-"  -> "ENTAILS",$buf
  |  ":"  -> "COLON",$buf
  |  "::"  -> "CONS",$buf
  | ',' -> "COMMA",","
  | '&' -> "AMPERSEND",","
  | ';' -> "SEMICOLON",";"
  | '.' -> "FULLSTOP","."
  | '\\' -> "BIND","\\"
  | '/' -> "BIND","/"
  | '(' -> "LPAREN","("
  | ')' -> "RPAREN",")"
  | '[' -> "LBRACKET","["
  | ']' -> "RBRACKET","]"
  | '|' -> "PIPE","|"
  | "=>" -> "IMPL", $buf
  | '=' -> "EQUAL","="
  | '<' -> "LT","<"
  | '>' -> "GT",">"
  | '$' 'a'-'z' ident -> "BUILTIN",$buf
  | '!' -> "BANG", $buf
  | "!-!" -> "AH5",$buf
  | "!+!" -> "AH6",$buf
  | '@' -> "AT", $buf
  | '#' -> "SHARP", $buf
  | '?' -> "QMARK", $buf
  | '"' string -> "LITERAL", let b = $buf in String.sub b 1 (String.length b-2)
]

let option_eq x y = match x, y with Some x, Some y -> x == y | _ -> x == y

let rec lex c = parser bp
  | [< '( ' ' | '\n' | '\t' ); s >] -> lex c s
  | [< '( '%' ); s >] -> comment c s
  | [< '( '/' ); s >] ep ->
       if option_eq (Stream.peek s) (Some '*') then comment2 c s
       else ("BIND", "/"), (bp,ep)
  | [< s >] ep ->
       if option_eq (Stream.peek s) None then ("EOF",""), (bp, ep)
       else
       (match tok c s with
       | "CONSTANT","module" -> "MODULE", "module"
       | "CONSTANT","import" -> "IMPORT", "accumulate"
       | "CONSTANT","accum_sig" -> "ACCUM_SIG", "accum_sig"
       | "CONSTANT","use_sig" -> "USE_SIG", "use_sig"
       | "CONSTANT","local" -> "LOCAL", "local"
       | "CONSTANT","localkind" -> "LOCALKIND", "localkind"
       | "CONSTANT","useonly" -> "USEONLY", "useonly"
       | "CONSTANT","exportdef" -> "EXPORTDEF", "exportdef"
       | "CONSTANT","kind" -> "KIND", "kind"
       | "CONSTANT","typeabbrev" -> "TYPEABBREV", "typeabbrev"
       | "CONSTANT","type" -> "TYPE", "type"

       | "CONSTANT","end" -> "EOF", "end"
       | "CONSTANT","accumulate" -> "ACCUMULATE", "accumulate"
       | "CONSTANT","infixl" -> "FIXITY", "infixl"
       | "CONSTANT","infixr" -> "FIXITY", "infixr"
       | "CONSTANT","infix" -> "FIXITY", "infix"
       | "CONSTANT","prefix" -> "FIXITY", "prefix"
       | "CONSTANT","prefixr" -> "FIXITY", "prefixr"
       | "CONSTANT","postfix" -> "FIXITY", "postfix"
       | "CONSTANT","postfixl" -> "FIXITY", "postfixl"

       | "CONSTANT","pi" -> "PI", "pi"
       | "CONSTANT","sigma" -> "SIGMA", "sigma"
       | "CONSTANT","nil" -> "NIL", "nil"
       | "CONSTANT","delay" -> "DELAY","delay"
       | "CONSTANT","in" -> "IN","in"
       | "CONSTANT","is" -> "IS","is"
       | "CONSTANT","with" -> "WITH","with"
       | "CONSTANT","resume" -> "RESUME","resume"
       | "CONSTANT","context" -> "CONTEXT","context"
       | x -> x), (bp, ep)
and skip_to_dot c = parser
  | [< '( '.' ); s >] -> lex c s
  | [< '_ ; s >] -> skip_to_dot c s
and comment c = parser
  | [< '( '\n' ); s >] -> lex c s
  | [< '_ ; s >] -> comment c s
and comment2 c = parser
  | [< '( '*' ); s >] ->
       if option_eq (Stream.peek s) (Some '/') then (Stream.junk s; lex c s)
       else comment2 c s
  | [< '_ ; s >] -> comment2 c s


open Plexing

let lex_fun s =
  let tab = Hashtbl.create 207 in
  let last = ref Ploc.dummy in
  (Stream.from (fun id ->
     let tok, loc = lex Lexbuf.empty s in
     last := Ploc.make_unlined loc;
     Hashtbl.add tab id !last;
     Some tok)),
  (fun id -> try Hashtbl.find tab id with Not_found -> !last)

let tok_match ((s1:string),_) = (); function
  | ((s2:string),v) when Pervasives.compare s1 s2 == 0 -> v
  | (s2,v) -> raise Stream.Failure

let lex = {
  tok_func = lex_fun;
  tok_using = (fun _ -> ());
  tok_removing = (fun _ -> ());
  tok_match = tok_match;
  tok_text = (function (s,_) -> s);
  tok_comm = None;
}

let g = Grammar.gcreate lex
let lp = Grammar.Entry.create g "lp"
let premise = Grammar.Entry.create g "premise"
let atom = Grammar.Entry.create g "atom"
let goal = Grammar.Entry.create g "goal"

(*
let uvmap = ref []
let conmap = ref []
let reset () = uvmap := []; conmap := []
let uvlist () = List.map snd !uvmap
*)

(*
let get_uv u =
  if List.mem_assoc u !uvmap then List.assoc u !uvmap
  else
    let n = List.length !uvmap in
    uvmap := (u,n) :: !uvmap;
    n
*)
(*
let fresh_lvl_name () = lvl_name_of (Printf.sprintf "_%d" (List.length !uvmap))

let check_con n l =
  try
    let l' = List.assoc n !conmap in
    if l <> l' then
      raise
        (Token.Error("Constant "^Name.to_string n^" used at different levels"))
  with Not_found -> conmap := (n,l) :: !conmap
let mkFreshCon name lvl =
  let name = Name.make name in
  let t = mkConN name lvl in
  assert(not(List.mem_assoc name !conmap));
  conmap := (name,lvl) :: !conmap;
  t
*)

(*
let sigma_abstract t =
  let uvl = collect_Uv t in
  List.fold_left (fun p uv -> mkSigma1 (grab uv 1 p)) t uvl
*)

(* TODO : test that it is of the form of a clause
let check_clause x = ()
let check_goal x = ()*)

let atom_levels =
  ["pi";"disjunction";"conjunction";"conjunction2";"implication";"equality";"term";"app";"simple";"list"]

let () =
  Grammar.extend [ Grammar.Entry.obj atom, None,
    List.map (fun x -> Some x, Some Gramext.NonA, []) atom_levels ]

EXTEND
  GLOBAL: lp premise atom goal;
  lp: [ [ cl = LIST0 clause; EOF -> List.concat cl ] ];
(*  name : [ [ c = CONSTANT -> c | u = UVAR -> u | FRESHUV -> "_" ] ];
  label : [ [ COLON;
              n = name;
              p = OPT [ LT; n = name -> `Before n | GT; n = name -> `After n ];
              COLON -> n,p ] ];
*)
  clause :
    [[ (*name = OPT label;*)
       hd = concl; hyp = OPT [ ENTAILS; hyp = premise -> hyp ]; FULLSTOP ->
(*
         let name, insertion = match name with
         | None -> CN.fresh (), `Here
         | Some (s,pos) -> match pos with
             | None -> CN.make s, `Here
             | Some (`Before "_") -> CN.make ~float:`Begin s, `Begin
             | Some (`After "_") -> CN.make ~float:`End s, `End
             | Some (`Before n) -> CN.make s, `Before(CN.make ~existing:true n)
             | Some (`After n) -> CN.make s, `After(CN.make ~existing:true n) in
*)
         let hyp = match hyp with None -> mkConj [](*L.empty*) | Some h -> h in
(*
         let clause = sigma_abstract (mkImpl hyp (mkAtom hd)) in
         check_clause clause;
         reset (); 
         ([], key_of clause, clause, name), insertion*)
         (*reset ();*)
         [mkClause hd hyp]
     | MODULE; CONSTANT; FULLSTOP -> []
     | ACCUMULATE; filenames=LIST1 CONSTANT SEP COMMA; FULLSTOP ->
        parse lp (List.map (fun fn -> fn ^ ".mod") filenames)
     | IMPORT; LIST1 CONSTANT SEP COMMA; FULLSTOP -> []
     | ACCUM_SIG; filenames=LIST1 CONSTANT SEP COMMA; FULLSTOP ->
        parse lp (List.map (fun fn -> fn ^ ".sig") filenames)
     | USE_SIG; filenames=LIST1 CONSTANT SEP COMMA; FULLSTOP ->
        parse lp (List.map (fun fn -> fn ^ ".sig") filenames)
     | LOCAL; LIST1 CONSTANT SEP COMMA; FULLSTOP -> []
     | LOCAL; LIST1 CONSTANT SEP COMMA; type_; FULLSTOP -> []
     | LOCALKIND; LIST1 CONSTANT SEP COMMA; FULLSTOP -> []
     | LOCALKIND; LIST1 CONSTANT SEP COMMA; kind; FULLSTOP -> []
     | USEONLY; LIST1 CONSTANT SEP COMMA; FULLSTOP -> []
     | USEONLY; LIST1 CONSTANT SEP COMMA; type_; FULLSTOP -> []
     | EXPORTDEF; LIST1 CONSTANT SEP COMMA; FULLSTOP -> []
     | EXPORTDEF; LIST1 CONSTANT SEP COMMA; type_; FULLSTOP -> []
     | TYPE; LIST1 CONSTANT SEP COMMA; type_; FULLSTOP -> []
     | KIND; LIST1 CONSTANT SEP COMMA; kind; FULLSTOP -> []
     | TYPEABBREV; abbrform; TYPE; FULLSTOP -> []
     | FIXITY; LIST1 CONSTANT SEP COMMA; INTEGER; FULLSTOP -> []
    ]];
  kind:
    [[ TYPE -> ()
     | TYPE; ARROW; kind -> ()
    ]];
  type_:
    [[ ctype -> ()
     | ctype; ARROW; type_ -> ()
    ]];
  ctype:
    [[ CONSTANT -> ()
     | CONSTANT; LIST1 ctype -> ()
     | LPAREN; type_; RPAREN -> ()
    ]];
  abbrform:
    [[ CONSTANT -> ()
     | LPAREN; CONSTANT; LIST1 CONSTANT; RPAREN -> ()
     | LPAREN; abbrform; RPAREN -> ()
    ]];
  goal:
    [[ p = premise -> (*
         let g = sigma_abstract p in
         check_goal g;
         reset ();
         g*)
         (*reset (); *)
         p ]];
  premise : [[ a = atom -> a ]];
  concl : [[ a = atom LEVEL "term" -> a ]];
  atom : LEVEL "pi"
     [[ PI; x = CONSTANT; BIND; p = atom LEVEL "disjunction" -> mkPi x p
      (*| PI; annot = bound; x = bound; BIND; p = atom LEVEL "disjuction" ->
         let (x, is_uv), annot = x, Some (fst annot) in
         let bind = if is_uv then mkSigma1 else mkPi1 annot in
         bind (grab x 1 p)
      | PI; LPAREN; annot = atom LEVEL "disjuction"; RPAREN;
        x = bound; BIND; p = atom LEVEL "disjuction" ->
         let (x, is_uv), annot = x, Some annot in
         let bind = if is_uv then mkSigma1 else mkPi1 annot in
         bind (grab x 1 p)
      | PI; annot = atom LEVEL "list";
        x = bound; BIND; p = atom LEVEL "disjuction" ->
         let (x, is_uv), annot = x, Some annot in
         let bind = if is_uv then mkSigma1 else mkPi1 annot in
         bind (grab x 1 p)*)
      | SIGMA; x=CONSTANT; BIND; p=atom LEVEL "disjunction"-> mkSigma x p]];
  atom : LEVEL "disjunction"
     [[ l = LIST1 atom LEVEL "conjunction" SEP SEMICOLON -> mkDisj l ]];
  atom : LEVEL "conjunction"
     [[ l = LIST1 atom LEVEL "conjunction2" SEP COMMA -> mkConj l ]];
  atom : LEVEL "conjunction2"
     [[ l = LIST1 atom LEVEL "implication" SEP AMPERSEND -> mkConj2 l ]];
  atom : LEVEL "implication"
     [[ a = atom; IMPL; p = atom LEVEL "implication" ->
          mkImpl a p
      | a = atom; ENTAILS; p = premise ->
          mkImpl p a ]];
  atom : LEVEL "equality"
     [[ a = atom; EQUAL; b = atom LEVEL "term" ->
          mkEq a b
      | a = atom; IS; b = atom LEVEL "term" ->
          mkIs a b
     ]];
  atom : LEVEL "term"
     [[ l = LIST1 atom LEVEL "app" SEP CONS ->
          if List.length l = 1 then List.hd l
          else mkSeq l ]];
  atom : LEVEL "app"
     [[ hd = atom; args = LIST1 atom LEVEL "simple" ->
          (*match args with
          | [tl;x] when equal x sentinel -> mkVApp `Rev tl hd None
          | _ ->*) mkApp (hd::args) (*(L.of_list (hd :: args))*) ]];
  atom : LEVEL "simple" 
     [[ c = CONSTANT; b = OPT [ BIND; a = atom LEVEL "term" -> a ] ->
          (*let c, lvl = lvl_name_of c in 
          let x = mkConN c lvl in
          (match b with
          | None -> check_con c lvl; x
          | Some b ->  mkBin 1 (grab x 1 b))*)
          (match b with
              None -> mkCon c
            | Some b -> mkLam c b)
      | u = FRESHUV -> mkFreshUVar ()
      (*| i = REL -> mkDB (int_of_string (String.sub i 1 (String.length i - 1)))*)
      | NIL -> mkNil
      | s = LITERAL -> mkString s
      | s = INTEGER -> mkInt (int_of_string s) 
      (*| AT; hd = atom LEVEL "simple"; args = atom LEVEL "simple" ->
          mkVApp `Regular hd args None
      | AT -> sentinel
      | CONTEXT; hd = atom LEVEL "simple" -> mkAtomBiContext hd
      | QMARK; hd = atom LEVEL "simple"; args = atom LEVEL "simple" ->
          mkVApp `Flex hd args None
      | SHARP; hd = atom LEVEL "simple"; args = atom LEVEL "simple";
        info = OPT atom LEVEL "simple" ->
          mkVApp `Frozen hd args info*)
      | bt = BUILTIN -> mkCustom bt
      | BANG -> mkCut
      (*| DELAY; t = atom LEVEL "simple"; p = atom LEVEL "simple";
        vars = OPT [ IN; x = atom LEVEL "simple" -> x ];
        info = OPT [ WITH; x = atom LEVEL "simple" -> x ] ->
          mkDelay t p vars info
      | RESUME; t = atom LEVEL "simple"; p = atom LEVEL "simple" -> mkResume t p*)
      | LPAREN; a = atom; RPAREN -> a ]];
  atom : LEVEL "list" 
     [[ LBRACKET; xs = LIST0 atom LEVEL "implication" SEP COMMA;
          tl = OPT [ PIPE; x = atom LEVEL "term" -> x ]; RBRACKET ->
          let tl = match tl with None -> mkNil | Some x -> x in
          if List.length xs = 0 && tl <> mkNil then 
            raise (Token.Error ("List with no elements cannot have a tail"));
          if List.length xs = 0 then mkNil
          else mkSeq (xs@[tl]) ]];
  (*bound : 
    NOTE: IT WAS RETURNING A BOOLEAN TOO TO DISCRIMINATE THE TWO CASES
    [[ c = CONSTANT -> c
     | u = UVAR -> u ]
    ];*)
END

let parse_program (*?(ontop=[])*) ~filenames : program =
  (* let insertions = parse plp s in
  let insert prog = function
    | item, (`Here | `End) -> prog @ [item]
    | item, `Begin -> item :: prog
    | (_,_,_,name as item), `Before n ->
        let newprog = List.fold_left (fun acc (_,_,_,cn as c) ->
          if CN.equal n cn then acc @ [item;c]
          else acc @ [c]) [] prog in
        if List.length prog = List.length newprog then
          raise (Stream.Error ("unable to insert clause "^CN.to_string name));
        newprog
    | (_,_,_,name as item), `After n ->
        let newprog = List.fold_left (fun acc (_,_,_,cn as c) ->
          if CN.equal n cn then acc @ [c;item]
          else acc @ [c]) [] prog in
        if List.length prog = List.length newprog then
          raise (Stream.Error ("unable to insert clause "^CN.to_string name));
        newprog in
  List.fold_left insert ontop insertions*)
  true_clause::eq_clause::or_clauses@parse lp filenames

let parse_goal s : goal = parse_string goal s
(*let parse_data s : data = parse atom s*)
