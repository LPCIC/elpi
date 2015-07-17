(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module ASTFuncS = struct

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

end

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

let mkConj = function [f] -> f | l -> App(Const ASTFuncS.andf,l)
(* TODO: Bug here: mkConj2 should be right associative!
   But what is the difference??? *)
let mkConj2 = mkConj
let mkDisj  = function [f] -> f | l -> App(Const ASTFuncS.orf, l)
let mkImpl f1 f2 = App(Const ASTFuncS.implf,[f1;f2])
let mkCut = Const ASTFuncS.cutf
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
type clause = { head : term; hyps : term }
type program = clause list
type goal = term

let mkClause lhs rhs = { head = lhs; hyps = rhs }

let mkApp =
 function
    App(c,l1)::l2 -> App(c,l1@l2)
  | (Custom _ | Const _) as c::l2 -> App(c,l2)
  | _ -> raise NotInProlog

let fresh_uv_names = ref (-1);;

let mkFreshUVar () = incr fresh_uv_names; Const (ASTFuncS.from_string ("_" ^ string_of_int !fresh_uv_names))
let mkCon c = Const (ASTFuncS.from_string c)
let mkCustom c = Custom (ASTFuncS.from_string c)

let parsed = ref [];;
let cur_dirname = ref ""

let rec symlink_dirname f =
  try
    let link = Unix.readlink f in
    if not(Filename.is_relative link) then symlink_dirname link
    else symlink_dirname Filename.(concat (dirname f) link)
  with Unix.Unix_error _ -> Filename.dirname f

let parse_one e filename =
 let filename =
   if not (Filename.is_relative filename) then filename
   else Filename.concat !cur_dirname filename in
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
  let saved_cur_dirname = !cur_dirname in
  cur_dirname := symlink_dirname filename;
  try
   let res = Grammar.Entry.parse e (Stream.of_channel ch) in
   close_in ch;
   cur_dirname := saved_cur_dirname;
   res
  with Ploc.Exc(l,(Token.Error msg | Stream.Error msg)) ->
    close_in ch;
    let last = Ploc.last_pos l in
    (*let ctx_len = 70 in CSC: TO BE FIXED AND RESTORED
    let ctx = "…"
      let start = max 0 (last - ctx_len) in
      let s = String.make 101 '\007' in
      let ch = open_in filename in
      (try really_input ch s 0 100 with End_of_file -> ());
      close_in ch;
      let last = String.index s '\007' in
      "…" ^ String.sub s start last ^ "…" in
    raise (Stream.Error(Printf.sprintf "%s\nnear: %s" msg ctx))*)
    raise (Stream.Error(Printf.sprintf "%s\nnear: %d" msg last))
  | Ploc.Exc(_,e) -> close_in ch; raise e
 end

let parse e filenames =
  List.concat (List.map (parse_one e) filenames)

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

let digit = lexer [ '0'-'9' ]
let octal = lexer [ '0'-'7' ]
let hex = lexer [ '0'-'9' | 'A'-'F' | 'a'-'f' ]
let schar2 =
 lexer [ '+'  | '*' | '/' | '^' | '<' | '>' | '`' | '\'' | '?' | '@' | '#'
       | '~' ]
let schar = lexer [ schar2 | '-' | '=' | '$' | '&' | '!' | '_' ]
let lcase = lexer [ 'a'-'z' ]
let ucase = lexer [ 'A'-'Z' ]
let idchar = lexer [ lcase | ucase | digit | schar ]
let rec idcharstar = lexer [ idchar idcharstar | ]
let idcharplus = lexer [ idchar idcharstar ]
let rec num = lexer [ digit | digit num ]

let rec string = lexer [ '"' | _ string ]

let tok = lexer
  [ ucase idcharstar -> "CONSTANT", $buf 
  | lcase idcharstar -> "CONSTANT", $buf
  | schar2 idcharstar -> "CONSTANT", $buf
  | '$' lcase idcharstar -> "BUILTIN",$buf
  | '$' idcharstar -> "CONSTANT",$buf
  | num -> "INTEGER", $buf
  | num ?= [ '.' '0'-'9' ] '.' num -> "REAL", $buf (* CSC *)
  | "->" -> "ARROW", $buf
  | "->" idcharplus -> "CONSTANT", $buf
  | '-' idcharstar -> "CONSTANT", $buf
  | '_' -> "FRESHUV", "_"
  | '_' idcharplus -> "CONSTANT", $buf
  |  ":-"  -> "ENTAILS",$buf
  |  ":"  -> "COLON",$buf
  |  "::"  -> "CONS",$buf
  | ',' -> "COMMA",$buf
  | ';' -> "SEMICOLON",$buf
  | '.' -> "FULLSTOP",$buf
  | '.' num -> "REAL",$buf
  | '\\' -> "BIND","\\"
  | '(' -> "LPAREN",$buf
  | ')' -> "RPAREN",$buf
  | '[' -> "LBRACKET",$buf
  | ']' -> "RBRACKET",$buf
  | '|' -> "PIPE",$buf
  | '&' -> "AMPERSEND",","
  | '&' idcharplus -> "CONSTANT", $buf
  | '!' -> "BANG", $buf
  | '!' idcharplus -> "CONSTANT", $buf
  | "=>" -> "IMPL",$buf
  | "=>" idcharplus -> "CONSTANT",$buf
  | '=' idcharstar -> "CONSTANT",$buf
  | '"' string -> "LITERAL", let b = $buf in String.sub b 1 (String.length b-2)
]

let option_eq x y = match x, y with Some x, Some y -> x == y | _ -> x == y

module StringSet = Set.Make(String);;
let symbols = ref StringSet.empty;;

let rec lex c = parser bp
  | [< '( ' ' | '\n' | '\t' | '\r' ); s >] -> lex c s
  | [< '( '%' ); s >] -> comment c s
  | [< ?= [ '/'; '*' ]; '( '/' ); '( '*' ); s >] -> comment2 c s
  | [< s >] ep ->
       if option_eq (Stream.peek s) None then ("EOF",""), (bp, ep)
       else
       (match tok c s with
       | "CONSTANT","module" -> "MODULE", "module"
       | "CONSTANT","sig" -> "SIG", "SIG"
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
       | "CONSTANT","closed" -> "CLOSED", "closed" (* CSC: ??? *)

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

       | "CONSTANT", x when StringSet.mem x !symbols -> "SYMBOL",x

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

let tok_match =
 function
    ((s1:string),"") ->
      fun ((s2:string),v) ->
       if Pervasives.compare s1 s2 == 0 then v else raise Stream.Failure
  | ((s1:string),v1) ->
      fun ((s2:string),v2) ->
       if Pervasives.compare s1 s2==0 && Pervasives.compare v1 v2==0 then v2
       else raise Stream.Failure

let lex = {
  tok_func = lex_fun;
  tok_using =
   (fun x,y ->
      if x = "SYMBOL" && y <> "" then begin
       symbols := StringSet.add y !symbols
      end
   );
  tok_removing = (fun _ -> ());
  tok_match = tok_match;
  tok_text = (function (s,y) -> s ^ " " ^ y);
  tok_comm = None;
}

let g = Grammar.gcreate lex
let lp = Grammar.Entry.create g "lp"
let premise = Grammar.Entry.create g "premise"
let atom = Grammar.Entry.create g "atom"
let goal = Grammar.Entry.create g "goal"

let min_precedence = 0
let max_precedence = 256

let rec mk_precedences acc n =
 if n > max_precedence then List.rev acc
 else string_of_int n :: mk_precedences acc (n+1)
;;

let atom_levels =
  ["pi";"disjunction";"conjunction";"conjunction2";"implication"]
  @ mk_precedences [] min_precedence @ ["term";"app";"simple";"list"]

let () =
  let dummy_action =
    Gramext.action (fun _ ->
      failwith "internal error, lexer generated a dummy token") in
  (* Needed since campl5 on "delete_rule" remove the precedence level if it
     gets empty after the deletion. The lexer never generate the Stoken
     below. *)
  let dummy_prod = [ [ Gramext.Stoken ("DUMMY", "") ], dummy_action ] in
  Grammar.extend [ Grammar.Entry.obj atom, None,
    List.map (fun x -> Some x, Some Gramext.NonA, dummy_prod) atom_levels ]

let used_precedences = ref [];;

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
         [mkClause hd hyp]
     | MODULE; CONSTANT; FULLSTOP -> []
     | SIG; CONSTANT; FULLSTOP -> []
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
     | fix = FIXITY; syms = LIST1 CONSTANT SEP COMMA; prec = INTEGER; FULLSTOP ->
        let nprec = int_of_string prec in
        if nprec < min_precedence || nprec > max_precedence then
         assert false (* wrong precedence *)
        else
         let next_prec =
          if nprec < max_precedence then string_of_int (nprec+1) else "term" in
         let extend_one cst =
          let rule =
           (* NOTE: we do not distinguish between infix and infixl,
              prefix and prefix, postfix and postfixl *)
           match fix with
             "infix"
           | "infixl" ->
              [ Gramext.Sself ; Gramext.Stoken ("SYMBOL",cst); Gramext.Sself ],
              Gramext.action (fun t2 cst t1 _ ->mkApp [mkCon cst;t1;t2])
           | "infixr" ->
              (* needs extra hack below *)
              [ Gramext.Snterml (Grammar.Entry.obj atom, next_prec) ;
                Gramext.Stoken ("SYMBOL",cst);
                Gramext.Snterml (Grammar.Entry.obj atom, string_of_int nprec)],
              Gramext.action (fun t2 cst t1 _ ->mkApp [mkCon cst;t1;t2])
           | "prefix"
           | "prefixr" ->
               [ Gramext.Stoken ("SYMBOL",cst); Gramext.Sself ],
               Gramext.action (fun t cst _ ->mkApp [mkCon cst;t])
           | "postfix"
           | "postfixl" ->
               [ Gramext.Sself ; Gramext.Stoken ("SYMBOL",cst) ],
               Gramext.action (fun cst t _ ->mkApp [mkCon cst;t])
           | _ -> assert false
          in
          let rules =
           if not (List.mem nprec !used_precedences) && fix = "infixr" then
            let skip_prod =
             [ Gramext.Snterml (Grammar.Entry.obj atom, next_prec) ],
             Gramext.action (fun r _ -> r) in
            used_precedences := nprec::!used_precedences;
            [rule ; skip_prod ]
           else
            [rule]
          in
           Grammar.extend
            [ Grammar.Entry.obj atom,
              Some (Gramext.Level prec),
              [ None, Some Gramext.NonA, rules ]];
         in
          List.iter extend_one syms ; 
          []
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
    [[ p = premise -> p ]];
  premise : [[ a = atom -> a ]];
  concl : [[ a = atom LEVEL "0" -> a ]];
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
  atom : LEVEL "term"
     [[ l = LIST1 atom LEVEL "app" SEP CONS ->
          if List.length l = 1 then List.hd l
          else mkSeq l
     ]];
  atom : LEVEL "app"
      [[ hd = atom; args = LIST1 atom LEVEL "simple" -> mkApp (hd::args)
      ]];
  atom : LEVEL "simple" 
     [[ c = CONSTANT; b = OPT [ BIND; a = atom LEVEL "0" -> a ] ->
          (match b with
              None -> mkCon c
            | Some b -> mkLam c b)
      | u = FRESHUV -> mkFreshUVar ()
      | NIL -> mkNil
      | s = LITERAL -> mkString s
      | s = INTEGER -> mkInt (int_of_string s) 
      | bt = BUILTIN -> mkCustom bt
      | BANG -> mkCut
      | LPAREN; a = atom; RPAREN -> a ]];
  atom : LEVEL "list" 
     [[ LBRACKET; xs = LIST0 atom LEVEL "implication" SEP COMMA;
          tl = OPT [ PIPE; x = atom LEVEL "0" -> x ]; RBRACKET ->
          let tl = match tl with None -> mkNil | Some x -> x in
          if List.length xs = 0 && tl <> mkNil then 
            raise (Token.Error ("List with no elements cannot have a tail"));
          if List.length xs = 0 then mkNil
          else mkSeq (xs@[tl]) ]];
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
  let execname = Unix.readlink "/proc/self/exe" in
  let pervasives = Filename.dirname execname ^ "/pervasives.elpi" in
  parse lp (pervasives::filenames)

let parse_goal s : goal = parse_string goal s
