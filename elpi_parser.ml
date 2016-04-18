(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Elpi_ast

type fixity = Infixl | Infixr | Infix | Prefix | Postfix

let set_precedence,precedence_of =
 let module ConstMap = Map.Make(Func) in 
 let precs = ref ConstMap.empty in
 (fun c p -> precs := ConstMap.add c p !precs),
 (fun c -> ConstMap.find c !precs)
;;

exception NotInProlog;;

let parsed = ref [];;
let cur_dirname = ref (Unix.getcwd ())

let rec readsymlinks f =
  try
    let link = Unix.readlink f in
    if not(Filename.is_relative link) then readsymlinks link
    else readsymlinks Filename.(concat (dirname f) link)
  with Unix.Unix_error _ -> f

let symlink_dirname f = Filename.dirname (readsymlinks f)

let make_absolute filename =
  if not (Filename.is_relative filename) then filename
  else Filename.concat !cur_dirname filename

let tjpath =
 let tjpath = try Sys.getenv "TJPATH" with Not_found -> "" in
 let tjpath = Str.split (Str.regexp ":") tjpath in
 let tjpath = List.map (fun f -> make_absolute (readsymlinks f)) tjpath in
 tjpath

module PointerFunc = struct
 type latex_export =
  {process:
    'a 'b. path:string -> shortpath:string -> ('a -> 'b) -> 'a -> 'b
   ; export: clause -> unit}
 let latex_export =
  ref {process=(fun ~path -> assert false) ; export=(fun _ -> assert false)}
 let set_latex_export f = latex_export := f
end;;

(*CSC: when parse_one opens a file for reading, open the .tex file
  for writing (and put the header) *)
let rec parse_one e (origfilename as filename) =
 let origprefixname = Filename.chop_extension origfilename in
 let prefixname,filename =
  let rec iter_tjpath dirnames =
   let filename,dirnames,relative =
    if not (Filename.is_relative filename) then filename,[],false
    else
     match dirnames with
        [] -> raise (Failure ("file not found in $TJPATH: " ^ filename))
      | dirname::dirnames->Filename.concat dirname filename,dirnames,true in
   let prefixname = Filename.chop_extension filename in
   let prefixname,filename =
    let change_suffix filename =
     if Filename.check_suffix filename ".elpi" then
      (* Backward compatibility with Teyjus *) 
      prefixname ^ ".mod"
     else if Filename.check_suffix filename ".mod" then
      (* Forward compatibility with Teyjus *) 
      prefixname ^ ".elpi"
     else filename in
    if Sys.file_exists filename then prefixname,filename
    else
     let changed_filename = change_suffix filename in
     if Sys.file_exists changed_filename then prefixname,changed_filename
     else if relative then iter_tjpath dirnames
     else raise (Failure ("file not found in $TJPATH: " ^ origfilename)) in
   prefixname,filename
  in
   iter_tjpath (!cur_dirname :: tjpath)
 in
 let inode = (Unix.stat filename).Unix.st_ino in
 if List.mem inode !parsed then begin
  Printf.eprintf "already loaded %s\n%!" origfilename;
  []
 end else begin
  let sigs =
   if Filename.check_suffix filename ".sig" then []
   else
    let signame = prefixname ^ ".sig" in
    if Sys.file_exists signame then
     let origsigname = origprefixname ^ ".sig" in
     parse_one e origsigname
    else [] in
  Printf.eprintf "loading %s\n%!" origfilename;
  parsed := inode::!parsed ;
  let ch = open_in filename in
  let saved_cur_dirname = !cur_dirname in
  cur_dirname := symlink_dirname filename;
  sigs @
  try
   let res = (!PointerFunc.latex_export).PointerFunc.process ~path:filename
    ~shortpath:origfilename (Grammar.Entry.parse e) (Stream.of_channel ch)in
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
    raise (Stream.Error(Printf.sprintf "%s\nnear: %s@%d" msg origfilename last))
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
       | '~' | '=' | '&' | '!' ]
let schar = lexer [ schar2 | '-' | '$' | '_' ]
let lcase = lexer [ 'a'-'z' ]
let ucase = lexer [ 'A'-'Z' ]
let idchar = lexer [ lcase | ucase | digit | schar ]
let rec idcharstar = lexer [ idchar idcharstar | ]
let idcharplus = lexer [ idchar idcharstar ]
let rec num = lexer [ digit | digit num ]

let rec stringchar = lexer
 [ "\\\\" / -> $add "\\"
 | "\\n" / -> $add "\n"
 | "\\b" / -> $add "\b"
 | "\\t" / -> $add "\t"
 | "\\r" / -> $add "\r"
 | "\\x" / -> $add "\x"
 | "\\\"" / -> $add "\""
 (* CSC: I have no idea how to implement the \octal syntax & friend :-(
 | "\\" / [ -> buflen := String.length $buf ; $add "" ] octal / ->
    $add (mkOctal "4")*)
 | "\n" -> raise Stream.Failure
 | _ ]
let rec string = lexer [ '"' / '"' string | '"' / | stringchar string ]

let constant = "CONSTANT" (* to use physical equality *)

let tok = lexer
  [ ucase idcharstar -> constant,$buf 
  | lcase idcharstar -> constant,$buf
  | schar2 ?= [ 'A'-'Z' ] -> constant,$buf
  | schar2 idcharstar -> constant,$buf
  | '$' lcase idcharstar -> "BUILTIN",$buf
  | '$' idcharstar -> constant,$buf
  | num -> "INTEGER",$buf
  | num ?= [ '.' '0'-'9' ] '.' num -> "FLOAT",$buf
  | "->" -> "ARROW",$buf
  | "->" idcharplus -> constant,$buf
  | '-' idcharstar -> constant,$buf
  | '_' -> "FRESHUV", "_"
  | '_' idcharplus -> constant,$buf
  | ":-"  -> constant,$buf
  | ":"  -> "COLON",$buf
  | ":="  -> constant,$buf
  | "::"  -> constant,$buf
  | ',' -> constant,$buf
  | ';' -> constant,$buf
  | '?' -> constant,$buf
  | '.' -> "FULLSTOP",$buf
  | '.' num -> "FLOAT",$buf
  | '\\' -> "BIND","\\"
  | '(' -> "LPAREN",$buf
  | ')' -> "RPAREN",$buf
  | '[' -> "LBRACKET",$buf
  | ']' -> "RBRACKET",$buf
  | '{' -> "LCURLY",$buf
  | '}' -> "RCURLY",$buf
  | '|' -> "PIPE",$buf
  | '"' / string -> "LITERAL", $buf
]

let option_eq x y = match x, y with Some x, Some y -> x == y | _ -> x == y

module StringSet = Set.Make(String);;
let symbols = ref StringSet.empty;;

let literatebuf = Buffer.create 17;;

(* %! <= \leq creates a map from "<=" to "\leq" *)
let set_liter_map,get_literal,print_lit_map =
 let module LitMap = Map.Make(String) in
 let lit_map = ref LitMap.empty in
 (fun s1 s2 -> lit_map := LitMap.add s1 s2 !lit_map),
 (fun s -> LitMap.find s !lit_map),
 (fun () -> LitMap.iter (fun s1 s2 -> Format.printf "\n%s -> %s\n%!" s1 s2) !lit_map);;


let rec lex c = parser bp
  | [< '( ' ' | '\n' | '\t' | '\r' ); s >] -> lex c s
  | [< '( '%' ); '( '!'); s >] -> literatecomment c s
  | [< '( '%' ); s >] -> comment c s
  | [< ?= [ '/'; '*' ]; '( '/' ); '( '*' ); s >] -> comment2 0 c s
  | [< s >] ep ->
       if option_eq (Stream.peek s) None then ("EOF",""), (bp, ep)
       else
        let (x,y) as res = tok c s in
        (if x == constant then
         (match y with
         | "module" -> "MODULE", "module"
         | "sig" -> "SIG", "SIG"
         | "import" -> "IMPORT", "accumulate"
         | "accum_sig" -> "ACCUM_SIG", "accum_sig"
         | "use_sig" -> "USE_SIG", "use_sig"
         | "local" -> "LOCAL", "local"
         | "mode" -> "MODE", "mode"
         | "constraint" -> "CONSTRAINT", "constraint"
         | "localkind" -> "LOCALKIND", "localkind"
         | "useonly" -> "USEONLY", "useonly"
         | "exportdef" -> "EXPORTDEF", "exportdef"
         | "kind" -> "KIND", "kind"
         | "typeabbrev" -> "TYPEABBREV", "typeabbrev"
         | "type" -> "TYPE", "type"
         | "closed" -> "CLOSED", "closed"
         | "end" -> "EOF", "end"
         | "accumulate" -> "ACCUMULATE", "accumulate"
         | "infixl" -> "FIXITY", "infixl"
         | "infixr" -> "FIXITY", "infixr"
         | "infix" -> "FIXITY", "infix"
         | "prefix" -> "FIXITY", "prefix"
         | "prefixr" -> "FIXITY", "prefixr"
         | "postfix" -> "FIXITY", "postfix"
         | "postfixl" -> "FIXITY", "postfixl"
        
         | x when StringSet.mem x !symbols -> "SYMBOL",x
        
         | _ -> res) else res), (bp, ep)
and skip_to_dot c = parser
  | [< '( '.' ); s >] -> lex c s
  | [< '_ ; s >] -> skip_to_dot c s
and literatecomment c = parser
  | [< '( '\n' ); s >] ->
      let buf = Buffer.contents literatebuf in
      Buffer.reset literatebuf;
      let list_str = Str.split (Str.regexp " +") buf in
      (match list_str with
       | [s1;s2] -> set_liter_map s1 s2; 
       | _ -> prerr_endline ("Wrong syntax: " ^ buf); exit 1);
  (*   print_lit_map (); *)
  (*   prerr_endline buf; (*register imperatively*) *)
      lex c s
  | [< '_ as x ; s >] -> Buffer.add_char literatebuf x; literatecomment c s
and comment c = parser
  | [< '( '\n' ); s >] -> lex c s
  | [< '_ ; s >] -> comment c s
and comment2 lvl c = parser
  | [< ?= [ '*'; '/' ]; '( '*' ); '( '/'); s >] ->
      if lvl = 0 then lex c s else comment2 (lvl-1) c s
  | [< ?= [ '/'; '*' ]; '( '/' ); '( '*' ); s >] -> comment2 (lvl+1) c s
  | [< '_ ; s >] -> comment2 lvl c s


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
let goal = Grammar.Entry.create g "goal"

let min_precedence = -1  (* minimal precedence in use *)
let lam_precedence = -1  (* precedence of lambda abstraction *)
let umin_precedence = 0   (* minimal user defined precedence *)
let umax_precedence = 256 (* maximal user defined precedence *)
let appl_precedence = umax_precedence + 1 (* precedence of application *)
let inf_precedence = appl_precedence+1 (* greater than any used precedence*)

let dummy_prod =
 let dummy_action =
   Gramext.action (fun _ ->
     failwith "internal error, lexer generated a dummy token") in
 [ [ Gramext.Stoken ("DUMMY", "") ], dummy_action ]

let used_precedences = ref [];;
let is_used n =
 let rec aux visited acc =
  function
     hd::_  when hd = n ->
     !used_precedences, (Gramext.Level (string_of_int n), None)
   | hd::tl when hd < n ->
     aux (hd::visited) (Gramext.After (string_of_int hd)) tl
   | l -> List.rev (n::visited) @ l, (acc, Some (string_of_int n))
 in
  let used, res = aux [] Gramext.First !used_precedences in
  used_precedences := used ;
  res
;;


EXTEND
  GLOBAL: lp goal;
  lp: [ [ cl = LIST0 clause; EOF -> List.concat cl ] ];
  const_sym:
    [[ c = CONSTANT -> c
     | s = SYMBOL -> s ]];
  filename:
    [[ c = CONSTANT -> c
     | c = LITERAL -> c ]];
  mode :
    [[ LPAREN; c = CONSTANT;
       l = LIST1 [ CONSTANT "i" -> true | CONSTANT "o" -> false ]; RPAREN;
       alias = OPT[ CONSTANT "xas"; c = CONSTANT;
                 subst = OPT [ LPAREN;
                               l = LIST1 [ c1 = CONSTANT; ARROW;
                                       c2 = CONSTANT ->
                                (Func.from_string c1, Func.from_string c2) ]
                 SEP SYMBOL ","; RPAREN -> l ] ->
                 Func.from_string c,
                 match subst with None -> [] | Some l -> l ] ->
      Func.from_string c,l,alias]];
  clause :
    [[ f = atom; FULLSTOP ->
       (!PointerFunc.latex_export).PointerFunc.export f ;
       [Clause f]
     | LCURLY -> [Begin]
     | RCURLY -> [End]
     | MODE; m = LIST1 mode SEP SYMBOL ","; FULLSTOP -> [Mode m]
     | CONSTRAINT; names=LIST0 CONSTANT; LCURLY ->
         [ Constraint (List.map Func.from_string names) ]
     | MODULE; CONSTANT; FULLSTOP -> []
     | SIG; CONSTANT; FULLSTOP -> []
     | ACCUMULATE; filenames=LIST1 filename SEP SYMBOL ","; FULLSTOP ->
        [Accumulated(parse lp (List.map (fun fn -> fn ^ ".mod") filenames))]
     | IMPORT; filenames=LIST1 CONSTANT SEP SYMBOL ","; FULLSTOP ->
        [Accumulated(parse lp (List.map (fun fn -> fn ^ ".mod") filenames))]
     | ACCUM_SIG; filenames=LIST1 filename SEP SYMBOL ","; FULLSTOP ->
        [Accumulated(parse lp (List.map (fun fn -> fn ^ ".sig") filenames))]
     | USE_SIG; filenames=LIST1 filename SEP SYMBOL ","; FULLSTOP ->
        [Accumulated(parse lp (List.map (fun fn -> fn ^ ".sig") filenames))]
     | LOCAL; vars = LIST1 const_sym SEP SYMBOL ","; FULLSTOP ->
        List.map (fun x -> mkLocal x) vars
     | LOCAL; vars = LIST1 const_sym SEP SYMBOL ","; type_; FULLSTOP ->
        List.map (fun x -> mkLocal x) vars
     | LOCALKIND; LIST1 const_sym SEP SYMBOL ","; FULLSTOP -> []
     | LOCALKIND; LIST1 const_sym SEP SYMBOL ","; kind; FULLSTOP -> []
     | CLOSED; LIST1 const_sym SEP SYMBOL ","; FULLSTOP -> []
     | CLOSED; LIST1 const_sym SEP SYMBOL ","; type_; FULLSTOP -> []
     | USEONLY; LIST1 const_sym SEP SYMBOL ","; FULLSTOP -> []
     | USEONLY; LIST1 const_sym SEP SYMBOL ","; type_; FULLSTOP -> []
     | EXPORTDEF; LIST1 const_sym SEP SYMBOL ","; FULLSTOP -> []
     | EXPORTDEF; LIST1 const_sym SEP SYMBOL ","; type_; FULLSTOP -> []
     | TYPE; LIST1 const_sym SEP SYMBOL ","; type_; FULLSTOP -> []
     | KIND; LIST1 const_sym SEP SYMBOL ","; kind; FULLSTOP -> []
     | TYPEABBREV; abbrform; TYPE; FULLSTOP -> []
     | fix = FIXITY; syms = LIST1 const_sym SEP SYMBOL ","; prec = INTEGER; FULLSTOP ->
        let nprec = int_of_string prec in
        if nprec < umin_precedence || nprec > umax_precedence then
         assert false (* wrong precedence *)
        else
         let extend_one cst =
          let binrule =
           [ Gramext.Sself ; Gramext.Stoken ("SYMBOL",cst); Gramext.Sself ],
           Gramext.action (fun t2 cst t1 _ ->mkApp [mkCon cst;t1;t2]) in
          let prerule =
           [ Gramext.Stoken ("SYMBOL",cst); Gramext.Sself ],
           Gramext.action (fun t cst _ -> mkApp [mkCon cst;t]) in
          let postrule =
           [ Gramext.Sself ; Gramext.Stoken ("SYMBOL",cst) ],
           Gramext.action (fun cst t _ -> mkApp [mkCon cst;t]) in
          let fixity,rule,ppinfo =
           (* NOTE: we do not distinguish between infix and infixl,
              prefix and prefix, postfix and postfixl *)
           match fix with
             "infix"    -> Gramext.NonA,   binrule,  (Infix,nprec)
           | "infixl"   -> Gramext.LeftA,  binrule,  (Infixl,nprec)
           | "infixr"   -> Gramext.RightA, binrule,  (Infixr,nprec)
           | "prefix"   -> Gramext.NonA,   prerule,  (Prefix,nprec)
           | "prefixr"  -> Gramext.RightA, prerule,  (Prefix,nprec)
           | "postfix"  -> Gramext.NonA,   postrule, (Postfix,nprec)
           | "postfixl" -> Gramext.LeftA,  postrule, (Postfix,nprec)
           | _ -> assert false in
          set_precedence (Func.from_string cst) ppinfo ;
          let where,name = is_used nprec in
           Grammar.extend
            [Grammar.Entry.obj atom, Some where, [name, Some fixity, [rule]]];
         in
          List.iter extend_one syms ; 
          (* Debugging code
          prerr_endline "###########################################";
          Grammar.iter_entry (
            Grammar.print_entry Format.err_formatter
          ) (Grammar.Entry.obj atom);
          prerr_endline ""; *)
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
  atom :
   [ "term"
      [ hd = atom; args = LIST1 atom LEVEL "abstterm" -> mkApp (hd :: args) ]
   | "abstterm"
      [ c = CONSTANT; OPT [ COLON ; type_ ] ; b = OPT [ BIND; a = atom LEVEL "0" -> a ] ->
          (match b with
              None -> mkCon c
            | Some b -> mkLam c b)
      | c = ARROW; a = atom LEVEL "abstterm" -> mkApp [mkCon c; a]
      | u = FRESHUV ; OPT [ COLON ; type_ ] -> mkFreshUVar ()
      | s = LITERAL -> mkString s
      | s = INTEGER -> mkInt (int_of_string s) 
      | s = FLOAT -> mkFloat (float_of_string s) 
      | bt = BUILTIN ; OPT [ COLON ; type_ ] -> mkCustom bt
      | LPAREN; a = atom; RPAREN -> a
        (* 120 is the first level after 110, which is that of ,
           Warning: keep the hard-coded constant in sync with
           the list_element_prec below :-(
        *)
      | LBRACKET; xs = LIST0 atom LEVEL "120" SEP SYMBOL ",";
          tl = OPT [ PIPE; x = atom LEVEL "0" -> x ]; RBRACKET ->
          let tl = match tl with None -> mkNil | Some x -> x in
          if List.length xs = 0 && tl <> mkNil then 
            raise (Token.Error ("List with no elements cannot have a tail"));
          if List.length xs = 0 then mkNil
          else mkSeq (xs@[tl]) ]];
END

(* 120 is the first level after 110, which is that of , *)
let list_element_prec = 120

let my_program_only = ref [];;

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
;;

let parse_goal s : goal = parse_string goal s

let parse_goal_from_stream strm =
  try Grammar.Entry.parse goal strm
  with
    Ploc.Exc(l,(Token.Error msg | Stream.Error msg)) -> raise(Stream.Error msg)
  | Ploc.Exc(_,e) -> raise e


