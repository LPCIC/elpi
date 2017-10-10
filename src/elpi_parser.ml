(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_ast

type fixity = Infixl | Infixr | Infix | Prefix | Postfix

let set_precedence,precedence_of =
 let module ConstMap = Map.Make(Func) in 
 let precs = ref ConstMap.empty in
 (fun c p -> precs := ConstMap.add c p !precs),
 (fun c -> ConstMap.find c !precs)
;;

let cur_dirname = ref "./"
let last_loc : Ploc.t ref = ref (Ploc.make_loc "dummy" 1 0 (0, 0) "")
let set_fname ?(line=1) fname = last_loc := (Ploc.make_loc fname line 0 (0, 0) "")

let rec readsymlinks f =
  try
    let link = Unix.readlink f in
    if not(Filename.is_relative link) then readsymlinks link
    else readsymlinks Filename.(concat (dirname f) link)
  with Unix.Unix_error _ | Failure _ -> f

let symlink_dirname f = Filename.dirname (readsymlinks f)

let make_absolute filename =
  if not (Filename.is_relative filename) then filename
  else Filename.concat !cur_dirname filename

let cur_tjpath = ref []

let set_tjpath cwd paths =
 cur_dirname := cwd;
 let tjpath = List.map (fun f -> make_absolute (readsymlinks f)) paths in
 cur_tjpath := tjpath

module PointerFunc = struct
 type latex_export =
  {process:
    'a 'b. path:string -> shortpath:string -> ('a -> 'b) -> 'a -> 'b
   ; export: clause -> unit}
 let latex_export =
  ref { process = (fun ~path  ~shortpath f x -> f x);
        export = (fun _ -> ()) }
 let set_latex_export f = latex_export := f
end;;

(*CSC: when parse_one opens a file for reading, open the .tex file
  for writing (and put the header) *)
(* the parsed variable is a cache to avoid parsing the same file twice *)

let parse_silent = ref true
let parsed = ref []

exception File_not_found of string

let rec parse_one e (origfilename as filename) =
 let origprefixname =
   try Filename.chop_extension origfilename
   with Invalid_argument _ ->
     raise (Failure ("File "^origfilename^" has no extension")) in
 let prefixname, filename =
  let rec iter_tjpath dirnames =
   let filename,dirnames,relative =
    if not (Filename.is_relative filename) then filename,[],false
    else
     match dirnames with
        [] -> raise (File_not_found filename)
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
     else raise (File_not_found origfilename) in
   prefixname,filename
  in
   let dirs = !cur_dirname :: !cur_tjpath in 
   try iter_tjpath dirs
   with File_not_found f ->
     raise (Failure ("File "^f^" not found in: " ^ String.concat ", " dirs))
 in
 let inode = Digest.file filename in
 if List.mem_assoc inode !parsed then begin
  if not !parse_silent then Printf.eprintf "already loaded %s\n%!" origfilename;
  match !(List.assoc inode !parsed) with
  | None -> []
  | Some l -> l
 end else begin
  let sigs =
   if Filename.check_suffix filename ".sig" then []
   else
    let signame = prefixname ^ ".sig" in
    if Sys.file_exists signame then
     let origsigname = origprefixname ^ ".sig" in
     parse_one e origsigname
    else [] in
  if not !parse_silent then
    Printf.eprintf "loading %s (%s)\n%!" origfilename (Digest.to_hex inode);
  let ast = ref None in
  parsed := (inode,ast) ::!parsed ;
  let ch = open_in filename in
  let saved_cur_dirname = !cur_dirname in
  cur_dirname := symlink_dirname filename;
  sigs @
  try
   let loc = !last_loc in
   set_fname filename;
   let res = (!PointerFunc.latex_export).PointerFunc.process ~path:filename
    ~shortpath:origfilename (Grammar.Entry.parse e) (Stream.of_channel ch)in
   last_loc := loc;
   ast := Some res;
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
let symbchar = lexer [ lcase | ucase | digit | schar | ':' ]
let rec symbcharstar = lexer [ symbchar symbcharstar | ]

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
 | _ ]
let string_of_chars chars = 
  let buf = Buffer.create 10 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf
let spy ?(name="") ?pp f b s =
  let l = Stream.npeek 10 s in
  Printf.eprintf "%s< %s | %S...\n"
    name (Plexing.Lexbuf.get b) (string_of_chars l);
  try
    let b = f b s in
    begin match pp with
    | None -> Printf.eprintf "%s> ok" name
    | Some pp -> Printf.eprintf "%s> %s\n\n" name (pp b)
    end; b
  with e ->
    Printf.eprintf "nope\n";
    raise e
;;
let rec string = lexer [ '"' / '"' string | '"' / | stringchar string ]
let any = lexer [ _ ]
let mk_terminator keep n b s =
  let l = Stream.npeek n s in
  if List.length l = n && List.for_all ((=) '}') l then begin
   let b = ref b in
   for i = 1 to n do
     Stream.junk s;
     if keep then b := Plexing.Lexbuf.add '}' !b;
   done; !b
  end else raise Stream.Failure
let rec quoted_inner d = (*spy ~name:"quoted_inner"*) (lexer
  [ d
  | "{" (maybe_quoted_inner d)
  | any (quoted_inner d) ])
and maybe_quoted_inner d = (*spy ~name:"maybe"*) (lexer
  [ d
  | "{" (quoted true 2) (quoted_inner d)
  | any (quoted_inner d) ])
and  quoted keep n = (*spy ~name:"quoted"*) (lexer
  [ "{" (quoted keep (n+1))
  | (quoted_inner (mk_terminator keep n)) ])

let constant = "CONSTANT" (* to use physical equality *)

let rec tok b s = (*spy ~name:"tok" ~pp:(fun (a,b) -> a ^ " " ^ b)*) (lexer
  [ ucase idcharstar -> constant,$buf 
  | lcase idcharstar -> constant,$buf
  | schar2 ?= [ 'A'-'Z' ] -> constant,$buf
  | schar2 symbcharstar -> constant,$buf
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
  | '(' [ is_infix ->
             "ESCAPE",  String.(sub $buf 0 (length $buf - 1))
        | -> "LPAREN",$buf ]
  | ')' -> "RPAREN",$buf
  | '[' -> "LBRACKET",$buf
  | ']' -> "RBRACKET",$buf
  | "{{" / (quoted false 2) -> "QUOTED", $buf
  | '{' -> "LCURLY",$buf
  | '}' -> "RCURLY",$buf
  | '|' -> "PIPE",$buf
  | '"' / string -> "LITERAL", $buf
]) b s
and is_infix_aux b s =
  let k1, s1 = tok b s in
  let k2, s2 = tok b s in 
  if k1 == constant && k2 = "RPAREN" && not (is_capital s1.[0])
  then string2lexbuf2 s1 s2
  else if k1 = "LBRACKET" && k2 = "RBRACKET" then
    let k3, s3 = tok b s in
    if k3 = "RPAREN" then string2lexbuf3 s1 s2 s3
    else raise Stream.Failure
  else raise Stream.Failure
and protect max_chars lex b s =
  let l = Stream.npeek max_chars s in
  let safe_s = Stream.of_list l in
  let to_junk, res = lex Plexing.Lexbuf.empty safe_s in
  for i = 0 to to_junk-1 do Stream.junk s; done;
  res
and is_infix b s = protect 6 is_infix_aux b s
and string2lexbuf2 s1 s2 =
  let b = ref Plexing.Lexbuf.empty in
  String.iter (fun c -> b := Plexing.Lexbuf.add c !b) s1;
  String.iter (fun c -> b := Plexing.Lexbuf.add c !b) s2;
  String.(length s1 + length s2), !b
and string2lexbuf3 s1 s2 s3 =
  let b = ref Plexing.Lexbuf.empty in
  String.iter (fun c -> b := Plexing.Lexbuf.add c !b) s1;
  String.iter (fun c -> b := Plexing.Lexbuf.add c !b) s2;
  String.iter (fun c -> b := Plexing.Lexbuf.add c !b) s3;
  String.(length s1 + length s2 + length s3), !b
and is_capital c = match c with 'A'..'Z' -> true | _ -> false

let option_eq x y = match x, y with Some x, Some y -> x == y | _ -> x == y

module StringSet = Set.Make(String);;
let symbols = ref StringSet.empty;;

let literatebuf = Buffer.create 17;;

(* %! <= \leq creates a map from "<=" to "\leq" *)
let set_liter_map,get_literal,print_lit_map =
 let lit_map = ref StrMap.empty in
 (fun s1 s2 -> lit_map := StrMap.add s1 s2 !lit_map),
 (fun s -> StrMap.find s !lit_map),
 (fun () -> StrMap.iter (fun s1 s2 -> Format.printf "\n%s -> %s\n%!" s1 s2) !lit_map);;

let succ_line loc =
  Ploc.make_loc (Ploc.file_name loc) (Ploc.line_nb loc + 1) 0
                (Ploc.last_pos loc, Ploc.last_pos loc) (Ploc.comment loc)

let set_loc_pos loc bp ep =
  Ploc.sub loc (bp - Ploc.first_pos loc) (ep - bp)

let rec lex loc c = parser bp
  | [< '( ' ' | '\t' | '\r' ); s >] -> lex loc c s
  | [< '( '\n' ) ; s >] -> lex (succ_line loc) c s
  | [< '( '%' ); '( '!'); s >] -> literatecomment loc c s
  | [< '( '%' ); s >] -> comment loc c s
  | [< ?= [ '/'; '*' ]; '( '/' ); '( '*' ); s >] -> comment2 loc 0 c s
  | [< s >] ep ->
       if option_eq (Stream.peek s) None
       then ("EOF",""), (set_loc_pos loc bp ep)
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
         | "pred" -> "PRED", "pred"
         | "mode" -> "MODE", "mode"
         | "macro" -> "MACRO", "macro"
         | "rule" -> "RULE", "rule"
         | "constraint" -> "CONSTRAINT", "constraint"
         | "localkind" -> "LOCALKIND", "localkind"
         | "useonly" -> "USEONLY", "useonly"
         | "exportdef" -> "EXPORTDEF", "exportdef"
         | "kind" -> "KIND", "kind"
         | "typeabbrev" -> "TYPEABBREV", "typeabbrev"
         | "type" -> "TYPE", "type"
         | "external" -> "EXTERNAL", "external"
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
        
         | _ -> res) else res), (set_loc_pos loc bp ep)
and skip_to_dot loc c = parser
  | [< '( '.' ); s >] -> lex loc c s
  | [< '_ ; s >] -> skip_to_dot loc c s
and literatecomment loc c = parser
  | [< '( '\n' ); s >] ->
      let loc = succ_line loc in
      let buf = Buffer.contents literatebuf in
      Buffer.reset literatebuf;
      let list_str = Str.split (Str.regexp " +") buf in
      (match list_str with
       | [s1;s2] -> set_liter_map s1 s2; 
       | _ -> prerr_endline ("Wrong syntax: literate comment: " ^ buf); exit 1);
  (*   print_lit_map (); *)
  (*   prerr_endline buf; (*register imperatively*) *)
      lex loc c s
  | [< '_ as x ; s >] -> Buffer.add_char literatebuf x; literatecomment loc c s
and comment loc c = parser
  | [< '( '\n' ); s >] -> lex (succ_line loc) c s
  | [< '_ ; s >] -> comment loc c s
and comment2 loc lvl c = parser
  | [< ?= [ '*'; '/' ]; '( '*' ); '( '/'); s >] ->
      if lvl = 0 then lex loc c s else comment2 loc (lvl-1) c s
  | [< ?= [ '/'; '*' ]; '( '/' ); '( '*' ); s >] -> comment2 loc (lvl+1) c s
  | [< '_ ; s >] -> comment2 loc lvl c s


open Plexing

(* For some reason, the [Ploc.after] function of Camlp5 does not update line
   numbers, so we define our own function that does it. *)
let after loc =
  let line_nb = Ploc.line_nb_last loc in
  let bol_pos = Ploc.bol_pos_last loc in
  Ploc.make_loc (Ploc.file_name loc) line_nb bol_pos
                (Ploc.last_pos loc, Ploc.last_pos loc) (Ploc.comment loc)

let lex_fun s =
  let tab = Hashtbl.create 207 in
  (Stream.from (fun id ->
     let tok, loc = lex !last_loc Lexbuf.empty s in
     last_loc := after loc;
     Hashtbl.add tab id loc;
     Some tok)),
  (fun id -> try Hashtbl.find tab id with Not_found -> !last_loc)
;;

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

let used_precedences = ref [110];;
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

let desugar_multi_binder = function
  | App(Const hd as binder,args)
    when Func.(equal hd pif || equal hd sigmaf) && List.length args > 1 ->
      let last, rev_rest = let l = List.rev args in List.hd l, List.tl l in
      let names = List.map (function
        | Const x -> Func.show x
        | _ -> Elpi_util.error "multi binder syntax") rev_rest in
      let body = mkApp [binder;last] in
      List.fold_left (fun bo name -> mkApp [binder;mkLam name bo]) body names
  | t -> t
;;

let desugar_macro = function
  | App(Const hd,[Const name; body]) when Func.(equal hd rimplf) ->
      if ((Func.show name).[0] != '@') then
        raise (Stream.Error "Macro name must begin with @");
      name, body
  | App(Const hd,[App(Const name,args); body]) when Func.(equal hd rimplf) ->
      if ((Func.show name).[0] != '@') then
        raise (Stream.Error "Macro name must begin with @");
      let names = List.map (function
        | Const x -> Func.show x
        | _ -> Elpi_util.error "macro binder syntax") args in
      name, List.fold_right mkLam names body
  | _ -> raise (Stream.Error "Illformed macro")
;;

EXTEND
  GLOBAL: lp goal;
  lp: [ [ cl = LIST0 clause; EOF -> List.concat cl ] ];
  const_sym:
    [[ c = CONSTANT -> c
     | s = SYMBOL -> s
     | e = ESCAPE -> e ]];
  filename:
    [[ c = CONSTANT -> c
     | c = LITERAL -> c ]];
  i_o : [[ CONSTANT "i" -> true | CONSTANT "o" -> false ]];
  mode :
    [[ LPAREN; c = CONSTANT;
       l = LIST1 i_o; RPAREN;
       alias = OPT[ CONSTANT "xas"; c = CONSTANT;
                 subst = OPT [ LPAREN;
                               l = LIST1 [ c1 = CONSTANT; ARROW;
                                       c2 = CONSTANT ->
                                (Func.from_string c1, Func.from_string c2) ]
                 SEP SYMBOL ","; RPAREN -> l ] ->
                 Func.from_string c,
                 match subst with None -> [] | Some l -> l ] ->
      Func.from_string c,l,alias]];
  chrrule :
    [[ to_match = LIST0 sequent;
       to_remove = OPT [ BIND; l = LIST1 sequent -> l ];
       alignement = OPT [ a =
         [ SYMBOL ">"; hd = CONSTANT; a =
             [ SYMBOL "="; l = LIST1 CONSTANT SEP SYMBOL "=" -> (l,`Spread)
             | SYMBOL "~"; l = LIST1 CONSTANT SEP SYMBOL "~" -> (l,`Align) ]
          -> hd :: fst a, snd a ] -> a];
       guard = OPT [ PIPE; a = atom LEVEL "abstterm" -> a ];
       new_goal = OPT [ SYMBOL "<=>"; g = atom -> g ] ->
         let to_remove = match to_remove with None -> [] | Some l -> l in
         let alignement =
           match alignement with
           | None -> None
           | Some (alignement,x) ->
               Some (List.map Func.from_string alignement,x) in
         create_chr ~to_match ~to_remove ?alignement ?guard ?new_goal ()
    ]];
  sequent :
    [[ LPAREN; t1 = atom; RPAREN ->
         match t1 with
         | App(Const x,[a;b]) when Func.equal x Func.sequentf -> a, b
         | _ -> mkFreshUVar (), t1
    ]];
  clname : [[ COLON; CONSTANT "name";
              name = [ c = CONSTANT -> c | l = LITERAL -> l] -> name ]];
  clinsert :
     [[ COLON; CONSTANT "before";
              name = [ c = CONSTANT -> c | l = LITERAL -> l] -> `Before, name
      | COLON; CONSTANT "after";
              name = [ c = CONSTANT -> c | l = LITERAL -> l] -> `After, name
    ]];
  pragma : [[ CONSTANT "#line"; l = INTEGER; f = LITERAL ->
    set_fname ~line:(int_of_string l) f ]];
  pred_item : [[ m = i_o; COLON; t = ctype -> (m,t) ]];
  pred : [[ c = const_sym; a = LIST0 pred_item SEP SYMBOL "," ->
    let name = Func.from_string c in
     [name, List.map fst a, None],
     (name, List.fold_right (fun (_,t) ty ->
        mkApp [mkCon "->";t;ty]) a (mkCon "prop"))
  ]];
  clause :
    [[ id = OPT clname; insert = OPT clinsert; f = atom; FULLSTOP ->
       let c = { loc; id; insert; body = f } in
       (!PointerFunc.latex_export).PointerFunc.export c ;
       [Clause c]
     | pragma -> []
     | LCURLY -> [Begin]
     | RCURLY -> [End]
     | PRED; p = pred; FULLSTOP ->
         let m, (n,t) = p in [Type(false,n,t); Mode m]
     | TYPE; names = LIST1 const_sym SEP SYMBOL ","; t = type_; FULLSTOP ->
         List.map (fun n -> Type(false,Func.from_string n,t)) names
     | EXTERNAL; TYPE; names = LIST1 const_sym SEP SYMBOL ","; t = type_; FULLSTOP ->
         List.map (fun n -> Type(true,Func.from_string n,t)) names
     | EXTERNAL; PRED; p = pred; FULLSTOP ->
         let _, (n,t) = p in [Type(true,n,t)] (* No mode for ML code *)
     | MODE; m = LIST1 mode SEP SYMBOL ","; FULLSTOP -> [Mode m]
     | MACRO; b = atom; FULLSTOP ->
         let name, body = desugar_macro b in
         [Macro(loc,name, body)]
     | RULE; r = chrrule; FULLSTOP -> [Chr r]
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
     | KIND; names = LIST1 const_sym SEP SYMBOL ","; t = kind; FULLSTOP ->
         List.map (fun n -> Type(false,Func.from_string n,t)) names
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
    [[ t = TYPE -> mkCon t
     | t = TYPE; a = ARROW; k = kind -> mkApp [mkCon a; mkCon t; k]
    ]];
  type_:
    [[ c = ctype -> c
     | s = ctype; a = ARROW; t = type_ -> mkApp [mkCon a; s; t]
    ]];
  ctype:
     [ "main" [ c = CONSTANT; l = LIST0 ctype LEVEL "arg" -> mkApp (mkCon c :: l)
              | CONSTANT "ctype"; s = LITERAL -> mkApp [Const Func.ctypef; mkString s] ]
     | "arg"  [ c = CONSTANT -> mkCon c
              | LPAREN; t = type_; RPAREN -> t ]
     ];
  abbrform:
    [[ CONSTANT -> ()
     | LPAREN; CONSTANT; LIST1 CONSTANT; RPAREN -> ()
     | LPAREN; abbrform; RPAREN -> ()
    ]];
  goal:
    [[ OPT pragma; p = premise -> loc, p ]];
  premise : [[ a = atom -> a ]];
  atom :
   [ "110"
      [ args = LIST1 atom LEVEL "120" SEP SYMBOL "," ->
          if List.length args > 1 then mkApp (Const Func.andf :: args)
          else List.hd args
      ]
   | "term"
      [ hd = atom; args = LIST1 atom LEVEL "abstterm" ->
         desugar_multi_binder (mkApp (hd :: args)) ]
   | "abstterm"
      [ c=CONSTANT; OPT[COLON;type_]; b=OPT[BIND; a = atom LEVEL "0" -> a ] ->
          (match b with None -> mkCon c | Some b -> mkLam c b)
      | c = ARROW; a = atom LEVEL "abstterm" -> mkApp [mkCon c; a]
      | u=FRESHUV; OPT[COLON;type_]; b=OPT[BIND; a = atom LEVEL "0" -> a ] ->
          (match b with None -> mkFreshUVar () | Some b ->
           mkLam Func.(show dummyname)  b)
      | s = LITERAL -> mkString s
      | s = QUOTED -> mkQuoted s
      | s = INTEGER -> mkInt (int_of_string s) 
      | s = FLOAT -> mkFloat (float_of_string s) 
      | LPAREN; a = atom; RPAREN -> a
      | LCURLY; a = atom; RCURLY -> mkApp [Const Func.spillf;a]
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
          else mkSeq (xs@[tl]) ]
   | "wtf" 
      [ s = ESCAPE -> mkCon s ]
      ];
END

(* 120 is the first level after 110, which is that of , *)
let list_element_prec = 120

let parser_initialized = ref false

let init ?(silent=true) ~paths ~cwd =
  assert(!parser_initialized = false);
  parse_silent := silent;
  parsed := [];
  set_tjpath cwd paths;
  assert(parse lp ["pervasives-syntax.elpi"] = []);
  parser_initialized := true
;;

let parse_program ?(no_pervasives=false) filenames : program =
  assert(!parser_initialized = true);
  let pervasives = if no_pervasives then [] else ["pervasives.elpi"] in
  parse lp (pervasives @ filenames)
;;

let parse_goal s : goal =
  assert(!parser_initialized = true);
  parse_string goal s

let parse_goal_from_stream strm =
  assert(!parser_initialized = true);
  try Grammar.Entry.parse goal strm
  with
    Ploc.Exc(l,(Token.Error msg | Stream.Error msg)) -> raise(Stream.Error msg)
  | Ploc.Exc(_,e) -> raise e


