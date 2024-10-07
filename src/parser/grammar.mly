(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

%parameter < C : Parser_config.ParseFile >

%{
open Elpi_util
open Elpi_lexer_config

open Lexer_config
open Parser_config
open Ast
open Term


let loc (startpos, endpos) = {
  Util.Loc.source_name = startpos.Lexing.pos_fname;
  source_start = startpos.Lexing.pos_cnum;
  source_stop = endpos.Lexing.pos_cnum;
  line = startpos.Lexing.pos_lnum;
  line_starts_at = startpos.Lexing.pos_bol;
}

let desugar_multi_binder loc t =
  match t.it with
  | App( { it = Const hd } as binder,args)
    when Func.equal hd Func.pif || Func.equal hd Func.sigmaf && List.length args > 1 ->
      let last, rev_rest = let l = List.rev args in List.hd l, List.tl l in
      let () = match last.it with
        | Lam _ -> ()
        | Const x when Func.is_uvar_name x -> ()
        | _ -> raise (ParseError(loc,"The last argument of 'pi' or 'sigma' must be a function or a unification variable, while it is: " ^ Ast.Term.show last)) in
      let names = List.map (function
        | { it = Const x; loc } -> Func.show x, loc
        | { it = (App _ | Lam _ | CData _ | Quoted _) } ->
            raise (ParseError(loc,"Only names are allowed after 'pi' or 'sigma'"))) rev_rest in
      let body = mkApp (Loc.merge binder.loc last.loc) [binder;last] in
      List.fold_left (fun bo (name,nloc) ->
        let loc = Loc.merge nloc bo.loc in
        mkApp loc [binder;mkLam loc name bo]) body names
  | (App _ | Const _ | Lam _ | CData _ | Quoted _) -> t
;;

let desugar_macro loc lhs rhs =
  match lhs, rhs with
  | { it = Const name }, body ->
      if ((Func.show name).[0] != '@') then
        raise (ParseError(loc,"Macro name must begin with '@'"));
      name, body
  | { it = App({ it = Const name },args) }, body ->
      if ((Func.show name).[0] != '@') then
        raise (ParseError(loc,"Macro name must begin with '@'"));
      let names = List.map (function
        | { it = Const x; loc } -> Func.show x, loc
        | { it = (App _ | Lam _ | CData _ | Quoted _) } ->
              raise (ParseError(loc,"Macro parameters must be names"))) args in
      name, List.fold_right (fun (name,nloc) b -> mkLam (Loc.merge nloc b.loc) name b) names body
  | _ ->
        raise (ParseError(loc,"Illformed macro left hand side"))
;;

let mkApp loc = function
  | { it = Const c; loc = cloc } :: a :: { it = App ({ it = Const c1 }, args) } :: [] when Func.(equal c andf && equal c1 andf) ->
      mkAppF loc (cloc,c) (a :: args)
  | l -> mkApp loc l

let mkAppF loc (cloc,c) = function
  | a :: { it = App ({ it = Const c1 }, args) } :: [] when Func.(equal c andf && equal c1 andf) ->
      mkAppF loc (cloc,c) (a :: args)
  | l -> mkAppF loc (cloc,c) l

let binder l = function
  | None -> l
  | Some (loc,b) ->
      match List.rev l with
      | { it = Const name; loc = bloc } :: rest ->
          let lloc = Loc.merge bloc b.loc in
          List.rev rest @ [mkLam lloc (Func.show name) b]
      | _ -> raise (ParseError(loc,"bind '\\' operator must follow a name"))
;;

let underscore loc = { loc; it = Const Func.dummyname }

let decode_sequent loc t =
  match t.it with
  | App({ it = Const c },[hyps;bo]) when c == Func.sequentf -> hyps, bo
  | _ -> underscore loc, t

let prop = Func.from_string "prop"

let fix_church x = if Func.show x = "o" then prop else x

let mode_of_IO io =
  if io = 'i' then true
  else if io = 'o' then false
  else assert false

%}

%on_error_reduce term

(* non terminals *)
%type < Program.t > program
%type < Goal.t > goal
%type < (Term.t, raw_attribute list) Clause.t > clause
%type < Term.t > term
%type < Program.decl > decl
%type < Func.t > infix_SYMB
%type < Func.t > prefix_SYMB
%type < Func.t > postfix_SYMB
%type < Func.t > constant

(* entry points *)
%start program
%start goal

(* for testing *)
%start infix_SYMB
%start prefix_SYMB
%start postfix_SYMB

(* token precedence are in token_precedence.mly *)

%%
program:
| EOF { [] }
| d = decl; p = program { d :: p }

decl:
| c = clause; FULLSTOP { Program.Clause c }
| r = chr_rule; FULLSTOP { Program.Chr r }
| p = pred; FULLSTOP { Program.Pred (snd p, fst p) }
| t = type_; FULLSTOP { Program.Type t }
| t = kind; FULLSTOP { Program.Type t }
| m = mode; FULLSTOP { Program.Mode [m] }
| m = macro; FULLSTOP { Program.Macro m }
| CONSTRAINT; hyps = list(constant); QDASH; cl = list(constant); LCURLY { Program.Constraint(loc $sloc, hyps, cl) }
| CONSTRAINT; cl = list(constant); LCURLY { Program.Constraint(loc $sloc, [], cl) }
| NAMESPACE; c = constant; LCURLY { Program.Namespace(loc $sloc, c )}
| SHORTEN; s = shorten; FULLSTOP { Program.Shorten(loc $sloc, s) }
| a = typeabbrev; FULLSTOP { Program.TypeAbbreviation a }
| LCURLY { Program.Begin (loc $sloc) }
| RCURLY { Program.End (loc $sloc) }
| ext = accumulate; l = separated_nonempty_list(CONJ,filename); FULLSTOP {
    Program.Accumulated(loc $sloc,List.(concat (map (fun x ->
      let cwd = Filename.dirname (loc $sloc).source_name in
      C.parse_file ~cwd (x ^ ext)) l)))
  }
| LOCAL; l = separated_nonempty_list(CONJ,constant); option(type_term); FULLSTOP {
    Program.Local l
  }
| ignored; FULLSTOP { Program.Ignored (loc $sloc) }
| f = fixity; FULLSTOP { error_mixfix (loc $loc) }

accumulate:
| ACCUMULATE { ".elpi" }
| IMPORT { ".mod" }
| ACCUM_SIG { ".sig" }
| USE_SIG { ".sig" }

filename:
| c = constant { Func.show c }
| s = STRING { s }

chr_rule:
| attributes = attributes; RULE;
  to_match = list(sequent);
  to_remove = preceded(BIND,nonempty_list(sequent))?;
  guard = preceded(PIPE,term)?;
  new_goal = preceded(IFF,sequent)? {
    { Chr.to_match; to_remove = Util.option_default [] to_remove; guard; new_goal; attributes; loc=(loc $loc) }
  }

pred:
| attributes = attributes; PRED;
  c = constant; args = separated_list(option(CONJ),pred_item) {
   let name = c in
   { Mode.loc=loc $sloc; name; args = List.map fst args },
   { Type.loc=loc $sloc; attributes; name;
     ty = List.fold_right (fun (_,t) ty ->
       mkApp (loc $loc(c)) [mkCon (t.loc)(* BUG *)"->";t;ty]) args (mkCon (loc $sloc) (* BUG *) "prop") }
 }
pred_item:
| io = IO_COLON; ty = type_term { (Mode.Fo (mode_of_IO io),ty) }

kind:
| KIND; names = separated_nonempty_list(CONJ,constant); k = kind_term {
    names |> List.map (fun n->
     { Type.loc=loc $sloc; attributes=[]; name =  n; ty = k })
  }
type_:
| attributes = attributes;
  TYPE; names = separated_nonempty_list(CONJ,constant); t = type_term {
    names |> List.map (fun n->
     { Type.loc=loc $sloc; attributes; name = n; ty = t })
  }

atype_term:
| c = STRING { mkC (loc $loc) (cstring.Util.CData.cin c) }
| c = constant { mkConst (loc $loc(c)) (fix_church c) }
| LPAREN; t = type_term; RPAREN { t }
type_term:
| c = constant { mkConst (loc $loc(c)) (fix_church c) }
| hd = constant; args = nonempty_list(atype_term) { mkAppF (loc $loc) (loc $loc(hd),hd) args }
| hd = type_term; a = ARROW; t = type_term { mkApp (loc $loc) [mkCon (loc $loc(a)) "->"; hd; t] }
| LPAREN; t = type_term; RPAREN { t }

kind_term:
| TYPE { mkCon (loc $loc) "type" }
| hd = TYPE; ARROW; t = kind_term { mkApp (loc $loc(hd)) [mkCon (loc $loc) "->"; mkCon (loc $loc) "type"; t] }

mode:
| MODE; LPAREN; c = constant; l = nonempty_list(i_o); RPAREN {
    { Mode.name = c; args = l; loc = loc $sloc } 
}
i_o:
| io = IO { Mode.Fo (mode_of_IO io) }

macro:
| MACRO; m = term; VDASH; b = term {
  let name, body = desugar_macro (loc $sloc) m b in
  { Macro.loc = loc $sloc; name; body }
}

typeabbrev:
| TYPEABBREV; a = abbrevform; t = type_term {
    let name, args = a in
    let nparams = List.length args in
    let value = List.fold_right (fun (n,loc) -> mkLam loc (Func.show n)) args t in
    { TypeAbbreviation.name = name;
      nparams = nparams;
      value = value;
      loc = loc $loc }
  }

abbrevform:
| c = constant { c, [] }
| LPAREN; hd = constant; args = nonempty_list(constant_w_loc); RPAREN { hd, args  }


ignored:
| MODULE; constant
| SIG; constant
| EXPORTDEF; separated_nonempty_list(CONJ,constant)
| EXPORTDEF; separated_nonempty_list(CONJ,constant); type_term
| LOCALKIND; separated_nonempty_list(CONJ,constant)
| USEONLY; separated_nonempty_list(CONJ,constant)
| USEONLY; separated_nonempty_list(CONJ,constant); type_term
| CLOSED; separated_nonempty_list(CONJ,constant)
  { Program.Ignored (loc $sloc) }

fixity:
| f = FIXITY; c = constant; i = INTEGER { (fixity_of_string f,c,i,loc $loc(c)) }
| f = FIXITY; c = mixfix_SYMB; i = INTEGER { (fixity_of_string f,c,i,loc $loc(c)) }

shorten:
| l = trie {
     List.map Func.(fun (x,y) -> from_string x, from_string y) l
  }

trie:
| c = constant; FULLSTOP; LCURLY; l = separated_nonempty_list(CONJ,subtrie); RCURLY {
    List.map (fun (p,x) -> Func.show c ^ "." ^ p, x) (List.flatten l)
}
subtrie:
| name = constant { [Func.show name, Func.show name] }
| prefix = constant; FULLSTOP; LCURLY; l = separated_nonempty_list(CONJ,subtrie); RCURLY {
    List.map (fun (p,x) -> Func.show prefix ^ "." ^ p, x) (List.flatten l)
}

sequent:
| t = closed_term {
    let context, conclusion = decode_sequent (loc $loc) t in
    { Chr.eigen = underscore (loc $loc); context; conclusion }
  }
| LPAREN; c = closed_term; COLON; t = term; RPAREN {
    let context, conclusion = decode_sequent (loc $loc) t in
    { Chr.eigen = c; context; conclusion }
  }

goal:
| g = term; EOF { ( loc $sloc , g ) }
| g = term; FULLSTOP { ( loc $sloc , g ) }

clause:
| attributes = attributes; body = clause_hd_term; {
    { Clause.loc = loc $sloc;
      attributes;
      body;
    }
  }
| attributes = attributes; l = clause_hd_term; v = VDASH; r = term { 
    { Clause.loc = loc $sloc;
      attributes;
      body = mkApp (loc $sloc) [mkConst (loc $loc(v)) Func.rimplf;l;r]
    }
}

attributes:
| { [] }
| EXTERNAL { [ External ] }
| COLON; l = separated_nonempty_list(COLON, attribute) { l }

attribute:
| IF; s = STRING { If s }
| NAME; s = STRING  { Name s }
| AFTER; s = STRING { After s }
| BEFORE; s = STRING { Before s }
| REPLACE; s = STRING { Replace s }
| REMOVE; s = STRING { Remove s }
| EXTERNAL { External }
| FUNCTIONAL { Functional }
| INDEX; LPAREN; l = nonempty_list(indexing) ; RPAREN; o = option(STRING) { Index (l,o) }

indexing:
| FRESHUV { 0 }
| i = INTEGER { i }

term:
| t = open_term { t }
| t = binder_term { t }
| t = closed_term { t }

term_noconj:
| t = open_term_noconj { t }
| t = binder_term_noconj { t }
| t = closed_term { t }

closed_term:
| x = INTEGER { mkC (loc $loc) (cint.Util.CData.cin x)}
| x = FLOAT { mkC (loc $loc) (cfloat.Util.CData.cin x)}
| x = STRING { mkC (loc $loc) (cstring.Util.CData.cin x)}
| x = QUOTED { mkQuoted (loc $loc) x }
| LPAREN; t = term; a = AS; c = term; RPAREN { mkApp (loc $loc) [mkCon (loc $loc(a)) "as";t;c] }
| LBRACKET; l = list_items { mkSeq (loc $loc) l }
| LBRACKET; l = list_items_tail;  {  mkSeq (loc $loc) l }
| l = LCURLY; t = term; RCURLY { mkAppF (loc $loc) (loc $loc(l),Func.spillf) [t] }
| t = head_term { t }

head_term:
| t = constant { mkConst (loc $loc) t }
| LPAREN; t = term; RPAREN { t }

list_items:
| RBRACKET { [mkNil (loc $loc)] }
| x = term_noconj; r = RBRACKET { [x;mkNil (loc $loc(r))] }
| x = term_noconj; CONJ; xs = list_items { x :: xs }

list_items_tail:
| PIPE; x = term_noconj; RBRACKET { [x] }
| x = term_noconj; PIPE; xs = term_noconj; RBRACKET { [x;xs] }
| x = term_noconj; CONJ; xs = list_items_tail { x :: xs }

binder_term:
| t = constant; b = binder_body { mkLam (loc $loc) (Func.show t) (snd b) }

binder_body:
| bind = BIND; b = term { (loc $loc(bind), b) }

binder_term_noconj:
| t = constant; BIND; b = term { mkLam (loc $loc) (Func.show t) b }

open_term:
| hd = head_term; args = nonempty_list(closed_term); b = option(binder_body) {
    let args = binder args b in
    let t = mkApp (loc $loc) (hd :: args) in
    desugar_multi_binder (loc $loc(hd)) t
} (*%prec OR*)
| l = term; s = infix;  r = term { mkAppF (loc $loc) (loc $loc(s),s) [l;r] }
| s = prefix; r = term { mkAppF (loc $loc) (loc $loc(s),s) [r] }
| l = term; s = postfix; { mkAppF (loc $loc) (loc $loc(s),s) [l] }

open_term_noconj:
| hd = head_term; args = nonempty_list(closed_term); b = option(binder_body) {
    let args = binder args b in
    let t = mkApp (loc $loc) (hd :: args) in
    desugar_multi_binder (loc $loc(hd)) t
} (*%prec OR*)
| l = term_noconj; s = infix_noconj;  r = term_noconj { mkAppF (loc $loc) (loc $loc(s),s) [l;r] }
| s = prefix; r = term_noconj { mkAppF (loc $loc) (loc $loc(s),s) [r] }
| l = term_noconj; s = postfix; { mkAppF (loc $loc) (loc $loc(s),s) [l] }

(* avoids the conflict between `{` (Program.Begin) and `{spilled}` (Program.Clause) *)
clause_hd_term:
| t = clause_hd_open_term { t }
| t = clause_hd_closed_term { t }

clause_hd_closed_term:
| t = constant { mkConst (loc $sloc) t }
| LPAREN; t = term; RPAREN { t }

clause_hd_open_term:
| hd = head_term; args = nonempty_list(closed_term); b = option(binder_body) {
    let args = binder args b in
    let t = mkApp (loc $loc) (hd :: args) in
    desugar_multi_binder (loc $loc(hd)) t
} (*%prec OR*)
| l = clause_hd_term; s = infix_novdash; r = term { mkAppF (loc $loc) (loc $loc(s),s) [l;r] }
| s = prefix; r = term { mkAppF (loc $loc) (loc $loc(s),s) [r] }
| l = clause_hd_term; s = postfix; { mkAppF (loc $loc) (loc $loc(s),s) [l] }

constant:
| c = CONSTANT {
    if c = "nil" then Func.nilf
    else if c = "cons" then Func.consf
    else Func.from_string c }
| IF { Func.from_string "if" }
| NAME { Func.from_string "name" }
| BEFORE { Func.from_string "before" }
| AFTER { Func.from_string "after" }
| REPLACE { Func.from_string "replace" }
| REMOVE { Func.from_string "remove" }
| INDEX { Func.from_string "index" }
| c = IO { Func.from_string @@ String.make 1 c }
| CUT { Func.cutf }
| PI { Func.pif }
| SIGMA { Func.sigmaf }
| FRESHUV { Func.dummyname }
| LPAREN; s = mixfix_SYMB; RPAREN { s }
| LPAREN; AS; RPAREN  { Func.from_string "as" }
| NIL { Func.nilf }

constant_w_loc:
| c = constant { c, loc $loc }

mixfix_SYMB:
| x = infix { x }
| x = prefix { x }
| x = postfix { x }

infix_SYMB:
| x = infix { x }

prefix_SYMB:
| x = prefix { x }

postfix_SYMB:
| x = postfix { x }

%inline prefix:
| x = extensible_prefix { x }

%inline postfix:
| x = extensible_postfix { x }

%inline infix:
| x = extensible_infix { x }
| x = non_extensible_infix { x }

%inline infix_noconj:
| x = extensible_infix { x }
| x = non_extensible_infix_noconj { x }

%inline infix_novdash:
| x = extensible_infix { x }
| x = non_extensible_infix_novdash { x }

%inline extensible_infix:
| s = FAMILY_PLUS  { Func.from_string s }
| s = FAMILY_TIMES { Func.from_string s }
| s = FAMILY_MINUS { Func.from_string s }
| s = FAMILY_EXP   { Func.from_string s }
| s = FAMILY_LT    { Func.from_string s }
| s = FAMILY_GT    { Func.from_string s }
| s = FAMILY_EQ    { Func.from_string s }
| s = FAMILY_AND   { Func.from_string s }
| s = FAMILY_OR   { Func.from_string s }
| s = FAMILY_SHARP { Func.from_string s }
| s = FAMILY_BTICK { Func.from_string s }
| s = FAMILY_TICK  { Func.from_string s }

%inline non_extensible_infix_novdash_noconj:
| CONS   { Func.consf }
| EQ     { Func.eqf }
| MINUS  { Func.from_string "-" }
| MINUSr { Func.from_string "r-" }
| MINUSi { Func.from_string "i-" }
| MINUSs { Func.from_string "s-" }
| EQ2    { Func.from_string "==" }
| OR     { Func.orf }
| IS     { Func.isf }
| MOD    { Func.from_string "mod" }
| DIV    { Func.from_string "div" }
| ARROW  { Func.arrowf }
| DARROW { Func.implf }
| QDASH  { Func.sequentf }
| SLASH  { Func.from_string "/" }
| CONJ2  { Func.andf }

%inline non_extensible_infix_novdash:
| x = non_extensible_infix_novdash_noconj { x }
| CONJ   { Func.andf }

%inline non_extensible_infix_noconj:
| x = non_extensible_infix_novdash_noconj { x }
| VDASH  { Func.rimplf }

%inline non_extensible_infix:
| x = non_extensible_infix_novdash { x }
| VDASH  { Func.rimplf }

%inline extensible_prefix:
| s = FAMILY_TILDE { Func.from_string s }

%inline extensible_postfix:
| s = FAMILY_QMARK { Func.from_string s }
