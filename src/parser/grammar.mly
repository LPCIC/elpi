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

open TypeExpression

let loc (startpos, endpos) = {
  Util.Loc.client_payload = C.get_current_client_loc_payload ();
  source_name = startpos.Lexing.pos_fname;
  source_start = startpos.Lexing.pos_cnum;
  source_stop = endpos.Lexing.pos_cnum;
  line = startpos.Lexing.pos_lnum;
  line_starts_at = startpos.Lexing.pos_bol;
}

let desugar_multi_binder loc (t : Ast.Term.t) =
  match t.it with
  | App( { it = Const hd } as binder,args)
    when Func.equal hd Func.pif || Func.equal hd Func.sigmaf && List.length args > 1 ->
      let last, rev_rest = let l = List.rev args in List.hd l, List.tl l in
      let ty = match last.it with
        | Lam (_,ty,_) -> ty
        | Const x when Func.is_uvar_name x -> None
        | _ -> raise (ParseError(loc,"The last argument of 'pi' or 'sigma' must be a function or a unification variable, while it is: " ^ Ast.Term.show last)) in
      let names = List.map (function
        | { it = Const x; loc } -> Func.show x, loc
        | { it = (App _ | Lam _ | CData _ | Quoted _ | Cast _ | Parens _) } ->
            raise (ParseError(loc,"Only names are allowed after 'pi' or 'sigma'"))) rev_rest in
      let body = mkApp (Loc.merge binder.loc last.loc) [binder;last] in
      List.fold_left (fun bo (name,nloc) ->
        let loc = Loc.merge nloc bo.loc in
        mkApp loc [binder;mkLam loc name ty bo]) body names
  | (App _ | Const _ | Lam _ | CData _ | Quoted _ | Cast _ | Parens _) -> t
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
        | { it = (App _ | Lam _ | CData _ | Quoted _ | Cast _ | Parens _) } ->
              raise (ParseError(loc,"Macro parameters must be names"))) args in
      name, List.fold_right (fun (name,nloc) b -> mkLam (Loc.merge nloc b.loc) name None b) names body
  | _ ->
        raise (ParseError(loc,"Illformed macro left hand side"))
;;

let mkParens_if_impl_or_conj loc t =
  match t.it with
  | App({ it = Const c},_) when Func.(equal c implf) -> mkParens loc t
  | App({ it = Const c},_) when Func.(equal c andf) -> mkParens loc t
  | _ -> t

let mkApp loc = function
  | { it = Const c; loc = cloc } :: a :: { it = App ({ it = Const c1 }, args) } :: [] when Func.(equal c andf && equal c1 andf) ->
      mkAppF loc (cloc,c) (a :: args)
  | l -> mkApp loc l

let rec unparen = function
  | [] -> []
  | { it = Parens { it = App ({ it = Const c1 }, args) } } as x :: xs when Func.(equal c1 implf) -> x :: unparen xs
  | { it = Parens x} :: xs -> x :: unparen xs
  | x :: xs -> x :: unparen xs

let mkAppF loc (cloc,c) l =
  if Func.(equal c implf) then
    match l with
    | { it = App ({ it = Const j; loc = jloc }, args) } :: rhs when Func.(equal j andf) ->
       begin match List.rev args with
       | last :: ( { loc = dloc } :: _ as rest_rev) ->
           let jloc = List.fold_left (fun x { loc } -> Loc.merge x loc) dloc rest_rev in
           let iloc = List.fold_left (fun x { loc } -> Loc.merge x loc) last.loc rhs in
           { it = App ({ it = Const j; loc = jloc },List.rev rest_rev @ [mkAppF iloc (cloc,c) (last :: rhs)]); loc = loc }
       | _ -> mkAppF loc (cloc,c) l
       end
    | _ -> mkAppF loc (cloc,c) (unparen l)
  else mkAppF loc (cloc,c) l

let binder l (loc,ty,b) =
  match List.rev l with
  | (name, bloc) :: rest ->
      let lloc = Loc.merge bloc b.loc in
      List.rev_map (fun (n,l) -> mkConst l n) rest @ [mkLam lloc (Func.show name) ty b]
  | _ -> raise (ParseError(loc,"bind '\\' operator must follow a name"))

let binder1 l = function
  | None -> l
  | Some (loc,ty,b) ->
      match List.rev l with
      | { it = Const name; loc = bloc } :: rest ->
        let lloc = Loc.merge bloc b.loc in
        List.rev rest @ [mkLam lloc (Func.show name) ty b]
      | _ -> raise (ParseError(loc,"bind '\\' operator must follow a name"))

;;

let underscore loc = { loc; it = Const Func.dummyname }

let decode_sequent loc t =
  match t.it with
  | App({ it = Const c },[hyps;bo]) when c == Func.sequentf -> hyps, bo
  | _ -> underscore loc, t

let fix_church x = if Func.show x = "o" then Func.propf else x

let mode_of_IO io =
  if io = 'i' then Mode.Input
  else if io = 'o' then Mode.Output
  else assert false

%}

%on_error_reduce term

(* non terminals *)
%type < Program.t > program
%type < Goal.t > goal
%type < (sugar, raw_attribute list, unit) Clause.t > clause
%type < Term.t > term
%type < Program.decl > decl
%type < Func.t > infix_SYMB
%type < Func.t > prefix_SYMB
%type < Func.t > postfix_SYMB
%type < Func.t > constant
%type < 'a TypeExpression.t > type_term
%type < 'a TypeExpression.t > atype_term

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
| p = pred; FULLSTOP { Program.Pred p }
| t = type_; FULLSTOP { Program.Type t }
| t = kind; FULLSTOP { Program.Kind t }
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
    raise (ParseError(loc $loc,"local keyword is no longer supported"))  }
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
  name = constant; args = separated_list(option(CONJ),pred_item) {
   { Type.loc=loc $sloc; name; attributes; ty = { tloc = loc $loc; tit = TPred ([], args) } }
 }
| attributes = attributes; FUNC;
  name = constant; in_args = separated_list(CONJ,fotype_term); ARROW; out_args = separated_list(CONJ,fotype_term) {
    let args = List.map (fun x -> Mode.Input,x) in_args @ List.map (fun x -> Mode.Output,x) out_args in
    { Type.loc=loc $sloc; name; attributes; ty = { tloc = loc $loc; tit = TPred ([Functional], args) } }
  }
| attributes = attributes; FUNC;
  name = constant; in_args = separated_list(CONJ,fotype_term) {
  let args = List.map (fun x -> Mode.Input,x) in_args in
  { Type.loc=loc $sloc; name; attributes; ty = { tloc = loc $loc; tit = TPred ([Functional], args) } }
}

pred_item:
| io = IO_COLON; ty = type_term { (mode_of_IO io,ty) }

anonymous_pred:
| PRED; args = separated_list(option(CONJ),pred_item) { { tloc = loc $loc; tit = TPred ([], args) } }
| FUNC; in_args = separated_list(CONJ,fotype_term); ARROW; out_args = separated_list(CONJ,fotype_term) {
    let args = List.map (fun x -> Mode.Input,x) in_args @ List.map (fun x -> Mode.Output,x) out_args in
    { tloc = loc $loc; tit = TPred ([Functional], args) }
  }
| FUNC; in_args = separated_list(CONJ,fotype_term) {
    let args = List.map (fun x -> Mode.Input,x) in_args in
    { tloc = loc $loc; tit = TPred ([Functional], args) }
  }

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
| c = constant { { tloc = loc $loc; tit = TConst (fix_church c) } }
| LPAREN; t = type_term; RPAREN { t }
| LPAREN; t = anonymous_pred; RPAREN { t }
fotype_term:
| c = constant { { tloc = loc $loc; tit = TConst (fix_church c) } }
| hd = constant; args = nonempty_list(atype_term) { { tloc = loc $loc; tit = TApp (hd, List.hd args, List.tl args) } }
| LPAREN; t = anonymous_pred; RPAREN { t }
| LPAREN; t = type_term; RPAREN { t }
type_term:
| fo = fotype_term { fo }
| hd = fotype_term; ARROW; t = type_term { { tloc = loc $loc; tit = TArr (hd, t) } }

kind_term:
| TYPE { { tloc = loc $loc; tit = TConst (Func.from_string "type") } }
| x = TYPE; ARROW; t = kind_term { { tloc = loc $loc; tit = TArr ({ tloc = loc $loc(x); tit = TConst (Func.from_string "type") }, t) } }

macro:
| MACRO; m = term; VDASH; b = term {
  let name, body = desugar_macro (loc $sloc) m b in
  { Macro.loc = loc $sloc; name; body }
}

typeabbrev:
| TYPEABBREV; a = abbrevform; t = type_term {
    let name, args = a in
    let nparams = List.length args in
    let mkLam (n,l) body =  TypeAbbreviation.Lam (n, l, body) in
    let value = List.fold_right mkLam args (Ty t) in
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
| LPAREN; c = closed_term; RTRI; t = term; RPAREN {
    let context, conclusion = decode_sequent (loc $loc) t in
    { Chr.eigen = c; context; conclusion }
  }

goal:
| g = term; EOF { g }
| g = term; FULLSTOP { g }

clause:
| attributes = attributes; body = clause_hd_term; {
    { Clause.loc = loc $sloc;
      attributes;
      body = Logic body;
      needs_spilling = ();
    }
  }
| attributes = attributes; l = clause_hd_term; v = VDASH; r = term { 
    { Clause.loc = loc $sloc;
      attributes;
      body = Logic (mkApp (loc $sloc) [mkConst (loc $loc(v)) Func.rimplf;l;r]);
      needs_spilling = ();
    }
}
| attributes = attributes; l = clause_hd_term; v = EQ; r = expr { 
    { Clause.loc = loc $sloc;
      attributes;
      body = Function (FunctionalTerm.of_term l,r);
      needs_spilling = ();
    }
}

expr:
| LET; p = closed_term; EQ; e = expr; IN; k = expr { FunctionalTerm.mkLet (loc $sloc) (FunctionalTerm.of_term p) e k }
| USE; l = clause_hd_term; EQ; e = expr; IN; k = expr { FunctionalTerm.mkUse (loc $sloc) (FunctionalTerm.of_term l) e k }
| FRESH; x = constant; IN; k = expr { FunctionalTerm.mkFresh (loc $sloc) (Func.show x) None k } 
| t = open_term_noconj { FunctionalTerm.of_term t }
| t = binder_term_noconj { FunctionalTerm.of_term t }
| t = closed_term { FunctionalTerm.of_term t }

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
| UNTYPED { Untyped }
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
| LBRACKET; l = list_items { mkSeq ~loc:(loc $loc) l }
| LBRACKET; l = list_items_tail;  {  mkSeq ~loc:(loc $loc) l }
| l = LCURLY; t = term; RCURLY { mkAppF (loc $loc) (loc $loc(l),Func.spillf) [t] }
| t = head_term { t }

head_term:
| t = constant { mkConst (loc $loc) t }
| LPAREN; t = term; RPAREN { mkParens_if_impl_or_conj (loc $loc) t }
| LPAREN; t = term; COLON; ty = type_term RPAREN { mkCast (loc $loc) t ty }

list_items:
| RBRACKET { [mkNil (loc $loc)] }
| x = term_noconj; r = RBRACKET { [x;mkNil (loc $loc(r))] }
| x = term_noconj; CONJ; xs = list_items { x :: xs }

list_items_tail:
| PIPE; x = term_noconj; RBRACKET { [x] }
| x = term_noconj; PIPE; xs = term_noconj; RBRACKET { [x;xs] }
| x = term_noconj; CONJ; xs = list_items_tail { x :: xs }

binder_term:
| t = constant; BIND; b = term { mkLam (loc $loc) (Func.show t) None b }
// | t = constant; COLON; ty = type_term; BIND; b = term { mkLam (loc $loc) (Func.show t) (Some ty) b }

binder_body_no_ty:
| bind = BIND; b = term { (loc $loc(bind), None, b) }

binder_body:
| bind = BIND; b = term { (loc $loc(bind), None, b) }
| COLON; ty = type_term; bind = BIND; b = term { (loc $loc(bind), Some ty, b) }

binder_term_noconj:
| t = constant; BIND; b = term { mkLam (loc $loc) (Func.show t) None b }
| t = constant; COLON; ty = type_term; BIND; b = term { mkLam (loc $loc) (Func.show t) (Some ty) b }

open_term:
| hd = PI; args = nonempty_list(constant_w_loc); b = binder_body { desugar_multi_binder (loc $loc) @@ mkApp (loc $loc) (mkConst (loc $loc(hd)) (Func.from_string "pi") :: binder args b) }
| hd = SIGMA; args = nonempty_list(constant_w_loc); b = binder_body { desugar_multi_binder (loc $loc) @@ mkApp (loc $loc) (mkConst (loc $loc(hd)) (Func.from_string "sigma") :: binder args b) }
| hd = head_term; args = nonempty_list(closed_term) ; b = option(binder_body_no_ty) {
    let args = binder1 args b in
    let t = mkApp (loc $loc) (hd :: args) in
    t
} (*%prec OR*)
| l = term; s = infix;  r = term { mkAppF (loc $loc) (loc $loc(s),s) [l;r] }
| s = prefix; r = term { mkAppF (loc $loc) (loc $loc(s),s) [r] }
| l = term; s = postfix; { mkAppF (loc $loc) (loc $loc(s),s) [l] }

open_term_noconj:
| hd = PI; args = nonempty_list(constant_w_loc); b = binder_body { desugar_multi_binder (loc $loc) @@ mkApp (loc $loc) (mkConst (loc $loc(hd)) (Func.from_string "pi") :: binder args b) }
| hd = SIGMA; args = nonempty_list(constant_w_loc); b = binder_body { desugar_multi_binder (loc $loc) @@ mkApp (loc $loc) (mkConst (loc $loc(hd)) (Func.from_string "sigma") :: binder args b) }
| hd = head_term; args = nonempty_list(closed_term); b = option(binder_body_no_ty) {
    let args = binder1 args b in
    let t = mkApp (loc $loc) (hd :: args) in
    t
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
| LPAREN; t = term; RPAREN { mkParens_if_impl_or_conj (loc $loc) t }

clause_hd_open_term:
| hd = PI; args = nonempty_list(constant_w_loc); b = binder_body { desugar_multi_binder (loc $loc) @@ mkApp (loc $loc) (mkConst (loc $loc(hd)) (Func.from_string "pi") :: binder args b) }
| hd = SIGMA; args = nonempty_list(constant_w_loc); b = binder_body { desugar_multi_binder (loc $loc) @@ mkApp (loc $loc) (mkConst (loc $loc(hd)) (Func.from_string "sigma") :: binder args b) }
| hd = head_term; args = nonempty_list(closed_term); b = option(binder_body_no_ty) {
    let args = binder1 args b in
    let t = mkApp (loc $loc) (hd :: args) in
    t
} (*%prec OR*)
| l = clause_hd_term; s = infix_noconj_novdash_noeq; r = term { mkAppF (loc $loc) (loc $loc(s),s) [l;r] }
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
| FUNCTIONAL { Func.from_string "functional" }
| UNTYPED { Func.from_string "untyped" }
| c = IO { Func.from_string @@ String.make 1 c }
| CUT { Func.cutf }
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
| PI { Func.from_string "pi" }
| SIGMA { Func.from_string "sigma" }

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

// %inline infix_novdash:
// | x = extensible_infix { x }
// | x = non_extensible_infix_novdash { x }

%inline infix_noconj_novdash_noeq:
| x = extensible_infix { x }
| x = non_extensible_infix_novdash_noconj_noeq { x }

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

%inline non_extensible_infix_novdash_noconj_noeq:
| CONS   { Func.consf }
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
| DDARROW { Func.implf }
| QDASH  { Func.sequentf }
| SLASH  { Func.from_string "/" }
| CONJ2  { Func.andf }

%inline non_extensible_infix_novdash_noconj:
| x = non_extensible_infix_novdash_noconj_noeq { x }
| EQ     { Func.eqf }

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
