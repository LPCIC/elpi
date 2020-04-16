let parsetree_declaration = ref []
let parsetree_mapper = ref []
open Ppxlib_ast.Import_for_core

let elpi_loc_of_location loc =
  let open Location in
  let open Lexing in
  {
    Elpi.API.Ast.Loc.source_name = loc.loc_end.pos_fname;
    source_start = loc.loc_end.pos_cnum;
    source_stop = loc.loc_end.pos_cnum;
    line = loc.loc_end.pos_lnum;
    line_starts_at = loc.loc_end.pos_bol;
  }

let dummy_position =
  let open Lexing in
  {
    pos_fname = "$elpi";
    pos_lnum  = 0;
    pos_bol   = 0;
    pos_cnum = 0;
  }

let dummy_location =
  let open Location in
  {
    loc_start = dummy_position;
    loc_end = dummy_position;
    loc_ghost = false
  }

let maybe_override_embed default = fun ~depth h c st e ->
  let open Parsetree in
  match e with
  | ({ Location.txt = ("e"|"p"|"t"|"m"|"i"); _ }, PStr [{ pstr_desc = Pstr_eval ({ pexp_desc = Parsetree.Pexp_constant (Pconst_string(s,_)); pexp_loc = loc; _ },[]) ; _}]) ->
      let loc = elpi_loc_of_location loc in
      let st, x = Elpi.API.Quotation.lp ~depth st loc s in
      st, x, []
  | e -> default ~depth h c st e

let maybe_override_embed2 default = fun ~depth h c st e a ->
  let open Parsetree in
  match e with
  | ({ Location.txt = ("e"|"p"|"t"|"m"|"i"); _ }, PStr [{ pstr_desc = Pstr_eval ({ pexp_desc = Parsetree.Pexp_constant (Pconst_string(s,_)); pexp_loc = loc; _ },[]) ; _}]) ->
      let loc = elpi_loc_of_location loc in
      let st, x = Elpi.API.Quotation.lp ~depth st loc s in
      st, x, []
  | _ -> default ~depth h c st e a

(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Definition of the OCaml AST *)


(* This file is obtained by:

   - copying a subset of the corresponding ast_xxx.ml file from migrate-parsetree
   (sub-modules Asttypes and Parsetree)
   - adding the type definitions for position, location, loc and longident
   - flattening all the modules
   - removing Asttypes.constant (unused and conflicts with Parsetree.constant)
   - renaming a few types:
   - - Location.t -> location
   - - Longident.t -> longident
   - adding a type longident_loc = longident loc and replacing all the occurences of the
   latter by the former. This is so that we can override iteration an the level of a
   longident loc
   - replacing all the (*IF_CURRENT = Foo.bar*) by: = Foo.bar
   - removing the extra values at the end of the file
   - replacing app [type ...] by [and ...] to make everything one recursive block
   - adding [@@deriving_inline traverse][@@@end] at the end
*)

(* Source code locations (ranges of positions), used in parsetree. *)

type position = Lexing.position =
  { pos_fname : string
  ; pos_lnum  : int
  ; pos_bol   : int
  ; pos_cnum  : int
  }

and location = Location.t = {
  loc_start: position;
  loc_end: position;
  loc_ghost: bool;
} [@@elpi.embed fun default ~depth h c st start end_ ghost ->
       if ghost = false && start = dummy_position && end_ = dummy_position then
         let st, v = Elpi.API.FlexibleData.Elpi.make st in
         st, Elpi.API.RawData.mkUnifVar v ~args: [] st, []
       else
         default ~depth h c st start end_ ghost ]
  [@@elpi.default_constructor_readback fun default ~depth h c st t ->
       match Elpi.API.RawData.look ~depth t with
       | Elpi.API.RawData.UnifVar _ -> st, dummy_location, []
       | _ -> default ~depth h c st t]

and location_stack = location list

(* Note on the use of Lexing.position in this module.
   If [pos_fname = ""], then use [!input_name] instead.
   If [pos_lnum = -1], then [pos_bol = 0]. Use [pos_cnum] and
   re-parse the file to get the line and character numbers.
   Else all fields are correct.

*)
and 'a loc = 'a Location.loc = {
  txt : 'a;
  loc : location;
}
[@@elpi.type_code "loc_"]

(* Long identifiers, used in parsetree. *)

and longident = Longident.t =
    Lident of string
  | Ldot of longident * string
  | Lapply of longident * longident

and longident_loc = longident loc

(** Auxiliary AST types used by parsetree and typedtree. *)

and rec_flag = Asttypes.rec_flag = Nonrecursive | Recursive

and direction_flag = Asttypes.direction_flag = Upto | Downto

(* Order matters, used in polymorphic comparison *)
and private_flag = Asttypes.private_flag = Private | Public

and mutable_flag = Asttypes.mutable_flag = Immutable | Mutable

and virtual_flag = Asttypes.virtual_flag = Virtual | Concrete

and override_flag = Asttypes.override_flag = Override | Fresh

and closed_flag = Asttypes.closed_flag = Closed [@elpi.code "closed_"] | Open [@elpi.code "open_"]

and label = string

and arg_label = Asttypes.arg_label =
    Nolabel
  | Labelled of string (*  label:T -> ... *)
  | Optional of string (* ?label:T -> ... *)

and variance = Asttypes.variance =
  | Covariant
  | Contravariant
  | Invariant

(** Abstract syntax tree produced by parsing *)

and constant = Parsetree.constant =
    Pconst_integer of string * char option
  (* 3 3l 3L 3n

     Suffixes [g-z][G-Z] are accepted by the parser.
     Suffixes except 'l', 'L' and 'n' are rejected by the typechecker
  *)
  | Pconst_char of char
  (* 'c' *)
  | Pconst_string of string * string option
  (* "constant"
     {delim|other constant|delim}
  *)
  | Pconst_float of string * char option
  (* 3.4 2e5 1.4e-4

     Suffixes [g-z][G-Z] are accepted by the parser.
     Suffixes are rejected by the typechecker.
  *)
[@@elpi.type_code "constant_"] (* silly bug in Elpi, constant is also a builtin *)
(** {1 Extension points} *)

and attribute = Parsetree.attribute =
  { attr_name : string loc;
    attr_payload : payload;
    attr_loc : location;
  }
(* [@id ARG]
   [@@id ARG]

   Metadata containers passed around within the AST.
   The compiler ignores unknown attributes.
*)

and extension = string loc * payload
(* [%id ARG]
   [%%id ARG]

   Sub-language placeholder -- rejected by the typechecker.
*)

and attributes = attribute list

and payload = Parsetree.payload =
  | PStr of structure
  | PSig of signature (* : SIG *)
  | PTyp of core_type  (* : T *)
  | PPat of pattern * expression option  (* ? P  or  ? P when E *)

(** {1 Core language} *)

(* Type expressions *)

and core_type = Parsetree.core_type =
  {
    ptyp_desc: core_type_desc;
    ptyp_loc: location;
    ptyp_loc_stack: location_stack;
    ptyp_attributes: attributes; (* ... [@id1] [@id2] *)
  }

and core_type_desc = Parsetree.core_type_desc =
  | Ptyp_any
  (*  _ *)
  | Ptyp_var of string
  (* 'a *)
  | Ptyp_arrow of arg_label * core_type * core_type
  (* T1 -> T2       Simple
     ~l:T1 -> T2    Labelled
     ?l:T1 -> T2    Optional
  *)
  | Ptyp_tuple of core_type list
  (* T1 * ... * Tn

     Invariant: n >= 2
  *)
  | Ptyp_constr of longident_loc * core_type list
  (* tconstr
     T tconstr
     (T1, ..., Tn) tconstr
  *)
  | Ptyp_object of object_field list * closed_flag
  (* < l1:T1; ...; ln:Tn >     (flag = Closed)
     < l1:T1; ...; ln:Tn; .. > (flag = Open)
  *)
  | Ptyp_class of longident_loc * core_type list
  (* #tconstr
     T #tconstr
     (T1, ..., Tn) #tconstr
  *)
  | Ptyp_alias of core_type * string
  (* T as 'a *)
  | Ptyp_variant of row_field list * closed_flag * label list option
  (* [ `A|`B ]         (flag = Closed; labels = None)
     [> `A|`B ]        (flag = Open;   labels = None)
     [< `A|`B ]        (flag = Closed; labels = Some [])
     [< `A|`B > `X `Y ](flag = Closed; labels = Some ["X";"Y"])
  *)
  | Ptyp_poly of string loc list * core_type
  (* 'a1 ... 'an. T

     Can only appear in the following context:

     - As the core_type of a Ppat_constraint node corresponding
     to a constraint on a let-binding: let x : 'a1 ... 'an. T
     = e ...

     - Under Cfk_virtual for methods (not values).

     - As the core_type of a Pctf_method node.

     - As the core_type of a Pexp_poly node.

     - As the pld_type field of a label_declaration.

     - As a core_type of a Ptyp_object node.
  *)

  | Ptyp_package of package_type
  (* (module S) *)
  | Ptyp_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%id] *)

and package_type = longident_loc * (longident_loc * core_type) list
        (*
   (module S)
   (module S with type t1 = T1 and ... and tn = Tn)
*)

and row_field = Parsetree.row_field =
  { prf_desc : row_field_desc;
    prf_loc : location;
    prf_attributes : attributes;
  }

and row_field_desc = Parsetree.row_field_desc =
  | Rtag of label loc * bool * core_type list
  (* [`A]                   ( true,  [] )
     [`A of T]              ( false, [T] )
     [`A of T1 & .. & Tn]   ( false, [T1;...Tn] )
     [`A of & T1 & .. & Tn] ( true,  [T1;...Tn] )

     - The 2nd field is true if the tag contains a
     constant (empty) constructor.
     - '&' occurs when several types are used for the same constructor
     (see 4.2 in the manual)

     - TODO: switch to a record representation, and keep location
  *)
  | Rinherit of core_type
  (* [ T ] *)

and object_field = Parsetree.object_field =
  { pof_desc : object_field_desc;
    pof_loc : location;
    pof_attributes : attributes;
  }

and object_field_desc = Parsetree.object_field_desc =
  | Otag of label loc * core_type
  | Oinherit of core_type

(* Patterns *)

and pattern = Parsetree.pattern =
  {
    ppat_desc: pattern_desc;
    ppat_loc: location;
    ppat_loc_stack: location_stack;
    ppat_attributes: attributes; (* ... [@id1] [@id2] *)
  }

and pattern_desc = Parsetree.pattern_desc =
  | Ppat_any
  (* _ *)
  | Ppat_var of string loc
  (* x *)
  | Ppat_alias of pattern * string loc
  (* P as 'a *)
  | Ppat_constant of constant
  (* 1, 'a', "true", 1.0, 1l, 1L, 1n *)
  | Ppat_interval of constant * constant
  (* 'a'..'z'

     Other forms of interval are recognized by the parser
     but rejected by the type-checker. *)
  | Ppat_tuple of pattern list
  (* (P1, ..., Pn)

     Invariant: n >= 2
  *)
  | Ppat_construct of longident_loc * pattern option
  (* C                None
     C P              Some P
     C (P1, ..., Pn)  Some (Ppat_tuple [P1; ...; Pn])
  *)
  | Ppat_variant of label * pattern option
  (* `A             (None)
     `A P           (Some P)
  *)
  | Ppat_record of (longident_loc * pattern) list * closed_flag
  (* { l1=P1; ...; ln=Pn }     (flag = Closed)
     { l1=P1; ...; ln=Pn; _}   (flag = Open)

     Invariant: n > 0
  *)
  | Ppat_array of pattern list
  (* [| P1; ...; Pn |] *)
  | Ppat_or of pattern * pattern
  (* P1 | P2 *)
  | Ppat_constraint of pattern * core_type
  (* (P : T) *)
  | Ppat_type of longident_loc
  (* #tconst *)
  | Ppat_lazy of pattern
  (* lazy P *)
  | Ppat_unpack of string loc
  (* (module P)
     Note: (module P : S) is represented as
     Ppat_constraint(Ppat_unpack, Ptyp_package)
  *)
  | Ppat_exception of pattern
  (* exception P *)
  | Ppat_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%id] *)
  | Ppat_open of longident_loc * pattern
  (* M.(P) *)

(* Value expressions *)

and expression = Parsetree.expression =
  {
    pexp_desc: expression_desc;
    pexp_loc: location;
    pexp_loc_stack: location_stack;
    pexp_attributes: attributes; (* ... [@id1] [@id2] *)
  }

and expression_desc = Parsetree.expression_desc =
  | Pexp_ident of longident_loc
  (* x
     M.x
  *)
  | Pexp_constant of constant
  (* 1, 'a', "true", 1.0, 1l, 1L, 1n *)
  | Pexp_let of rec_flag * value_binding list * expression
  (* let P1 = E1 and ... and Pn = EN in E       (flag = Nonrecursive)
     let rec P1 = E1 and ... and Pn = EN in E   (flag = Recursive)
  *)
  | Pexp_function of case list
  (* function P1 -> E1 | ... | Pn -> En *)
  | Pexp_fun of arg_label * expression option * pattern * expression
  (* fun P -> E1                          (Simple, None)
     fun ~l:P -> E1                       (Labelled l, None)
     fun ?l:P -> E1                       (Optional l, None)
     fun ?l:(P = E0) -> E1                (Optional l, Some E0)

     Notes:
     - If E0 is provided, only Optional is allowed.
     - "fun P1 P2 .. Pn -> E1" is represented as nested Pexp_fun.
     - "let f P = E" is represented using Pexp_fun.
  *)
  | Pexp_apply of expression * (arg_label * expression) list
  (* E0 ~l1:E1 ... ~ln:En
     li can be empty (non labeled argument) or start with '?'
     (optional argument).

     Invariant: n > 0
  *)
  | Pexp_match of expression * case list
  (* match E0 with P1 -> E1 | ... | Pn -> En *)
  | Pexp_try of expression * case list
  (* try E0 with P1 -> E1 | ... | Pn -> En *)
  | Pexp_tuple of expression list
  (* (E1, ..., En)

     Invariant: n >= 2
  *)
  | Pexp_construct of longident_loc * expression option
  (* C                None
     C E              Some E
     C (E1, ..., En)  Some (Pexp_tuple[E1;...;En])
  *)
  | Pexp_variant of label * expression option
  (* `A             (None)
     `A E           (Some E)
  *)
  | Pexp_record of (longident_loc * expression) list * expression option
  (* { l1=P1; ...; ln=Pn }     (None)
     { E0 with l1=P1; ...; ln=Pn }   (Some E0)

     Invariant: n > 0
  *)
  | Pexp_field of expression * longident_loc
  (* E.l *)
  | Pexp_setfield of expression * longident_loc * expression
  (* E1.l <- E2 *)
  | Pexp_array of expression list
  (* [| E1; ...; En |] *)
  | Pexp_ifthenelse of expression * expression * expression option
  (* if E1 then E2 else E3 *)
  | Pexp_sequence of expression * expression
  (* E1; E2 *)
  | Pexp_while of expression * expression
  (* while E1 do E2 done *)
  | Pexp_for of
      pattern *  expression * expression * direction_flag * expression
  (* for i = E1 to E2 do E3 done      (flag = Upto)
     for i = E1 downto E2 do E3 done  (flag = Downto)
  *)
  | Pexp_constraint of expression * core_type
  (* (E : T) *)
  | Pexp_coerce of expression * core_type option * core_type
  (* (E :> T)        (None, T)
     (E : T0 :> T)   (Some T0, T)
  *)
  | Pexp_send of expression * label loc
  (*  E # m *)
  | Pexp_new of longident_loc
  (* new M.c *)
  | Pexp_setinstvar of label loc * expression
  (* x <- 2 *)
  | Pexp_override of (label loc * expression) list
  (* {< x1 = E1; ...; Xn = En >} *)
  | Pexp_letmodule of string loc * module_expr * expression
  (* let module M = ME in E *)
  | Pexp_letexception of extension_constructor * expression
  (* let exception C in E *)
  | Pexp_assert of expression
  (* assert E
     Note: "assert false" is treated in a special way by the
     type-checker. *)
  | Pexp_lazy of expression
  (* lazy E *)
  | Pexp_poly of expression * core_type option
  (* Used for method bodies.

     Can only be used as the expression under Cfk_concrete
     for methods (not values). *)
  | Pexp_object of class_structure
  (* object ... end *)
  | Pexp_newtype of string loc * expression
  (* fun (type t) -> E *)
  | Pexp_pack of module_expr
  (* (module ME)

     (module ME : S) is represented as
     Pexp_constraint(Pexp_pack, Ptyp_package S) *)
  | Pexp_open of open_declaration * expression
  (* M.(E)
     let open M in E
     let! open M in E *)
  | Pexp_letop of letop
  (* let* P = E in E
     let* P = E and* P = E in E *)
  | Pexp_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%id] *)
  | Pexp_unreachable
  (* . *)

and case = Parsetree.case =   (* (P -> E) or (P when E0 -> E) *)
  {
    pc_lhs: pattern;
    pc_guard: expression option;
    pc_rhs: expression;
  }

and letop = Parsetree.letop =
  { let_ : binding_op;
    ands : binding_op list;
    body : expression;
  }

and binding_op = Parsetree.binding_op =
  { pbop_op : string loc;
    pbop_pat : pattern;
    pbop_exp : expression;
    pbop_loc : location;
  }

(* Value descriptions *)

and value_description = Parsetree.value_description =
  {
    pval_name: string loc;
    pval_type: core_type;
    pval_prim: string list;
    pval_attributes: attributes;  (* ... [@@id1] [@@id2] *)
    pval_loc: location;
  }

  (*
   val x: T                            (prim = [])
   external x: T = "s1" ... "sn"       (prim = ["s1";..."sn"])
*)

(* Type declarations *)

and type_declaration = Parsetree.type_declaration =
  {
    ptype_name: string loc;
    ptype_params: (core_type * variance) list;
    (* ('a1,...'an) t; None represents  _*)
    ptype_cstrs: (core_type * core_type * location) list;
    (* ... constraint T1=T1'  ... constraint Tn=Tn' *)
    ptype_kind: type_kind;
    ptype_private: private_flag;   (* = private ... *)
    ptype_manifest: core_type option;  (* = T *)
    ptype_attributes: attributes;   (* ... [@@id1] [@@id2] *)
    ptype_loc: location;
  }

  (*
   type t                     (abstract, no manifest)
   type t = T0                (abstract, manifest=T0)
   type t = C of T | ...      (variant,  no manifest)
   type t = T0 = C of T | ... (variant,  manifest=T0)
   type t = {l: T; ...}       (record,   no manifest)
   type t = T0 = {l : T; ...} (record,   manifest=T0)
   type t = ..                (open,     no manifest)
*)

and type_kind = Parsetree.type_kind =
  | Ptype_abstract
  | Ptype_variant of constructor_declaration list
  | Ptype_record of label_declaration list
  (* Invariant: non-empty list *)
  | Ptype_open

and label_declaration = Parsetree.label_declaration =
  {
    pld_name: string loc;
    pld_mutable: mutable_flag;
    pld_type: core_type;
    pld_loc: location;
    pld_attributes: attributes; (* l : T [@id1] [@id2] *)
  }

(*  { ...; l: T; ... }            (mutable=Immutable)
    { ...; mutable l: T; ... }    (mutable=Mutable)

    Note: T can be a Ptyp_poly.
*)

and constructor_declaration = Parsetree.constructor_declaration =
  {
    pcd_name: string loc;
    pcd_args: constructor_arguments;
    pcd_res: core_type option;
    pcd_loc: location;
    pcd_attributes: attributes; (* C of ... [@id1] [@id2] *)
  }

and constructor_arguments = Parsetree.constructor_arguments =
  | Pcstr_tuple of core_type list
  | Pcstr_record of label_declaration list

  (*
   | C of T1 * ... * Tn     (res = None,    args = Pcstr_tuple [])
   | C: T0                  (res = Some T0, args = [])
   | C: T1 * ... * Tn -> T0 (res = Some T0, args = Pcstr_tuple)
   | C of {...}             (res = None,    args = Pcstr_record)
   | C: {...} -> T0         (res = Some T0, args = Pcstr_record)
   | C of {...} as t        (res = None,    args = Pcstr_record)
*)

and type_extension = Parsetree.type_extension =
  {
    ptyext_path: longident_loc;
    ptyext_params: (core_type * variance) list;
    ptyext_constructors: extension_constructor list;
    ptyext_private: private_flag;
    ptyext_loc: location;
    ptyext_attributes: attributes;   (* ... [@@id1] [@@id2] *)
  }
  (*
   type t += ...
*)

and extension_constructor = Parsetree.extension_constructor =
  {
    pext_name: string loc;
    pext_kind : extension_constructor_kind;
    pext_loc : location;
    pext_attributes: attributes; (* C of ... [@id1] [@id2] *)
  }

and type_exception = Parsetree.type_exception =
  { ptyexn_constructor: extension_constructor;
    ptyexn_loc: location;
    ptyexn_attributes: attributes;
  }

and extension_constructor_kind = Parsetree.extension_constructor_kind =
    Pext_decl of constructor_arguments * core_type option
        (*
     | C of T1 * ... * Tn     ([T1; ...; Tn], None)
     | C: T0                  ([], Some T0)
     | C: T1 * ... * Tn -> T0 ([T1; ...; Tn], Some T0)
  *)
  | Pext_rebind of longident_loc
        (*
     | C = D
  *)

(** {1 Class language} *)

(* Type expressions for the class language *)

and class_type = Parsetree.class_type =
  {
    pcty_desc: class_type_desc;
    pcty_loc: location;
    pcty_attributes: attributes; (* ... [@id1] [@id2] *)
  }

and class_type_desc = Parsetree.class_type_desc =
  | Pcty_constr of longident_loc * core_type list
  (* c
     ['a1, ..., 'an] c *)
  | Pcty_signature of class_signature
  (* object ... end *)
  | Pcty_arrow of arg_label * core_type * class_type
  (* T -> CT       Simple
     ~l:T -> CT    Labelled l
     ?l:T -> CT    Optional l
  *)
  | Pcty_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%id] *)
  | Pcty_open of open_description * class_type
  (* let open M in CT *)

and class_signature = Parsetree.class_signature =
  {
    pcsig_self: core_type;
    pcsig_fields: class_type_field list;
  }
(* object('selfpat) ... end
   object ... end             (self = Ptyp_any)
*)

and class_type_field = Parsetree.class_type_field =
  {
    pctf_desc: class_type_field_desc;
    pctf_loc: location;
    pctf_attributes: attributes; (* ... [@@id1] [@@id2] *)
  }

and class_type_field_desc = Parsetree.class_type_field_desc =
  | Pctf_inherit of class_type
  (* inherit CT *)
  | Pctf_val of (label loc * mutable_flag * virtual_flag * core_type)
  (* val x: T *)
  | Pctf_method  of (label loc * private_flag * virtual_flag * core_type)
  (* method x: T

     Note: T can be a Ptyp_poly.
  *)
  | Pctf_constraint  of (core_type * core_type)
  (* constraint T1 = T2 *)
  | Pctf_attribute of attribute
  (* [@@@id] *)
  | Pctf_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%%id] *)

and 'a class_infos = 'a Parsetree.class_infos =
  {
    pci_virt: virtual_flag;
    pci_params: (core_type * variance) list;
    pci_name: string loc;
    pci_expr: 'a;
    pci_loc: location;
    pci_attributes: attributes;  (* ... [@@id1] [@@id2] *)
  }
(* class c = ...
   class ['a1,...,'an] c = ...
   class virtual c = ...

   Also used for "class type" declaration.
*)

and class_description = class_type class_infos

and class_type_declaration = class_type class_infos

(* Value expressions for the class language *)

and class_expr = Parsetree.class_expr =
  {
    pcl_desc: class_expr_desc;
    pcl_loc: location;
    pcl_attributes: attributes; (* ... [@id1] [@id2] *)
  }

and class_expr_desc = Parsetree.class_expr_desc =
  | Pcl_constr of longident_loc * core_type list
  (* c
     ['a1, ..., 'an] c *)
  | Pcl_structure of class_structure
  (* object ... end *)
  | Pcl_fun of arg_label * expression option * pattern * class_expr
  (* fun P -> CE                          (Simple, None)
     fun ~l:P -> CE                       (Labelled l, None)
     fun ?l:P -> CE                       (Optional l, None)
     fun ?l:(P = E0) -> CE                (Optional l, Some E0)
  *)
  | Pcl_apply of class_expr * (arg_label * expression) list
  (* CE ~l1:E1 ... ~ln:En
     li can be empty (non labeled argument) or start with '?'
     (optional argument).

     Invariant: n > 0
  *)
  | Pcl_let of rec_flag * value_binding list * class_expr
  (* let P1 = E1 and ... and Pn = EN in CE      (flag = Nonrecursive)
     let rec P1 = E1 and ... and Pn = EN in CE  (flag = Recursive)
  *)
  | Pcl_constraint of class_expr * class_type
  (* (CE : CT) *)
  | Pcl_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%id] *)
  | Pcl_open of open_description * class_expr
  (* let open M in CE *)


and class_structure = Parsetree.class_structure =
  {
    pcstr_self: pattern;
    pcstr_fields: class_field list;
  }
(* object(selfpat) ... end
   object ... end           (self = Ppat_any)
*)

and class_field = Parsetree.class_field =
  {
    pcf_desc: class_field_desc;
    pcf_loc: location;
    pcf_attributes: attributes; (* ... [@@id1] [@@id2] *)
  }

and class_field_desc = Parsetree.class_field_desc =
  | Pcf_inherit of override_flag * class_expr * string loc option
  (* inherit CE
     inherit CE as x
     inherit! CE
     inherit! CE as x
  *)
  | Pcf_val of (label loc * mutable_flag * class_field_kind)
  (* val x = E
     val virtual x: T
  *)
  | Pcf_method of (label loc * private_flag * class_field_kind)
  (* method x = E            (E can be a Pexp_poly)
     method virtual x: T     (T can be a Ptyp_poly)
  *)
  | Pcf_constraint of (core_type * core_type)
  (* constraint T1 = T2 *)
  | Pcf_initializer of expression
  (* initializer E *)
  | Pcf_attribute of attribute
  (* [@@@id] *)
  | Pcf_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%%id] *)

and class_field_kind = Parsetree.class_field_kind =
  | Cfk_virtual of core_type
  | Cfk_concrete of override_flag * expression

and class_declaration = class_expr class_infos

(** {1 Module language} *)

(* Type expressions for the module language *)

and module_type = Parsetree.module_type =
  {
    pmty_desc: module_type_desc;
    pmty_loc: location;
    pmty_attributes: attributes; (* ... [@id1] [@id2] *)
  }

and module_type_desc = Parsetree.module_type_desc =
  | Pmty_ident of longident_loc
  (* S *)
  | Pmty_signature of signature
  (* sig ... end *)
  | Pmty_functor of string loc * module_type option * module_type
  (* functor(X : MT1) -> MT2 *)
  | Pmty_with of module_type * with_constraint list
  (* MT with ... *)
  | Pmty_typeof of module_expr
  (* module type of ME *)
  | Pmty_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%id] *)
  | Pmty_alias of longident_loc
  (* (module M) *)

and signature = signature_item list

and signature_item = Parsetree.signature_item =
  {
    psig_desc: signature_item_desc;
    psig_loc: location;
  }

and signature_item_desc = Parsetree.signature_item_desc =
  | Psig_value of value_description
          (*
     val x: T
     external x: T = "s1" ... "sn"
  *)
  | Psig_type of rec_flag * type_declaration list
  (* type t1 = ... and ... and tn = ... *)
  | Psig_typesubst of type_declaration list
  (* type t1 := ... and ... and tn := ...  *)
  | Psig_typext of type_extension
  (* type t1 += ... *)
  | Psig_exception of type_exception
  (* exception C of T *)
  | Psig_module of module_declaration
  (* module X : MT *)
  | Psig_modsubst of module_substitution
  (* module X := M *)
  | Psig_recmodule of module_declaration list
  (* module rec X1 : MT1 and ... and Xn : MTn *)
  | Psig_modtype of module_type_declaration
  (* module type S = MT
     module type S *)
  | Psig_open of open_description
  (* open X *)
  | Psig_include of include_description
  (* include MT *)
  | Psig_class of class_description list
  (* class c1 : ... and ... and cn : ... *)
  | Psig_class_type of class_type_declaration list
  (* class type ct1 = ... and ... and ctn = ... *)
  | Psig_attribute of attribute
  (* [@@@id] *)
  | Psig_extension of extension * attributes [@elpi.embed maybe_override_embed2 ]
  (* [%%id] *)

and module_declaration = Parsetree.module_declaration =
  {
    pmd_name: string loc;
    pmd_type: module_type;
    pmd_attributes: attributes; (* ... [@@id1] [@@id2] *)
    pmd_loc: location;
  }
(* S : MT *)

and module_substitution = Parsetree.module_substitution =
  { pms_name: string loc;
    pms_manifest: longident_loc;
    pms_attributes: attributes;
    pms_loc: location;
  }

and module_type_declaration = Parsetree.module_type_declaration =
  {
    pmtd_name: string loc;
    pmtd_type: module_type option;
    pmtd_attributes: attributes; (* ... [@@id1] [@@id2] *)
    pmtd_loc: location;
  }
(* S = MT
   S       (abstract module type declaration, pmtd_type = None)
*)

and 'a open_infos = 'a Parsetree.open_infos =
  { popen_expr: 'a;
    popen_override: override_flag;
    popen_loc: location;
    popen_attributes: attributes;
  }

and open_description = longident_loc open_infos
(* open! X - popen_override = Override (silences the 'used identifier
   shadowing' warning)
   open  X - popen_override = Fresh
*)

and open_declaration = module_expr open_infos

and 'a include_infos = 'a Parsetree.include_infos =
  {
    pincl_mod: 'a;
    pincl_loc: location;
    pincl_attributes: attributes;
  }

and include_description = module_type include_infos
(* include MT *)

and include_declaration = module_expr include_infos
(* include ME *)

and with_constraint = Parsetree.with_constraint =
  | Pwith_type of longident_loc * type_declaration
  (* with type X.t = ...

     Note: the last component of the longident must match
     the name of the type_declaration. *)
  | Pwith_module of longident_loc * longident_loc
  (* with module X.Y = Z *)
  | Pwith_typesubst of longident_loc * type_declaration
  (* with type X.t := ..., same format as [Pwith_type] *)
  | Pwith_modsubst of longident_loc * longident_loc
  (* with module X.Y := Z *)

(* Value expressions for the module language *)

and module_expr = Parsetree.module_expr =
  {
    pmod_desc: module_expr_desc;
    pmod_loc: location;
    pmod_attributes: attributes; (* ... [@id1] [@id2] *)
  }

and module_expr_desc = Parsetree.module_expr_desc =
  | Pmod_ident of longident_loc
  (* X *)
  | Pmod_structure of structure
  (* struct ... end *)
  | Pmod_functor of string loc * module_type option * module_expr
  (* functor(X : MT1) -> ME *)
  | Pmod_apply of module_expr * module_expr
  (* ME1(ME2) *)
  | Pmod_constraint of module_expr * module_type
  (* (ME : MT) *)
  | Pmod_unpack of expression
  (* (val E) *)
  | Pmod_extension of extension [@elpi.embed maybe_override_embed ]
  (* [%id] *)

and structure = structure_item list

and structure_item = Parsetree.structure_item =
  {
    pstr_desc: structure_item_desc;
    pstr_loc: location;
  }

and structure_item_desc = Parsetree.structure_item_desc =
  | Pstr_eval of expression * attributes
  (* E *)
  | Pstr_value of rec_flag * value_binding list
  (* let P1 = E1 and ... and Pn = EN       (flag = Nonrecursive)
     let rec P1 = E1 and ... and Pn = EN   (flag = Recursive)
  *)
  | Pstr_primitive of value_description
  (*  val x: T
      external x: T = "s1" ... "sn" *)
  | Pstr_type of rec_flag * type_declaration list
  (* type t1 = ... and ... and tn = ... *)
  | Pstr_typext of type_extension
  (* type t1 += ... *)
  | Pstr_exception of type_exception
  (* exception C of T
     exception C = M.X *)
  | Pstr_module of module_binding
  (* module X = ME *)
  | Pstr_recmodule of module_binding list
  (* module rec X1 = ME1 and ... and Xn = MEn *)
  | Pstr_modtype of module_type_declaration
  (* module type S = MT *)
  | Pstr_open of open_declaration
  (* open X *)
  | Pstr_class of class_declaration list
  (* class c1 = ... and ... and cn = ... *)
  | Pstr_class_type of class_type_declaration list
  (* class type ct1 = ... and ... and ctn = ... *)
  | Pstr_include of include_declaration
  (* include ME *)
  | Pstr_attribute of attribute
  (* [@@@id] *)
  | Pstr_extension of extension * attributes
  (* [%%id] *)

and value_binding = Parsetree.value_binding =
  {
    pvb_pat: pattern;
    pvb_expr: expression;
    pvb_attributes: attributes;
    pvb_loc: location;
  }

and module_binding = Parsetree.module_binding =
  {
    pmb_name: string loc;
    pmb_expr: module_expr;
    pmb_attributes: attributes;
    pmb_loc: location;
  }
(* X = ME *)

(** {1 Toplevel} *)

(* Toplevel phrases *)

and toplevel_phrase = Parsetree.toplevel_phrase =
  | Ptop_def of structure
  | Ptop_dir of toplevel_directive
  (* #use, #load ... *)

and toplevel_directive = Parsetree.toplevel_directive =
  { pdir_name : string loc;
    pdir_arg : directive_argument option;
    pdir_loc : location;
  }
and directive_argument = Parsetree.directive_argument =
  { pdira_desc : directive_argument_desc;
    pdira_loc : location;
  }

and directive_argument_desc = Parsetree.directive_argument_desc =
  | Pdir_string of string
  | Pdir_int of string * char option
  | Pdir_ident of longident
  | Pdir_bool of bool
[@@deriving show, elpi { declaration = parsetree_declaration; mapper = parsetree_mapper }]

let parsetree_declaration = !parsetree_declaration
let parsetree_mapper = !parsetree_mapper
