(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id: notationPt.ml 13145 2016-03-13 17:30:14Z fguidi $ *)

(** CIC Notation Parse Tree *)

type binder_kind = [ `Lambda | `Pi | `Exists | `Forall ]
type induction_kind = [ `Inductive | `CoInductive ]
type sort_kind = [ `Prop | `Set | `NType of string |`NCProp of string]
type fold_kind = [ `Left | `Right ]

type location = Stdpp.location
let fail floc msg =
  let (x, y) = HExtlib.loc_of_floc floc in
  failwith (Printf.sprintf "Error at characters %d - %d: %s" x y msg)

type href = NReference.reference

type child_pos = [ `Left | `Right | `Inner ]

type term_attribute =
  [ `Loc of location                  (* source file location *)
  | `IdRef of string                  (* ACic pointer *)
  | `Level of int
  | `XmlAttrs of (string option * string * string) list
      (* list of XML attributes: namespace, name, value *)
  | `Raw of string                    (* unparsed version *)
  ]

type literal =
  [ `Symbol of string
  | `Keyword of string
  | `Number of string
  ]

type case_indtype = string * href option

type 'term capture_variable = 'term * 'term option

(** To be increased each time the term type below changes, used for "safe"
 * marshalling *)
let magic = 8

type term =
  (* CIC AST *)

  | AttributedTerm of term_attribute * term

  | Appl of term list
  | Binder of binder_kind * term capture_variable * term (* kind, name, body *)
  | Case of term * case_indtype option * term option *
      (case_pattern * term) list
      (* what to match, inductive type, out type, <pattern,action> list *)
  | Cast of term * term
  | LetIn of term capture_variable * term * term  (* name, body, where *)
  | Ident of string * subst list option
      (* literal, substitutions.
      * Some [] -> user has given an empty explicit substitution list 
      * None -> user has given no explicit substitution list *)
  | Implicit of [`Vector | `JustOne | `Tagged of string]
  | Meta of int * meta_subst list
  | Num of string * int (* literal, instance *)
  | Sort of sort_kind
  | Symbol of string * int  (* canonical name, instance *)

  | UserInput (* place holder for user input, used by MatitaConsole, not to be
              used elsewhere *)
  | Uri of string * subst list option (* as Ident, for long names *)
  | NRef of NReference.reference

  | NCic of NCic.term

  (* Syntax pattern extensions *)

  | Literal of literal
  | Layout of layout_pattern

  | Magic of magic_term
  | Variable of pattern_variable

  (* name, type. First component must be Ident or Variable (FreshVar _) *)

and meta_subst = term option
and subst = string * term
and case_pattern =
   Pattern of string * href option * term capture_variable list
 | Wildcard

and box_kind = H | V | HV | HOV
and box_spec = box_kind * bool * bool (* kind, spacing, indent *)

and layout_pattern =
  | Sub of term * term
  | Sup of term * term
  | Below of term * term
  | Above of term * term
  | Frac of term * term
  | Over of term * term
  | Atop of term * term
  | InfRule of term * term * term
(*   | array of term * literal option * literal option
      |+ column separator, row separator +| *)
  | Maction of term list
  | Sqrt of term
  | Root of term * term (* argument, index *)
  | Break
  | Box of box_spec * term list
  | Group of term list
  | Mstyle of (string * string) list * term list
  | Mpadded of (string * string) list * term list

and magic_term =
  (* level 1 magics *)
  | List0 of term * literal option (* pattern, separator *)
  | List1 of term * literal option (* pattern, separator *)
  | Opt of term

  (* level 2 magics *)
  | Fold of fold_kind * term * string list * term
    (* base case pattern, recursive case bound names, recursive case pattern *)
  | Default of term * term  (* "some" case pattern, "none" case pattern *)
  | Fail
  | If of term * term * term (* test, pattern if true, pattern if false *)

and term_level = Self of int | Level of int

and pattern_variable =
  (* level 1 and 2 variables *)
  | NumVar of string
  | IdentVar of string
  | TermVar of string * term_level

  (* level 1 variables *)
  | Ascription of term * string

  (* level 2 variables *)
  | FreshVar of string

type argument_pattern =
  | IdentArg of int * string (* eta-depth, name *)

type cic_appl_pattern =
  | NRefPattern of NReference.reference
  | VarPattern of string
  | ImplicitPattern
  | ApplPattern of cic_appl_pattern list

  (** <name, inductive/coinductive, type, constructor list>
  * true means inductive, false coinductive *)
type 'term inductive_type = string * bool * 'term * (string * 'term) list

type 'term obj =
  | Inductive of 'term capture_variable list * 'term inductive_type list * NCic.source
      (** parameters, list of loc * mutual inductive types *)
  | Theorem of string * 'term * 'term option * NCic.c_attr
      (** name, type, body, attributes
       * - name is absent when an unnamed theorem is being proved, tipically in
       *   interactive usage
       * - body is present when its given along with the command, otherwise it
       *   will be given in proof editing mode using the tactical language,
       *   unless the flavour is an Axiom
       *)
  | Record of 'term capture_variable list * string * 'term * (string * 'term * bool * int) list * NCic.source
      (** left parameters, name, type, fields *)
  | LetRec of induction_kind * ('term capture_variable list * 'term capture_variable * 'term * int) list * NCic.f_attr
      (* (params, name, body, decreasing arg) list, attributes *)

(** {2 Standard precedences} *)

let let_in_prec = 10
let binder_prec = 20
let apply_prec = 70
let simple_prec = 90
