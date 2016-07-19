(* Copyright (C) 2004, HELM Team.
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

(* $Id: grafiteAst.ml 13176 2016-04-18 15:29:33Z fguidi $ *)

type direction = [ `LeftToRight | `RightToLeft ]

type loc = Stdpp.location

type nterm = NotationPt.term

type npattern = 
 nterm option * (string * nterm) list * nterm option

type auto_params = nterm list option * (string*string) list

type ntactic =
   | NApply of loc * nterm
   | NSmartApply of loc * nterm
   | NAssert of loc * ((string * [`Decl of nterm | `Def of nterm * nterm]) list * nterm) list
   | NCases of loc * nterm * npattern  
   | NCase1 of loc * string
   | NChange of loc * npattern * nterm
   | NClear of loc * string list
   | NConstructor of loc * int option * nterm list
   | NCut of loc * nterm
(* | NDiscriminate of loc * nterm
   | NSubst of loc * nterm *)
   | NDestruct of loc * string list option * string list
   | NElim of loc * nterm * npattern  
   | NGeneralize of loc * npattern
   | NId of loc
   | NIntro of loc * string
   | NIntros of loc * string list
   | NInversion of loc * nterm * npattern  
   | NLApply of loc * nterm
   | NLetIn of loc * npattern * nterm * string
   | NReduce of loc * [ `Normalize of bool | `Whd of bool ] * npattern
   | NRewrite of loc * direction * nterm * npattern
   | NAuto of loc * auto_params
   | NDot of loc
   | NSemicolon of loc
   | NBranch of loc
   | NShift of loc
   | NPos of loc * int list
   | NPosbyname of loc * string
   | NWildcard of loc
   | NMerge of loc
   | NSkip of loc
   | NFocus of loc * int list
   | NUnfocus of loc
   | NTry of loc * ntactic
   | NAssumption of loc
   | NRepeat of loc * ntactic
   | NBlock of loc * ntactic list

type nmacro =
  | NCheck of loc * nterm
  | Screenshot of loc * string
  | NAutoInteractive of loc * auto_params
  | NIntroGuess of loc

(** To be increased each time the command type below changes, used for "safe"
 * marshalling *)
let magic = 37

(* composed magic: term + command magics. No need to change this value *)
let magic = magic + 10000 * NotationPt.magic

type alias_spec =
  | Ident_alias of string * string        (* identifier, uri *)
  | Symbol_alias of string * int * string (* name, instance no, description *)
  | Number_alias of int * string          (* instance no, description *)

type inclusion_mode = WithPreferences | WithoutPreferences | OnlyPreferences (* aka aliases *)

type command =
  | Include of loc * inclusion_mode * string (* _,buri,_,path *)
  | UnificationHint of loc * nterm * int (* term, precedence *)
  | NObj of loc * nterm NotationPt.obj * bool
  | NDiscriminator of loc * nterm
  | NInverter of loc * string * nterm * bool list option * nterm option
  | NUnivConstraint of loc * bool * NUri.uri * NUri.uri
  | NCopy of loc * string * NUri.uri * (NUri.uri * NUri.uri) list
  | NCoercion of loc * string * bool * 
      (nterm * nterm * (string * nterm) * nterm) option
  | NQed of loc * bool
  (* ex lexicon commands *)
  | Alias of loc * alias_spec
      (** parameters, name, type, fields *) 
  | Notation of loc * direction option * nterm * Gramext.g_assoc *
      int * nterm
      (* direction, l1 pattern, associativity, precedence, l2 pattern *)
  | Interpretation of loc *
      string * (string * NotationPt.argument_pattern list) *
        NotationPt.cic_appl_pattern
      (* description (i.e. id), symbol, arg pattern, appl pattern *)

type code =
  | NCommand of loc * command
  | NMacro of loc * nmacro 
  | NTactic of loc * ntactic list
             
type comment =
  | Note of loc * string
  | Code of loc * code
             
type statement =
  | Executable of loc * code
  | Comment of loc * comment

let description_of_alias =
 function
    Ident_alias (_,desc)
  | Symbol_alias (_,_,desc)
  | Number_alias (_,desc) -> desc
