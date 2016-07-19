(* Copyright (C) 2000-2002, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

(***************************************************************************)
(*                                                                         *)
(*                               PROJECT HELM                              *)
(*                                                                         *)
(*                   Andrea Asperti <asperti@cs.unibo.it>                  *)
(*                                21/11/2003                               *)
(*                                                                         *)
(*                                                                         *)
(***************************************************************************)

(* $Id: applyTransformation.ml 12012 2012-05-10 14:18:17Z sacerdot $ *)

let use_high_level_pretty_printer = ref true;; 

let to_text to_content to_pres lowlevel ~map_unicode_to_tex size status t =
 if !use_high_level_pretty_printer then
  let content,ids_to_nrefs = to_content status t in
  let pres = to_pres status ~ids_to_nrefs content in
  let pres = CicNotationPres.mpres_of_box pres in
   BoxPp.render_to_string ~map_unicode_to_tex
    (function x::_ -> x | _ -> assert false) size pres
 else
  [],lowlevel t

let ntxt_of_cic_sequent ~metasenv ~subst =
 to_text (Interpretations.nmap_sequent ~metasenv ~subst)
  Content2pres.nsequent2pres
  (fun seq -> (new NCicPp.status)#ppmetasenv ~subst [seq])

let ntxt_of_cic_object ~map_unicode_to_tex =
 to_text Interpretations.nmap_cobj Content2pres.nobj2pres ~map_unicode_to_tex
  (new NCicPp.status)#ppobj

let ntxt_of_cic_term ~metasenv ~subst ~context =
 to_text (Interpretations.nmap_term ~metasenv ~subst ~context)
  (Content2pres.nterm2pres ?prec:None)
  ((new NCicPp.status)#ppterm ~metasenv ~subst ~context)

let ntxt_of_cic_context ~metasenv ~subst =
 to_text (Interpretations.nmap_context ~metasenv ~subst)
  Content2pres.ncontext2pres
  ((new NCicPp.status)#ppcontext ~metasenv ~subst)

let ntxt_of_cic_subst ~map_unicode_to_tex size status ~metasenv ?use_subst subst =
 [],
 "<<<high level printer for subst not implemented; low-level printing:>>>\n" ^
  (new NCicPp.status)#ppsubst ~metasenv ?use_subst subst

class status =
 object(self)
  inherit Interpretations.status
  inherit TermContentPres.status
  method ppterm ~context ~subst ~metasenv ?margin ?inside_fix t =
   snd (ntxt_of_cic_term ~map_unicode_to_tex:false 80 self ~metasenv ~subst
    ~context t)

  method ppcontext ?sep ~subst ~metasenv context =
   snd (ntxt_of_cic_context ~map_unicode_to_tex:false 80 self ~metasenv ~subst
    context)

  method ppsubst ~metasenv ?use_subst subst =
   snd (ntxt_of_cic_subst ~map_unicode_to_tex:false 80 self ~metasenv ?use_subst
    subst)

  method ppmetasenv ~subst metasenv =
   String.concat "\n"
    (List.map
      (fun m -> snd (ntxt_of_cic_sequent ~map_unicode_to_tex:false 80 self
        ~metasenv ~subst m)) metasenv)

  method ppobj obj =
   snd (ntxt_of_cic_object ~map_unicode_to_tex:false 80 self obj)
 end
