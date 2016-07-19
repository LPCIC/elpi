(* Copyright (C) 2000, HELM Team.
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

(**************************************************************************)
(*                                                                        *)
(*                           PROJECT HELM                                 *)
(*                                                                        *)
(*                Andrea Asperti <asperti@cs.unibo.it>                    *)
(*                             27/6/2003                                  *)
(*                                                                        *)
(**************************************************************************)

val nterm2pres:
 #TermContentPres.status ->
  ids_to_nrefs:(Content.id, NReference.reference) Hashtbl.t ->
  ?prec:int -> NotationPt.term -> CicNotationPres.boxml_markup

val ncontext2pres:
 #TermContentPres.status ->
  ids_to_nrefs:(Content.id, NReference.reference) Hashtbl.t ->
  NotationPt.term Content.context -> CicNotationPres.boxml_markup

val nobj2pres:
 #TermContentPres.status ->
  ids_to_nrefs:(Content.id, NReference.reference) Hashtbl.t ->
  NotationPt.term Content.cobj -> CicNotationPres.boxml_markup

val nsequent2pres :
 #TermContentPres.status ->
  ids_to_nrefs:(Content.id, NReference.reference) Hashtbl.t ->
  NotationPt.term Content.conjecture -> CicNotationPres.boxml_markup
