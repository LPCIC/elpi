(* Copyright (C) 2004-2005, HELM Team.
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

  (** {2 state handling} *)

type db

class type g_status =
  object
    method content_pres_db: db
  end

class virtual status :
  object ('self)
    inherit NCic.status
    method content_pres_db: db
    method set_content_pres_db: db -> 'self
    method set_content_pres_status: #g_status -> 'self
  end

val add_pretty_printer:
 #status as 'status ->
  NotationPt.term ->             (* level 2 pattern *)
  CicNotationParser.checked_l1_pattern ->
   'status

  (** {2 content -> pres} *)

val pp_ast: #status -> NotationPt.term -> NotationPt.term

  (** {2 pres -> content} *)

  (** fills a term pattern instantiating variable magics *)
val instantiate_level2:
 #NCic.status -> NotationEnv.t -> NotationPt.term -> NotationPt.term
