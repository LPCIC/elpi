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

type db 

class type g_status =
 object
  inherit CicNotationParser.g_status
  method parser_db: db
 end

class virtual status :
 object('self)
  inherit g_status
  inherit CicNotationParser.status
  method set_parser_db : db -> 'self
  method set_parser_status : 'status. #g_status as 'status -> 'self
 end

val extend : #status as 'status ->
           CicNotationParser.checked_l1_pattern ->
           (NotationEnv.t -> NotationPt.location -> NotationPt.term) -> 'status


 (* never_include: do not call LexiconEngine to do includes, 
  * always raise NoInclusionPerformed *) 
(** @raise End_of_file *)
type parsable
val parsable_statement: #status -> Ulexing.lexbuf -> parsable
val parse_statement: #status -> parsable -> GrafiteAst.statement
val strm_of_parsable: parsable -> Ulexing.lexbuf
