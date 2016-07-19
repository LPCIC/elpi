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

(* $Id: grafiteTypes.ml 12484 2013-02-02 00:38:05Z sacerdot $ *)

exception Option_error of string * string
exception Statement_error of string
exception Command_error of string

let command_error msg = raise (Command_error msg)

class virtual status = fun (b : string) ->
 let fake_obj =
  NUri.uri_of_string "cic:/matita/dummy.decl",0,[],[],
   NCic.Constant([],"",None,NCic.Implicit `Closed,(`Provided,`Theorem,`Regular))
 in
  object
   (* Warning: #stack and #obj are meaningful iff #ng_mode is `ProofMode *)
   inherit ([Continuationals.Stack.t] NTacStatus.status fake_obj (Continuationals.Stack.empty))
   inherit NCicLibrary.dumpable_status
   inherit NCicLibrary.status
   inherit NCicExtraction.status
   inherit OcamlExtractionTable.status
   inherit GrafiteParser.status
   inherit TermContentPres.status
   val baseuri = b
   val ng_mode = (`CommandMode : [`CommandMode | `ProofMode])
   method baseuri = baseuri
   method set_baseuri v = {< baseuri = v >}
   method ng_mode = ng_mode;
   method set_ng_mode v = {< ng_mode = v >}
 end

module Serializer = NCicLibrary.Serializer(struct type dumpable_s = status end)
