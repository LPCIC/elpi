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

(* $Id: grafiteTypes.mli 12484 2013-02-02 00:38:05Z sacerdot $ *)

exception Option_error of string * string
exception Statement_error of string
exception Command_error of string

val command_error: string -> 'a   (** @raise Command_error *)

class virtual status :
 string ->
  object ('self)
   (* Warning: #stack and #obj are meaningful iff #ng_mode is `ProofMode *)
   inherit NTacStatus.tac_status
   inherit NCicLibrary.dumpable_status
   inherit NCicLibrary.status
   inherit NCicExtraction.status
   inherit OcamlExtractionTable.status
   inherit GrafiteParser.status
   inherit TermContentPres.status
   method baseuri: string
   method set_baseuri: string -> 'self
   method ng_mode: [`ProofMode | `CommandMode]
   method set_ng_mode: [`ProofMode | `CommandMode] -> 'self
  end

module Serializer: NCicLibrary.SerializerType with type dumpable_status = status
