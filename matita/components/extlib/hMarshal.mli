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

(** {2 Marshalling with version/consistency checks} *)

(** {3 File formats}
 *
 * Files saved/loaded by this module share a common format:
 *
 * | n | Field name  | Field type | Description                           |
 * +---+-------------+------------+---------------------------------------+
 * | 1 | format      | integer    | hash value of the 'fmt' parameter     |
 * | 2 | version     | integer    | 'version' parameter                   |
 * | 3 | format dsc  | string     | extended 'fmt' parameter              |
 * | 4 | version dsc | string     | extended 'version' parameter          |
 * | 5 | checksum    | integer    | hash value of the _field_ below       |
 * | 6 | data        | raw        | ocaml marshalling of 'data' parameter |
 *
 *)

exception Corrupt_file of string (** checksum mismatch, or file too short *)
exception Format_mismatch of string
exception Version_mismatch of string

  (** Marhsal some data according to the file format above.
   * @param fmt format name
   * @param version version number
   * @param fname file name to which marshal data
   * @param data data to be marshalled on disk *)
val save: fmt:string -> version:int -> fname:string -> 'a -> unit

  (** parameters as above
   * @raise Corrupt_file
   * @raise Format_mismatch
   * @raise Version_mismatch *)
val load: fmt:string -> version:int -> fname:string -> 'a

