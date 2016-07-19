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

module Make :
  functor (M : Map.S) ->
    sig
      type key = M.key list
      type 'a t = Node of 'a option * 'a t M.t
      val empty : 'a t
      val find : M.key list -> 'a t -> 'a
      val mem : M.key list -> 'a t -> bool
      val add : M.key list -> 'a -> 'a t -> 'a t
      val remove : M.key list -> 'a t -> 'a t
      val map : ('a -> 'b) -> 'a t -> 'b t
      val mapi : (M.key list -> 'a -> 'b) -> 'a t -> 'b t
      val iter : (M.key list -> 'a -> 'b) -> 'a t -> unit
      val fold : (M.key list -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
      val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
      val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
      val is_empty : 'a t -> bool
    end
