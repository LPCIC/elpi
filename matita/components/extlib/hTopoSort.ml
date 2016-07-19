(* Copyright (C) 2006, HELM Team.
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

module Make (OT:Map.OrderedType) =
    struct
      
      module M = Map.Make(OT);;
      
      let topological_sort l find_deps = 
        let find_deps m x = 
          let deps = find_deps x in
          M.add x deps m
        in
        (* build the partial order relation *)
        let m = List.fold_left (fun m i -> find_deps m i) M.empty l in
        let m = (* keep only deps inside l *) 
          List.fold_left 
            (fun m' i ->
              M.add i (List.filter (fun x -> List.mem x l) (M.find i m)) m') 
            M.empty l 
        in
        let m = M.map (fun x -> Some x) m in
        (* utils *)
        let keys m = M.fold (fun i _ acc -> i::acc) m [] in
        let split l m = List.filter (fun i -> M.find i m = Some []) l in
        let purge l m = 
          M.mapi 
            (fun k v -> if List.mem k l then None else 
               match v with
               | None -> None
               | Some ll -> Some (List.filter (fun i -> not (List.mem i l)) ll)) 
            m
        in
        let rec aux m res = 
            let keys = keys m in
            let ok = split keys m in
            let m = purge ok m in
            let res = ok @ res in
            if ok = [] then res else aux m res
        in
        let rc = List.rev (aux m []) in
        rc
      ;;
      
    end
;;

