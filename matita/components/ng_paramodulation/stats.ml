(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: stats.ml 9822 2009-06-03 15:37:06Z denes $ *)

module Stats (B : Terms.Blob) = 
  struct

    module SymbMap = Map.Make(B)

    let rec occ_nbr t acc = function
	| Terms.Leaf u when B.eq t u -> 1+acc
	| Terms.Node l -> List.fold_left (occ_nbr t) acc l
	| _ -> acc
    ;;

    let occ_nbr t = occ_nbr t 0;;

    let goal_occ_nbr t = function
      | (_,Terms.Equation (l,r,_,_),_,_) ->
	  occ_nbr t l + occ_nbr t r
      | _ -> assert false
    ;;

    let rec parse_symbols acc l =
      let rec aux acc = function
	| Terms.Leaf t ->
	    (try
	       let (occ,ar) = SymbMap.find t acc in
		 SymbMap.add t (occ+1,ar) acc
	     with Not_found -> SymbMap.add t (1,0) acc)
	| Terms.Var _ -> acc
	| Terms.Node (Terms.Leaf hd::tl) ->
	    let acc =
	      try let (occ,ar) = SymbMap.find hd acc in
		SymbMap.add hd (occ+1,ar) acc
	      with Not_found -> SymbMap.add hd (1,List.length tl) acc
	      in List.fold_left aux acc tl
	| _ -> assert false
      in
	match l with
	  | [] -> acc
	  | (_,hd,_,_)::tl ->
	      match hd with
		| Terms.Equation (l,r,_,_) ->
		    parse_symbols (aux (aux acc l) r) tl
		| Terms.Predicate _ -> assert false;
    ;;

    let goal_pos t goal =
      let rec aux path = function
       | Terms.Var _ -> [] 
       | Terms.Leaf x ->
           if B.eq t x then path else []
       | Terms.Node l ->
           match 
             HExtlib.list_findopt
               (fun x i -> 
                  let p = aux (i::path) x in
                  if p = [] then None else Some p)
               l
           with
           | None -> []
           | Some p -> p
      in 
        aux [] 
          (match goal with
          | _,Terms.Equation (l,r,ty,_),_,_ -> Terms.Node [ Terms.Leaf B.eqP; ty; l; r ]
	  | _,Terms.Predicate p,_,_ -> p)
    ;;

    let parse_symbols l goal = 
      let res = parse_symbols (parse_symbols SymbMap.empty [goal]) l in
	SymbMap.fold (fun t (occ,ar) acc ->
			(t,occ,ar,goal_occ_nbr t goal,goal_pos t goal)::acc) res []
    ;;

    let rec leaf_count = function
      | Terms.Node l -> List.fold_left (fun acc x -> acc + (leaf_count x)) 0 l
      | Terms.Leaf _ -> 1
      | _ -> 0
    ;;

    let rec dependencies op clauses acc =
      match clauses with
	| [] -> acc
	| (_,lit,_,_)::tl ->
	    match lit with
	      | Terms.Predicate _ -> assert false
	      | Terms.Equation (l,r,_,_) ->
		  match l,r with
		    | (Terms.Node (Terms.Leaf op1::_),Terms.Node
			 (Terms.Leaf op2::_)) ->
			if (B.eq op1 op) && not (B.eq op2 op) then
			  let already = List.exists (B.eq op2) acc in
			  let occ_l = occ_nbr op l in
			  let occ_r = occ_nbr op r in
			    if not already && occ_r > occ_l then
			      dependencies op tl (op2::acc)
			    else dependencies op tl acc
			else if not (B.eq op1 op) && (B.eq op2 op) then
			  let already = List.exists (B.eq op1) acc in
			  let occ_l = occ_nbr op l in
			  let occ_r = occ_nbr op r in
			    if not already && occ_l > occ_r then
			      dependencies op tl (op1::acc)
			    else
			      dependencies op tl acc
			else dependencies op tl acc
                    | ((Terms.Node (Terms.Leaf op1::t) as x),y)
                    | (y,(Terms.Node (Terms.Leaf op1::t) as x)) when leaf_count x > leaf_count y ->
                         let rec term_leaves = function
                           | Terms.Node l -> List.fold_left (fun acc x -> acc @ (term_leaves x)) [] l
                           | Terms.Leaf x -> [x]
                           | _ -> []
                         in
                         if List.mem op (List.filter (fun z -> not (B.eq op1 z)) (term_leaves x)) then 
                           dependencies op tl (op1::acc)
                         else
                           dependencies op tl acc
		    | _ -> dependencies op tl acc
    ;;

    let dependencies op clauses = HExtlib.list_uniq (List.sort Pervasives.compare (dependencies op clauses []));;

    (* let max_weight_hyp = *)

  end
