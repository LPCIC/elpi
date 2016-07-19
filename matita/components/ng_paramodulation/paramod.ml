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

(* $Id: orderings.ml 9869 2009-06-11 22:52:38Z denes $ *)

let print s = prerr_endline (Lazy.force s) ;; 
let noprint s = ();;  
let debug = noprint;;

let monster = 100;;
    
module type Paramod =
  sig
    type t
    type input
    type szsontology = 
      | Unsatisfiable of 
	  (t Terms.bag * int * t Terms.substitution * int list) list
      | GaveUp 
      | Error of string 
      | Timeout of int * t Terms.bag
    type bag = t Terms.bag * int
    type state
    val empty_state : state
    val bag_of_state : state -> bag
    val replace_bag: state -> bag -> state
    val mk_passive : bag -> input * input -> bag * t Terms.unit_clause
    val mk_goal : bag -> input * input -> bag * t Terms.unit_clause
    val forward_infer_step : 
      state ->
      t Terms.unit_clause ->
      int ->
      state
    val goal_narrowing : 
      int 
      -> int
      -> float option
      -> state
      -> state
    val paramod :
      useage:bool ->
      max_steps:int ->
      ?timeout:float ->
      bag -> 
      g_passives:t Terms.unit_clause list -> 
      passives:t Terms.unit_clause list -> szsontology
    val demod :
      state -> input* input -> szsontology
    val fast_eq_check :
      state -> input* input -> szsontology
    val nparamod :
      useage:bool ->
      max_steps:int ->
      ?timeout:float ->
      state -> input* input -> szsontology
  end

module Paramod (B : Orderings.Blob) = struct
  module Pp = Pp.Pp (B) 
  module FU = FoUnif.Founif(B) 
  module IDX = Index.Index(B) 
  module Sup = Superposition.Superposition(B) 
  module Utils = FoUtils.Utils(B) 
  module Order = B
  module WeightOrderedPassives =
      struct
        type t = B.t Terms.passive_clause
        let compare = Utils.compare_passive_clauses_weight
      end

  module AgeOrderedPassives =
      struct
        type t = B.t Terms.passive_clause
        let compare = Utils.compare_passive_clauses_age
      end
  
  module WeightPassiveSet = Set.Make(WeightOrderedPassives)
  module AgePassiveSet = Set.Make(AgeOrderedPassives)

  type t = B.t
  type input = B.input
  type bag = B.t Terms.bag * int 
  type szsontology = 
    | Unsatisfiable of 
	(B.t Terms.bag * int * B.t Terms.substitution * int list) list
    | GaveUp 
    | Error of string 
    | Timeout of int * B.t Terms.bag
  exception Stop of szsontology
  type state = 
      t Terms.bag 
      * int
      * Index.Index(B).active_set 
      * (IDX.DT.t * WeightPassiveSet.t * AgePassiveSet.t) 
      * B.t Terms.unit_clause list 
      * (WeightPassiveSet.t * AgePassiveSet.t)

  let empty_state = 
    Terms.empty_bag,
    0,
    ([],IDX.DT.empty),
    (IDX.DT.empty,WeightPassiveSet.empty,AgePassiveSet.empty),
    [],
    (WeightPassiveSet.empty,AgePassiveSet.empty)
  ;;

  let bag_of_state (bag,n,_,_,_,_) = bag,n
  ;;
  
  let replace_bag (_,_,a,b,c,d) (bag,n) = bag,n,a,b,c,d
  ;;

  let add_passive_clause ?(no_weight=false)
      (passive_t,passives_w,passives_a) cl =
    let pcl = if no_weight then (0,cl)
    else Utils.mk_passive_clause cl in
    IDX.index_unit_clause passive_t cl,
    WeightPassiveSet.add pcl passives_w, 
    AgePassiveSet.add pcl passives_a
  ;;

  let add_passive_goal ?(no_weight=false) (passives_w,passives_a) g =
    let g = if no_weight then (0,g)
    else Utils.mk_passive_goal g in
    WeightPassiveSet.add g passives_w, AgePassiveSet.add g passives_a
  ;;

  let remove_passive_clause (passive_t,passives_w,passives_a) cl =
    let passive_t = IDX.remove_unit_clause passive_t (snd cl) in
    let passives_w = WeightPassiveSet.remove cl passives_w in
    let passives_a = AgePassiveSet.remove cl passives_a in
      passive_t,passives_w,passives_a
  ;;

  let add_passive_clauses ?(no_weight=false) =
    List.fold_left (add_passive_clause ~no_weight)
  ;;

  let add_passive_goals ?(no_weight=false)
      (passives_w,passives_a) new_clauses =
    let new_clauses_w,new_clauses_a =
      List.fold_left (add_passive_goal ~no_weight)
      (WeightPassiveSet.empty,AgePassiveSet.empty) new_clauses
    in
      (WeightPassiveSet.union new_clauses_w passives_w,
       AgePassiveSet.union new_clauses_a passives_a)
  ;;

  let remove_passive_goal (passives_w,passives_a) cl =
    let passives_w = WeightPassiveSet.remove cl passives_w in
    let passives_a = AgePassiveSet.remove cl passives_a in
      passives_w,passives_a
  ;;

  let is_passive_set_empty (_,passives_w,passives_a) =
    if (WeightPassiveSet.is_empty passives_w) then begin
      assert (AgePassiveSet.is_empty passives_a); true
    end else begin
      assert (not (AgePassiveSet.is_empty passives_a)); false
    end
  ;;

  let is_passive_g_set_empty (passives_w,passives_a) =
    if (WeightPassiveSet.is_empty passives_w) then begin
      assert (AgePassiveSet.is_empty passives_a); true
    end else begin
      assert (not (AgePassiveSet.is_empty passives_a)); false
    end
  ;;

  let passive_set_cardinal (_,passives_w,_) 
      = WeightPassiveSet.cardinal passives_w
  ;;

  let g_passive_set_cardinal (passives_w,_) 
      = WeightPassiveSet.cardinal passives_w
  ;;

  let passive_empty_set =
    (IDX.DT.empty,WeightPassiveSet.empty,AgePassiveSet.empty)
  ;;

  let g_passive_empty_set =
    (WeightPassiveSet.empty,AgePassiveSet.empty)
  ;;

  let pick_min_passive ~use_age (_,passives_w,passives_a) =
    if use_age then AgePassiveSet.min_elt passives_a
    else WeightPassiveSet.min_elt passives_w
  ;;

  let pick_min_g_passive ~use_age (passives_w,passives_a) =
    if use_age then AgePassiveSet.min_elt passives_a
    else WeightPassiveSet.min_elt passives_w
  ;;

  let mk_unit_clause bag maxvar (t,ty) =
    let c, maxvar = Utils.mk_unit_clause maxvar (B.embed ty) (B.embed t) in
    let bag, c = Terms.add_to_bag c bag in
    (bag, maxvar), c
  ;;

  let mk_clause bag maxvar (t,ty) =
    let (proof,ty) = B.saturate t ty in
    let c, maxvar = Utils.mk_unit_clause maxvar ty proof in
    let bag, c = Terms.add_to_bag c bag in
    (bag, maxvar), c
  ;;
  
  let mk_passive (bag,maxvar) = mk_clause bag maxvar;;

  let mk_goal (bag,maxvar) = mk_clause bag maxvar;;

  let initialize_goal (bag,maxvar,actives,passives,_,_) t = 
    let (bag,maxvar), g = mk_unit_clause bag maxvar t in
    let g_passives = g_passive_empty_set in
    (* if the goal is not an equation we returns an empty
       passive set *)
    let g_passives =
      if Terms.is_eq_clause g then add_passive_goal g_passives g
      else g_passives 
    in
      (bag,maxvar,actives,passives,[],g_passives)


  (* TODO : global age over facts and goals (without comparing weights) *)
  let select ~use_age passives g_passives =
    if is_passive_set_empty passives then begin
      if (is_passive_g_set_empty g_passives) then
        raise (Stop GaveUp) (* we say we are incomplete *)
      else
       let g_cl = pick_min_g_passive ~use_age:use_age g_passives in
        (true,g_cl,passives,remove_passive_goal g_passives g_cl)
    end
    else let cl = pick_min_passive ~use_age:use_age passives in
      if is_passive_g_set_empty g_passives then
        (false,cl,remove_passive_clause passives cl,g_passives)
      else
        let g_cl = pick_min_g_passive ~use_age:use_age g_passives in
	let (id1,_,_,_),(id2,_,_,_) = snd cl, snd g_cl in
	let cmp = if use_age then id1 <= id2
	else fst cl <= fst g_cl
	in
          if cmp then
            (false,cl,remove_passive_clause passives cl,g_passives)
          else
            (true,g_cl,passives,remove_passive_goal g_passives g_cl)
  ;;

  let backward_infer_step bag maxvar actives passives
                          g_actives g_passives g_current iterno =
    (* superposition left, simplifications on goals *)
      debug (lazy "infer_left step...");
      let bag, maxvar, new_goals = 
        Sup.infer_left bag maxvar g_current actives 
      in
        debug (lazy "Performed infer_left step");
	let bag = Terms.replace_in_bag (g_current,false,iterno) bag in
          bag, maxvar, actives, passives, g_current::g_actives,
    (add_passive_goals g_passives new_goals)
  ;;

  let pp_clauses actives passives =
    let actives_l, _ = actives in
    let passive_t,_,_ = passives in
    let wset = IDX.elems passive_t in
      ("Actives :" ^ (String.concat ";\n" 
	(List.map Pp.pp_unit_clause actives_l)))
      ^ 
      ("Passives:" ^(String.concat ";\n" 
        (List.map (fun (_,cl) -> Pp.pp_unit_clause cl)
	       (IDX.ClauseSet.elements wset))))
  ;;

  let forward_infer_step 
      ((bag,maxvar,actives,passives,g_actives,g_passives) as s)  
      current iterno =
    (* forward step *)
    
    (* e = select P           *
     * e' = demod A e         *
     * A' = demod [e'] A      *
     * A'' = A' + e'          *
     * e'' = fresh e'         *
     * new = supright e'' A'' *
     * new'= demod A'' new    *
     * P' = P + new'          *)
    debug (lazy ("Forward infer step for "^ (Pp.pp_unit_clause current)));
    debug (lazy("Number of actives : " ^ (string_of_int (List.length (fst actives)))));
    noprint (lazy (pp_clauses actives passives));
    let _ = noprint
      (lazy 
	 ("Actives before simplification:" ^ (String.concat ";\n" 
	    (List.map Pp.pp_unit_clause (fst actives))))) in 
    match Sup.keep_simplified current actives bag maxvar
    with
      | _,None -> debug(lazy("None")); s
      | bag,Some (current,actives) ->
    debug (lazy ("simplified to " ^ (Pp.pp_unit_clause current)));
    let _ = noprint
      (lazy 
	 ("Actives after simplification:" ^ (String.concat ";\n" 
	    (List.map Pp.pp_unit_clause (fst actives))))) in 
    let bag, maxvar, actives, new_clauses = 
      Sup.infer_right bag maxvar current actives 
    in
      debug
	(lazy 
	 ("New clauses :" ^ (String.concat ";\n" 
	    (List.map Pp.pp_unit_clause new_clauses)))); 
      debug (lazy "Demodulating goals with actives...");
      (* keep goals demodulated w.r.t. actives and check if solved *)
      let bag, g_actives = 
        List.fold_left 
          (fun (bag,acc) c -> 
             match 
               Sup.simplify_goal ~no_demod:false maxvar (snd actives) bag acc c
             with
               | None -> bag, acc
               | Some (bag,c1) -> bag,if c==c1 then c::acc else c::c1::acc)
          (bag,[]) g_actives 
      in
      let ctable = IDX.index_unit_clause IDX.DT.empty current in
      let bag, maxvar, new_goals = 
        List.fold_left 
          (fun (bag,m,acc) g -> 
             let bag, m, ng = Sup.infer_left bag m g ([current],ctable) in
               bag,m,ng@acc) 
          (bag,maxvar,[]) g_actives 
      in
      let bag = Terms.replace_in_bag (current,false,iterno) bag in
	(* prerr_endline (Pp.pp_bag bag); *)
    bag, maxvar, actives,
    add_passive_clauses passives new_clauses, g_actives,
    add_passive_goals g_passives new_goals
  ;;

  let debug_status (_,_,actives,passives,g_actives,g_passives) =
    lazy
      ((Printf.sprintf "Number of active goals : %d\n"
          (List.length g_actives)) ^
       (Printf.sprintf "Number of passive goals : %d\n"
          (g_passive_set_cardinal g_passives)) ^
       (Printf.sprintf "Number of actives : %d\n" 
	  (List.length (fst actives))) ^
       (Printf.sprintf "Number of passives : %d\n"
         (passive_set_cardinal passives)))
  ;;


  (* we just check if any of the active goals is subsumed by a
     passive clause, or if any of the passive goal is subsumed
     by an active or passive clause *) 
  let last_chance (bag,maxvar,actives,passives,g_actives,g_passives) =
    debug (lazy("Last chance " ^ string_of_float
		  (Unix.gettimeofday())));
    let actives_l, active_t = actives in
    let passive_t,wset,_ = passives in
    let _ = noprint
      (lazy 
	 ("Actives :" ^ (String.concat ";\n" 
	    (List.map Pp.pp_unit_clause actives_l)))) in 
    let wset = IDX.elems passive_t in
    let _ = noprint
      (lazy 
	 ("Passives:" ^(String.concat ";\n" 
	    (List.map (fun (_,cl) -> Pp.pp_unit_clause cl)
	       (IDX.ClauseSet.elements wset))))) in 
    let g_passives = 
      WeightPassiveSet.fold 
	(fun (_,x) acc ->
	  if List.exists (Sup.are_alpha_eq x) g_actives then acc
          else x::acc)
	  (fst g_passives) []
    in 
      ignore
      (List.iter
	(fun x -> 
	    ignore 
	     (debug (lazy("ckecking goal vs a: " ^ Pp.pp_unit_clause x));
               Sup.simplify_goal ~no_demod:true maxvar active_t bag [] x))
       g_passives); 
      ignore
      (List.iter
	 (fun x -> 
	    ignore 
	      (debug (lazy("ckecking goal vs p: " ^ Pp.pp_unit_clause x));
	Sup.simplify_goal ~no_demod:true maxvar passive_t bag [] x))
        (g_actives@g_passives)); 
    raise (Stop (Timeout (maxvar,bag)))

  let check_timeout = function
    | None -> false
    | Some timeout -> Unix.gettimeofday () > timeout
 
  let rec given_clause ~useage
    bag maxvar iterno weight_picks max_steps timeout 
    actives passives g_actives g_passives 
  =
    let iterno = iterno + 1 in
    if iterno = max_steps || check_timeout timeout then
      last_chance (bag,maxvar,actives,passives,g_actives,g_passives)
    else 
    let use_age = useage && (weight_picks = (iterno / 6 + 1)) in
    let weight_picks = if use_age then 0 else weight_picks+1
    in

    let rec aux_select bag 
	(passives:IDX.DT.t * WeightPassiveSet.t * AgePassiveSet.t)
	g_passives =
      let backward,(weight,current),passives,g_passives =
        select ~use_age passives g_passives
      in
	if use_age && weight > monster then
	  let bag,cl = Terms.add_to_bag current bag in
	    if backward then
	      aux_select bag passives (add_passive_goal g_passives cl)
	    else
	      aux_select bag (add_passive_clause passives cl) g_passives
	else
	  let bag = Terms.replace_in_bag (current,false,iterno) bag in
        if backward then
          let _ = debug (lazy("Selected goal : " ^ Pp.pp_unit_clause current)) in
         match 
           Sup.simplify_goal 
             ~no_demod:false maxvar (snd actives) bag g_actives current 
         with
           | None -> aux_select bag passives g_passives
           | Some (bag,g_current) ->
               backward_infer_step bag maxvar actives passives
                 g_actives g_passives g_current iterno
        else
          let _ = debug (lazy("Selected fact : " ^ Pp.pp_unit_clause current)) 
	  in
            if Sup.orphan_murder bag (fst actives) current then
	      let _ = debug (lazy "Orphan murdered") in
              let bag = Terms.replace_in_bag (current,true,iterno) bag in
		aux_select bag passives g_passives
            else
	      let s = bag,maxvar,actives,passives,g_actives,g_passives in
              let s1 = forward_infer_step s current iterno
	      in 
		if s == s1 then aux_select bag passives g_passives  
		else s1
    in
      (*prerr_endline "Active table :"; 
       (List.iter (fun x -> prerr_endline (Pp.pp_unit_clause x))
          (fst actives)); *)

    let (bag,maxvar,actives,passives,g_actives,g_passives) as status  =      
      aux_select bag passives g_passives
    in
      debug (debug_status status);       
      given_clause ~useage
        bag maxvar iterno weight_picks max_steps timeout 
        actives passives g_actives g_passives
  ;;

  let check_and_infer ~no_demod iterno status current =
    let bag,maxvar,actives,passives,g_actives,g_passives = status in
    match 
      Sup.simplify_goal 
        ~no_demod maxvar (snd actives) bag g_actives current 
    with
      | None -> debug (lazy "None"); status
      | Some (bag,g_current) -> 
	  let _ = 
	    debug (lazy("Infer on goal : " 
			^ Pp.pp_unit_clause g_current)) 
	  in
	    backward_infer_step bag maxvar actives passives
              g_actives g_passives g_current iterno

  (* similar to given_clause, but it merely works on goals, 
     in parallel, at each iteration *)
  let rec goal_narrowing iterno max_steps timeout status
  = 
    debug (debug_status status);
    let iterno = iterno + 1 in
    if iterno = max_steps || check_timeout timeout then
      last_chance status
    else 
    let _,_,_,_,_,g_passives = status in 
    let passive_goals = WeightPassiveSet.elements (fst g_passives) in
    let newstatus = 
      List.fold_left
	(fun acc g ->
	   let bag,maxvar,actives,passives,g_actives,g_passives = acc in
	   let g_passives =
	     remove_passive_goal g_passives g in
	   let current = snd g in
	   let _ = 
	     debug (lazy("Selected goal gn: " ^ Pp.pp_unit_clause current)) 
	   in
	     (* we work both on the original goal and the demodulated one*)
	   let acc = check_and_infer ~no_demod:false iterno acc current
	   in check_and_infer ~no_demod:true iterno acc current)
	status passive_goals
    in
      goal_narrowing iterno max_steps timeout newstatus

    let compute_result bag i subst =
      let l =
        let rec traverse ongoal (accg,acce) i =
          match Terms.get_from_bag i bag with
            | (id,_,_,Terms.Exact _),_,_ ->
                if ongoal then [i],acce else
                  if (List.mem i acce) then accg,acce else accg,acce@[i]
            | (_,_,_,Terms.Step (_,i1,i2,_,_,_)),_,_ ->
                if (not ongoal) && (List.mem i acce) then accg,acce
                else
                  let accg,acce = 
                    traverse false (traverse ongoal (accg,acce) i1) i2
                  in
                    if ongoal then i::accg,acce else accg,i::acce
        in
        let gsteps,esteps = traverse true ([],[]) i in
          (List.rev esteps)@gsteps
      in
      debug (lazy ("steps: " ^ (string_of_int (List.length l))));
      let max_w = 
	List.fold_left 
	  (fun acc i ->
	     let (cl,_,_) = Terms.get_from_bag i bag in
	       max acc (Order.compute_unit_clause_weight cl)) 0 l in
	debug (lazy ("Max weight : " ^ (string_of_int max_w)));
(*	  List.iter (fun id -> let ((_,lit,_,proof as cl),d,it) =
	    Terms.get_from_bag id bag in
	      if d then
		prerr_endline
		(Printf.sprintf "Id : %d, selected at %d, weight %d,disc, by %s"
		   id it (Order.compute_unit_clause_weight cl) 
		   (Pp.pp_proof_step proof))
	      else
	       prerr_endline
		(Printf.sprintf "Id : %d, selected at %d, weight %d by %s"
		   id it (Order.compute_unit_clause_weight cl) 
		   (Pp.pp_proof_step proof))) l;*)
        debug (lazy ("Proof:" ^
          (String.concat "\n" 
	     (List.map 
		(fun x ->
		   let cl,_,_ = Terms.get_from_bag x bag in
		     Pp.pp_unit_clause cl) l))));
        Unsatisfiable [ bag, i, subst, l ]

  let paramod ~useage ~max_steps ?timeout (bag,maxvar) ~g_passives ~passives =
    let _initial_timestamp = Unix.gettimeofday () in
    let passives =
      add_passive_clauses ~no_weight:true passive_empty_set passives
    in
    let g_passives =
      add_passive_goals ~no_weight:true g_passive_empty_set g_passives
    in
    let g_actives = [] in
    let actives = [], IDX.DT.empty in
    try 
     given_clause ~useage ~noinfer:false
      bag maxvar 0  0 max_steps timeout actives passives g_actives g_passives
    with 
    | Sup.Success (bag, _, (i,_,_,_),subst) ->
	compute_result bag i subst
    | Stop (Unsatisfiable _) -> Error "solution found!"
    | Stop o -> o
  ;;

let demod s goal =
  let bag,maxvar,actives,passives,g_actives,g_passives = s in
  let (bag,maxvar), g = mk_goal (bag,maxvar) goal in
  let bag, ((i,_,_,_) as g1) = Sup.demodulate bag g (snd actives) in
    if g1 = g then GaveUp else compute_result bag i []
(*
  if Terms.is_eq_clause g then 

  else GaveUp *)

let fast_eq_check s goal =
  let (_,_,_,_,_,g_passives) as s = initialize_goal s goal in
  if is_passive_g_set_empty g_passives then Error "not an equation"
  else
  try 
    goal_narrowing 0 2 None s
  with
    | Sup.Success (bag, _, (i,_,_,_),subst) ->
	compute_result bag i subst
    | Stop (Unsatisfiable _) -> Error "solution found!"
    | Stop o -> o
  ;;

let nparamod ~useage ~max_steps ?timeout s goal =
  let bag,maxvar,actives,passives,g_actives,g_passives
      = initialize_goal s goal in
  if is_passive_g_set_empty g_passives then Error "not an equation" 
  else
    try given_clause ~useage ~noinfer:false
      bag maxvar 0 0 max_steps timeout actives passives g_actives g_passives
  with
    | Sup.Success (bag, _, (i,_,_,_),subst) ->
	compute_result bag i subst
    | Stop (Unsatisfiable _) -> Error "solution found!"
    | Stop o -> o
  ;;

end
