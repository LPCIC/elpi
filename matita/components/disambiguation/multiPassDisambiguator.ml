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

(* $Id: multiPassDisambiguator.ml 10958 2010-09-30 12:32:10Z tassi $ *)

open Printf

let debug = ref false;;
let debug_print s =
 if !debug then prerr_endline (Lazy.force s) else ();;

exception DisambiguationError of
 int *
 ((Stdpp.location list * string * string) list *
  (DisambiguateTypes.domain_item * string) list * 
  (Stdpp.location * string) Lazy.t * bool) list list
  (** parameters are: option name, error message *)

(* implement module's API *)

let only_one_pass = ref false;;
let use_library = ref false;;

let passes () = (* <fresh_instances?, aliases, coercions?> *)
 if !only_one_pass then
  [ (true, `Mono, false) ]
 else if !use_library then
  [ (true, `Library, false); 
      (* for demo to reduce the number of interpretations *)
    (true, `Library, true);
  ]
 else if !debug then
  [ (true, `Multi, true); ]
 else
  [ (true, `Mono, false);
    (true, `Multi, false);
    (true, `Mono, true);
    (true, `Multi, true);
  ]
;;

let drop_aliases ?(minimize_instances=false) ~description_of_alias
 (choices, user_asked)
=
 let module D = DisambiguateTypes in
 let compare ci1 ci2 = description_of_alias ci1 = description_of_alias ci2 in
 let minimize d =
  if not minimize_instances then
   d
  else
   let rec aux =
    function
       [] -> []
     | (D.Symbol (s,n),ci1) as he::tl when n > 0 ->
         if
          List.for_all
           (function
               (D.Symbol (s2,_),ci2) -> s2 <> s || compare ci1 ci2
             | _ -> true
           ) d
         then
          (D.Symbol (s,0),ci1)::(aux tl)
         else
          he::(aux tl)
     | (D.Num n,ci1) as he::tl when n > 0 ->
         if
          List.for_all
           (function (D.Num _,ci2) -> compare ci1 ci2 | _ -> true) d
         then
          (D.Num 0,ci1)::(aux tl)
         else
          he::(aux tl)
      | he::tl -> he::(aux tl)
   in
    aux d
 in
  (List.map (fun (d, a, b, c, e) -> minimize d, a, b, c, e) choices),
  user_asked

let drop_aliases_and_clear_diff (choices, user_asked) =
  (List.map (fun (_, a, b, c, d) -> [], a, b, c, d) choices),
  user_asked

let disambiguate_thing ~description_of_alias ~passes ~aliases ~universe ~f thing
=
  assert (universe <> None);
  let library = false, DisambiguateTypes.Environment.empty, None in
  let multi_aliases = false, DisambiguateTypes.Environment.empty, universe in
  let mono_aliases = true, aliases, Some DisambiguateTypes.Environment.empty in
  let passes =
    List.map
     (function (fresh_instances,env,use_coercions) ->
       fresh_instances,
       (match env with `Mono -> mono_aliases | `Multi -> multi_aliases |
       `Library -> library),
       use_coercions) passes in
  let try_pass (fresh_instances, (_, aliases, universe), use_coercions) =
    f ~fresh_instances ~aliases ~universe ~use_coercions thing
  in
  let set_aliases (instances,(use_mono_aliases,_,_),_) (_, user_asked as res) =
   if use_mono_aliases then
    drop_aliases ~minimize_instances:true ~description_of_alias res (* one shot aliases *)
   else if user_asked then
    drop_aliases ~minimize_instances:true ~description_of_alias res (* one shot aliases *)
   else
    drop_aliases_and_clear_diff res
  in
  let rec aux i errors passes =
  debug_print (lazy ("Pass: " ^ string_of_int i));
   match passes with
      [ pass ] ->
        (try
          set_aliases pass (try_pass pass)
         with Disambiguate.NoWellTypedInterpretation (offset,newerrors) ->
          raise (DisambiguationError (offset, errors @ [newerrors])))
    | hd :: tl ->
        (try
          set_aliases hd (try_pass hd)
        with Disambiguate.NoWellTypedInterpretation (_offset,newerrors) ->
         aux (i+1) (errors @ [newerrors]) tl)
    | [] -> assert false
  in
   aux 1 [] passes
;;

let disambiguate_thing ~passes ~freshen_thing ~context ~metasenv ~subst
  ~string_context_of_context ~initial_ugraph ~expty ~mk_implicit
  ~description_of_alias ~fix_instance ~aliases ~universe ~lookup_in_library
  ~uri ~pp_thing ~domain_of_thing ~interpretate_thing ~refine_thing
  ~mk_localization_tbl thing
 =
  let f ~fresh_instances ~aliases ~universe ~use_coercions (txt,len,thing) =
    let thing = if fresh_instances then freshen_thing thing else thing in
     Disambiguate.disambiguate_thing
      ~context ~metasenv ~subst ~use_coercions ~string_context_of_context
      ~initial_ugraph ~expty ~mk_implicit ~description_of_alias ~fix_instance
      ~aliases ~universe ~lookup_in_library 
      ~uri ~pp_thing ~domain_of_thing ~interpretate_thing ~refine_thing 
      ~mk_localization_tbl (txt,len,thing)
  in
  disambiguate_thing ~description_of_alias ~passes ~aliases
   ~universe ~f thing
