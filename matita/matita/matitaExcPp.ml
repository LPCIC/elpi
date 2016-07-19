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

(* $Id: matitaExcPp.ml 11304 2011-06-03 08:53:47Z sacerdot $ *)

open Printf

let compact_disambiguation_errors all_passes errorll =
  let choices =
   List.flatten
    (List.map
      (fun (pass,l) ->
        List.map
         (fun (env,diff,offset_msg,significant) ->
           let offset, msg = Lazy.force offset_msg in
           offset, [[pass], [[pass], env, diff], lazy msg, significant]) l
      ) errorll) in
  (* Here we are doing a stable sort and list_uniq returns the latter
     "equal" element. I.e. we are showing the error corresponding to the
     most advanced disambiguation pass *)
  let choices =
   let choices_compare (o1,_) (o2,_) = compare o1 o2 in
   let choices_compare_by_passes (p1,_,_,_) (p2,_,_,_) =
    compare p1 p2 in
   let rec uniq =
    function
       [] -> []
     | h::[] -> [h]
     | (o1,res1)::(o2,res2)::tl when o1 = o2 ->
        let merge_by_name errors =
         let merge_by_env errors =
          let choices_compare_by_env (_,e1,_) (_,e2,_) = compare e1 e2 in
          let choices_compare_by_passes (p1,_,_) (p2,_,_) =
           compare p1 p2 in
          let rec uniq_by_env =
           function
              [] -> []
            | h::[] -> [h]
            | (p1,e1,_)::(p2,e2,d2)::tl when e1 = e2 ->
                uniq_by_env ((p1@p2,e2,d2) :: tl) 
            | h1::tl -> h1 :: uniq_by_env tl
          in
           List.sort choices_compare_by_passes
            (uniq_by_env (List.stable_sort choices_compare_by_env errors))
         in
         let choices_compare_by_msg (_,_,m1,_) (_,_,m2,_) =
          compare (Lazy.force m1) (Lazy.force m2) in
         let rec uniq_by_msg =
          function
             [] -> []
           | h::[] -> [h]
           | (p1,i1,m1,s1)::(p2,i2,m2,s2)::tl
             when Lazy.force m1 = Lazy.force m2 && s1 = s2 ->
               uniq_by_msg ((p1@p2,merge_by_env (i1@i2),m2,s2) :: tl)
           | h1::tl -> h1 :: uniq_by_msg tl
         in
          List.sort choices_compare_by_msg
           (uniq_by_msg (List.stable_sort choices_compare_by_msg errors))
        in
         let res = merge_by_name (res1@res2) in
          uniq ((o1,res) :: tl)
     | h1::tl -> h1 :: uniq tl
   in
   (* Errors in phase 3 that are not also in phase 4 are filtered out *)
   let filter_phase_3 choices =
    if all_passes then choices
    else
     let filter =
      HExtlib.filter_map
       (function
           (loffset,messages) ->
              let filtered_messages =
               HExtlib.filter_map
                (function
                    [3],_,_,_ -> None
                  | item -> Some item
                ) messages
              in
               if filtered_messages = [] then
                None
               else
                Some (loffset,filtered_messages))
     in
      filter choices
   in
    filter_phase_3
     (List.map (fun o,l -> o,List.sort choices_compare_by_passes l)
       (uniq (List.stable_sort choices_compare choices)))
  in
   choices
;;

let rec to_string exn =
 try
  (match exn with
    HExtlib.Localized (floc,exn) ->
      let _,msg = to_string exn in
      let (x, y) = HExtlib.loc_of_floc floc in
       Some floc, sprintf "Error at %d-%d: %s" x y msg
  | NCicLibrary.IncludedFileNotCompiled (s1,s2) ->
      None, "Including: "^s1^" "^s2^ "\nNothing to do... did you run matitadep?"
  | GrafiteTypes.Command_error msg -> None, "Error: " ^ msg
  | CicNotationParser.Parse_error err ->
      None, sprintf "Parse error: %s" err
  | Unix.Unix_error (code, api, param) ->
      let err = Unix.error_message code in
      None, "Unix Error (" ^ api ^ "): " ^ err
  | HMarshal.Corrupt_file fname -> None, sprintf "file '%s' is corrupt" fname
  | HMarshal.Format_mismatch fname
  | HMarshal.Version_mismatch fname ->
      None,
      sprintf "format/version mismatch for file '%s', please recompile it'"
        fname
  | Continuationals.Error s -> None, "Tactical error: " ^ Lazy.force s
  | NCicRefiner.RefineFailure msg ->
     None, "NRefiner failure: " ^ snd (Lazy.force msg)
  | NCicRefiner.Uncertain msg ->
     None, "NRefiner uncertain: " ^ snd (Lazy.force msg)
  | NCicMetaSubst.Uncertain msg ->
     None, "NCicMetaSubst uncertain: " ^ Lazy.force msg
  | NCicMetaSubst.MetaSubstFailure msg ->
     None, "NCicMetaSubst failure: " ^ Lazy.force msg
  | NCicTypeChecker.TypeCheckerFailure msg ->
     None, "NTypeChecker failure: " ^ Lazy.force msg
  | NCicTypeChecker.AssertFailure msg ->
     None, "NTypeChecker assert failure: " ^ Lazy.force msg
  | NCicEnvironment.ObjectNotFound msg ->
     None, "NCicEnvironment object not found: " ^ Lazy.force msg
  | NCicEnvironment.AlreadyDefined msg ->
     None, "NCicEnvironment already defined: " ^ Lazy.force msg
  | MatitaEngine.CircularDependency fname ->
      None, "Circular dependency including " ^ fname
  | MatitaEngine.TryingToAdd msg ->
     None, "Attempt to insert an alias in batch mode: " ^ Lazy.force msg
  | MatitaEngine.AlreadyLoaded msg ->
     None, "The file " ^ Lazy.force msg ^ " needs recompilation but it is
     already loaded; undo the inclusion and try again."
  | MatitaEngine.FailureCompiling (filename,exn) ->
     None, "Compiling " ^ filename ^ ":\n" ^ snd (to_string exn)
  | NCicRefiner.AssertFailure msg ->
     None, "NRefiner assert failure: " ^ Lazy.force msg
  | NCicEnvironment.BadDependency (msg,e) ->
     None, "NCicEnvironment bad dependency: " ^ Lazy.force msg ^ 
     snd (to_string e)
  | NCicEnvironment.BadConstraint msg ->
     None, "NCicEnvironment bad constraint: " ^ Lazy.force msg
  | NCicUnification.UnificationFailure msg ->
     None, "NCicUnification failure: " ^ Lazy.force msg
  | NCicUnification.Uncertain msg ->
     None, "NCicUnification uncertain: " ^ Lazy.force msg
  | DisambiguateChoices.Choice_not_found msg ->
     None, ("Disambiguation choice not found: " ^ Lazy.force msg)
  | DisambiguateTypes.Invalid_choice msg ->
     None, ("Invalid choice: " ^ snd (Lazy.force msg))
  | MatitaEngine.EnrichedWithStatus (exn,_) ->
     None, snd(to_string exn)
  | NTacStatus.Error (msg,None) ->
     None, "NTactic error: " ^ Lazy.force msg 
  | NTacStatus.Error (msg,Some exn) ->
     None, "NTactic error: " ^ Lazy.force msg ^ "\n" ^ snd(to_string exn)
  | MultiPassDisambiguator.DisambiguationError (offset,errorll) ->
     let loc =
      match errorll with
        | ((_,_,loc_msg,_)::_)::_ ->
          let floc, _ = Lazy.force loc_msg in
          if floc = Stdpp.dummy_loc then None else
            let (x, y) = HExtlib.loc_of_floc floc in
            let x = x + offset in
            let y = y + offset in
            let floc = HExtlib.floc_of_loc (x,y) in
             Some floc
        | _ -> assert false
     in
     let annotated_errorll =
      List.rev
       (snd
         (List.fold_left (fun (pass,res) item -> pass+1,(pass+1,item)::res)
           (0,[]) errorll)) in
     let choices = compact_disambiguation_errors true annotated_errorll in
     let errorll =
      (List.map
       (function (loffset,l) ->
         List.map
          (function
            passes,envs_and_diffs,msg,significant ->
             let _,env,diff = List.hd envs_and_diffs in
              passes,env,diff,loffset,msg,significant
          ) l
        ) choices) in
     let rec aux =
      function
         [] -> []
       | phase::tl ->
          let msg =
            (List.map (fun (passes,_,_,floc,msg,significant) ->
              let loc_descr =
                if floc = HExtlib.dummy_floc then "" 
                else 
                  let (x, y) = HExtlib.loc_of_floc floc in
                  sprintf " at %d-%d" (x+offset) (y+offset)
              in
               "*" ^ (if not significant then "(Spurious?) " else "")
               ^ "Error" ^ loc_descr ^ ": " ^ Lazy.force msg,
             passes) phase)
          in
           msg@aux tl in
     let rec explain =
      function
         [] -> ""
       | (msg,phases)::tl ->
           explain tl ^
           "***** Errors obtained during phase" ^
            (if phases = [] then " " else "s ") ^
            String.concat "," (List.map string_of_int phases) ^": *****\n"^
            msg ^ "\n\n"
     in
      loc,
       "********** DISAMBIGUATION ERRORS: **********\n" ^
        explain (aux errorll)
  | exn -> None, ("Uncaught exception: " ^ Printexc.to_string exn ^ Printexc.get_backtrace ()))
 with exn ->
  None, ("Exception raised during pretty-printing of an exception: " ^
   snd (to_string exn))
