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

(* $Id: matitac.ml 13023 2015-02-04 16:55:03Z fguidi $ *)

(* compiler ala pascal/java using make *)
let main_compiler () =
  MatitaInit.add_cmdline_spec
    ["-elpi", Arg.String
      NCicELPI.set_kernel_from_string,
      "the prolog kernel to use: NO, CSC, FG0, FG1";
     "-elpi-trace", Arg.Unit
      NCicELPI.trace_on,
      "turn on prolog query tracing";
     "-elpi-quiet", Arg.Unit
      NCicELPI.prints_off,
      "turn off prolog informational prints";
     "-elpi-cache", Arg.Unit
      NCicELPI.cache_on,
      "turn on prolog query caching";
    ];
  MatitaInit.initialize_all ();
  (* targets and deps *)
  let targets = Helm_registry.get_list Helm_registry.string "matita.args" in
  let targets = 
    match targets with
    | [] ->
      (match Librarian.find_roots_in_dir (Sys.getcwd ()) with
      | [x] ->
         let root = Filename.dirname x in
          HExtlib.find ~test:(fun path -> Filename.check_suffix path ".ma") root
      | [] -> 
         prerr_endline "No targets and no root found"; exit 1
      | roots -> 
         let roots = List.map (HExtlib.chop_prefix (Sys.getcwd()^"/")) roots in
         prerr_endline ("Too many roots found:\n\t" ^ String.concat "\n\t" roots);
         prerr_endline ("\nEnter one of these directories and retry");
         exit 1);
    | _ ->
      let map targets file =
          if HExtlib.is_dir file then
             let files = HExtlib.find ~test:(fun path -> Filename.check_suffix path ".ma") file in
             files @ targets
          else file :: targets
      in
      List.fold_left map [] (List.rev targets)
  in
  (* must be called after init since args are set by cmdline parsing *)
  let system_mode =  Helm_registry.get_bool "matita.system" in
  if system_mode then HLog.message "Compiling in system space";
  (* here we go *)
  if not (Helm_registry.get_bool "matita.verbose") then MatitaMisc.shutup ();
  if List.fold_left
   (fun b t ->
     (try
       ignore (MatitaEngine.assert_ng ~include_paths:[] t); true
      with
       MatitaEngine.FailureCompiling (_,exn) ->
        HLog.error (snd (MatitaExcPp.to_string exn)); false) && b
   ) true targets
  then 
    (HLog.message "Compilation successful"; 0)
  else
    (HLog.message "Compilation failed"; 1)
;;

let main () =
  Sys.catch_break true;
  let bin = Filename.basename Sys.argv.(0) in
  if Pcre.pmatch ~pat:"^matitaclean"  bin then Matitaclean.main ()
  else exit (main_compiler ())
;;

let _ = main ()

