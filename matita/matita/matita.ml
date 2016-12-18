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

(* $Id: matita.ml 12176 2012-07-26 14:53:37Z fguidi $ *)

open Printf

open MatitaGtkMisc
open GrafiteTypes

(** {2 Initialization} *)

let _ = 
  MatitaInit.add_cmdline_spec
    ["-tptppath", Arg.String
      (fun s -> Helm_registry.set_string "matita.tptppath" s),
      "Where to find the Axioms/ and Problems/ directory";
     "-elpi", Arg.String
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
  MatitaMisc.reset_font_size ()
;;

let _ =
  Predefined_virtuals.load_predefined_virtuals ();
  Predefined_virtuals.load_predefined_classes ()
;;
  
  (** {{{ Debugging *)
let init_debugging_menu gui =
  if BuildTimeConf.debug ||
     Helm_registry.get_bool "matita.debug_menu" 
  then begin
    gui#main#debugMenu#misc#show ();
    let addDebugItem label callback =
      let item =
        GMenu.menu_item ~packing:gui#main#debugMenu_menu#append ~label () in
      ignore (item#connect#activate callback) 
    in
    let addDebugCheckbox label ?(init=false) callback =
      let item =
        GMenu.check_menu_item 
          ~packing:gui#main#debugMenu_menu#append ~label () in
      item#set_active init;
      ignore (item#connect#toggled (callback item)) 
    in
    let addDebugSeparator () =
      ignore (GMenu.separator_item ~packing:gui#main#debugMenu_menu#append ())
    in
    addDebugItem "dump aliases" (fun _ ->
      let status = (MatitaScript.current ())#status in
      GrafiteDisambiguate.dump_aliases prerr_endline "" status);
(* FG: DEBUGGING   
    addDebugItem "dump interpretations" (fun _ ->
      let status = script#lexicon_status in
      let filter = 
       List.filter (function LexiconAst.Interpretation _ -> true | _ -> false)
      in
      HLog.debug (String.concat "\n"
       (List.fold_right
         (fun x l -> (LexiconAstPp.pp_command x)::l)
         (filter status.LexiconEngine.lexicon_content_rev) [])));
*)
    addDebugSeparator ();
    addDebugCheckbox "high level pretty printer" ~init:true
      (fun mi () -> ApplyTransformation.use_high_level_pretty_printer := mi#active);
    addDebugSeparator ();
    addDebugCheckbox "prune errors"
      (fun mi () -> MatitaGui.all_disambiguation_passes := not (mi#active));
    (*MATITA 1.0: ??? addDebugItem "prune disambiguation errors"
      (fun _ -> MatitaGui.all_disambiguation_passes := false);*)
    addDebugCheckbox "multiple disambiguation passes" ~init:true
      (fun mi () -> MultiPassDisambiguator.only_one_pass := mi#active);
    addDebugSeparator ();
    addDebugCheckbox "tactics logging" 
      (fun mi () -> NTacStatus.debug := mi#active);
    addDebugCheckbox "disambiguation logging"
      (fun mi () -> MultiPassDisambiguator.debug := mi#active; NCicDisambiguate.debug := mi#active);
    addDebugCheckbox "disambiguation/refiner/unification/metasubst logging"
      (fun mi () -> NCicRefiner.debug := mi#active; NCicUnification.debug :=
              mi#active; MultiPassDisambiguator.debug := mi#active; NCicDisambiguate.debug := mi#active; NCicMetaSubst.debug := mi#active);
    addDebugCheckbox "reduction logging"
      (fun mi () -> NCicReduction.debug := mi#active);
    addDebugSeparator ();
    addDebugItem "Expand virtuals"
    (fun _ -> (MatitaScript.current ())#expandAllVirtuals);
  end
  (** Debugging }}} *)

  (** {2 Main} *)

let _ =
  at_exit (fun () -> print_endline "\nThanks for using Matita!\n");
  Sys.catch_break true;
  let args = Helm_registry.get_list Helm_registry.string "matita.args" in
  let gui = MatitaGui.instance () in
  init_debugging_menu gui;
  List.iter gui#loadScript (List.rev args);
  gui#main#mainWin#show ();
  try
   GtkThread.main ()
  with Sys.Break -> ()
;;

(* vim:set foldmethod=marker: *)
