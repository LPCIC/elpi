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

(* $Id: matitaGui.ml 12574 2013-04-08 12:20:15Z sacerdot $ *)

open Printf

open MatitaGeneratedGui
open MatitaGtkMisc
open MatitaMisc

exception Found of int

let all_disambiguation_passes = ref false

(* this is a shit and should be changed :-{ *)
let interactive_uri_choice
  ?(selection_mode:[`SINGLE|`MULTIPLE] = `MULTIPLE) ?(title = "")
  ?(msg = "") ?(nonvars_button = false) ?(hide_uri_entry=false) 
  ?(hide_try=false) ?(ok_label="_Auto") ?(ok_action:[`SELECT|`AUTO] = `AUTO) 
  ?copy_cb ()
  ~id uris
=
  if (selection_mode <> `SINGLE) &&
    (Helm_registry.get_opt_default Helm_registry.get_bool ~default:true "matita.auto_disambiguation")
  then
    uris
  else begin
    let dialog = new uriChoiceDialog () in
    if hide_uri_entry then
      dialog#uriEntryHBox#misc#hide ();
    if hide_try then
      begin
      dialog#uriChoiceSelectedButton#misc#hide ();
      dialog#uriChoiceConstantsButton#misc#hide ();
      end;
    dialog#okLabel#set_label ok_label;  
    dialog#uriChoiceTreeView#selection#set_mode
      (selection_mode :> Gtk.Tags.selection_mode);
    let model = new stringListModel dialog#uriChoiceTreeView in
    let choices = ref None in
    (match copy_cb with
    | None -> ()
    | Some cb ->
        dialog#copyButton#misc#show ();
        connect_button dialog#copyButton 
        (fun _ ->
          match model#easy_selection () with
          | [u] -> (cb u)
          | _ -> ()));
    dialog#uriChoiceDialog#set_title title;
    dialog#uriChoiceLabel#set_text msg;
    List.iter model#easy_append (List.map NReference.string_of_reference uris);
    dialog#uriChoiceConstantsButton#misc#set_sensitive nonvars_button;
    let return v =
      choices := v;
      dialog#uriChoiceDialog#destroy ();
      GMain.Main.quit ()
    in
    ignore (dialog#uriChoiceDialog#event#connect#delete (fun _ -> true));
    connect_button dialog#uriChoiceConstantsButton (fun _ ->
      return (Some uris));
    if ok_action = `AUTO then
      connect_button dialog#uriChoiceAutoButton (fun _ ->
        Helm_registry.set_bool "matita.auto_disambiguation" true;
        return (Some uris))
    else
      connect_button dialog#uriChoiceAutoButton (fun _ ->
        match model#easy_selection () with
        | [] -> ()
        | uris -> return (Some (List.map NReference.reference_of_string uris)));
    connect_button dialog#uriChoiceSelectedButton (fun _ ->
      match model#easy_selection () with
      | [] -> ()
      | uris -> return (Some (List.map NReference.reference_of_string uris)));
    connect_button dialog#uriChoiceAbortButton (fun _ -> return None);
    dialog#uriChoiceDialog#show ();
    GtkThread.main ();
    (match !choices with 
    | None -> raise MatitaTypes.Cancel
    | Some uris -> uris)
  end


class console ~(buffer: GText.buffer) () =
  object (self)
    val error_tag   = buffer#create_tag [ `FOREGROUND "red" ]
    val warning_tag = buffer#create_tag [ `FOREGROUND "orange" ]
    val message_tag = buffer#create_tag []
    val debug_tag   = buffer#create_tag [ `FOREGROUND "#888888" ]
    method message s = buffer#insert ~iter:buffer#end_iter ~tags:[message_tag] s
    method error s   = buffer#insert ~iter:buffer#end_iter ~tags:[error_tag] s
    method warning s = buffer#insert ~iter:buffer#end_iter ~tags:[warning_tag] s
    method debug s   = buffer#insert ~iter:buffer#end_iter ~tags:[debug_tag] s
    method clear () =
      buffer#delete ~start:buffer#start_iter ~stop:buffer#end_iter
    method log_callback (tag: HLog.log_tag) s =
      let s = Pcre.replace ~pat:"\\[0;3.m([^]+)\\[0m" ~templ:"$1" s in
      match tag with
      | `Debug -> self#debug (s ^ "\n")
      | `Error -> self#error (s ^ "\n")
      | `Message -> self#message (s ^ "\n")
      | `Warning -> self#warning (s ^ "\n")
  end
        
let clean_current_baseuri status = 
  LibraryClean.clean_baseuris [status#baseuri]

let save_moo0 ~do_clean script status = 
  let baseuri = status#baseuri in
  match script#bos, script#eos with
  | true, _ -> ()
  | _, true ->
     GrafiteTypes.Serializer.serialize ~baseuri:(NUri.uri_of_string baseuri)
      status
  | _ -> if do_clean then clean_current_baseuri status 
;;

let save_moo status = 
 let script = MatitaScript.current () in
  save_moo0 ~do_clean:true script status
;;
    
let ask_unsaved parent filename =
  MatitaGtkMisc.ask_confirmation 
    ~parent ~title:"Unsaved work!" 
    ~message:("Script <b>" ^ filename ^ "</b> is modified.!\n\n"^
         "<i>Do you want to save the script before continuing?</i>")
    ()

class interpErrorModel =
  let cols = new GTree.column_list in
  let id_col = cols#add Gobject.Data.string in
  let dsc_col = cols#add Gobject.Data.string in
  let interp_no_col = cols#add Gobject.Data.caml in
  let tree_store = GTree.tree_store cols in
  let id_renderer = GTree.cell_renderer_text [], ["text", id_col] in
  let dsc_renderer = GTree.cell_renderer_text [], ["text", dsc_col] in
  let id_view_col = GTree.view_column ~renderer:id_renderer () in
  let dsc_view_col = GTree.view_column ~renderer:dsc_renderer () in
  fun (tree_view: GTree.view) choices ->
    object
      initializer
        tree_view#set_model (Some (tree_store :> GTree.model));
        ignore (tree_view#append_column id_view_col);
        ignore (tree_view#append_column dsc_view_col);
        tree_store#clear ();
        let idx1 = ref ~-1 in
        List.iter
          (fun _,lll ->
            incr idx1;
            let loc_row =
             if List.length choices = 1 then
              None
             else
              (let loc_row = tree_store#append () in
                begin
                 match lll with
                    [passes,envs_and_diffs,_,_] ->
                      tree_store#set ~row:loc_row ~column:id_col
                       ("Error location " ^ string_of_int (!idx1+1) ^
                        ", error message " ^ string_of_int (!idx1+1) ^ ".1" ^
                        " (in passes " ^
                        String.concat " " (List.map string_of_int passes) ^
                        ")");
                      tree_store#set ~row:loc_row ~column:interp_no_col
                       (!idx1,Some 0,None);
                  | _ ->
                    tree_store#set ~row:loc_row ~column:id_col
                     ("Error location " ^ string_of_int (!idx1+1));
                    tree_store#set ~row:loc_row ~column:interp_no_col
                     (!idx1,None,None);
                end ;
                Some loc_row) in
            let idx2 = ref ~-1 in
             List.iter
              (fun passes,envs_and_diffs,_,_ ->
                incr idx2;
                let msg_row =
                 if List.length lll = 1 then
                  loc_row
                 else
                  let msg_row = tree_store#append ?parent:loc_row () in
                   (tree_store#set ~row:msg_row ~column:id_col
                     ("Error message " ^ string_of_int (!idx1+1) ^ "." ^
                      string_of_int (!idx2+1) ^
                      " (in passes " ^
                      String.concat " " (List.map string_of_int passes) ^
                      ")");
                    tree_store#set ~row:msg_row ~column:interp_no_col
                     (!idx1,Some !idx2,None);
                    Some msg_row) in
                let idx3 = ref ~-1 in
                List.iter
                 (fun (passes,env,_) ->
                   incr idx3;
                   let interp_row =
                    match envs_and_diffs with
                       _::_::_ ->
                        let interp_row = tree_store#append ?parent:msg_row () in
                        tree_store#set ~row:interp_row ~column:id_col
                          ("Interpretation " ^ string_of_int (!idx3+1) ^
                           " (in passes " ^
                           String.concat " " (List.map string_of_int passes) ^
                           ")");
                        tree_store#set ~row:interp_row ~column:interp_no_col
                         (!idx1,Some !idx2,Some !idx3);
                        Some interp_row
                     | [_] -> msg_row
                     | [] -> assert false
                   in
                    List.iter
                     (fun (_, id, dsc) ->
                       let row = tree_store#append ?parent:interp_row () in
                       tree_store#set ~row ~column:id_col id;
                       tree_store#set ~row ~column:dsc_col dsc;
                       tree_store#set ~row ~column:interp_no_col
                        (!idx1,Some !idx2,Some !idx3)
                     ) env
                 ) envs_and_diffs
              ) lll ;
             if List.length lll > 1 then
              HExtlib.iter_option
               (fun p -> tree_view#expand_row (tree_store#get_path p))
               loc_row
          ) choices

      method get_interp_no tree_path =
        let iter = tree_store#get_iter tree_path in
        tree_store#get ~row:iter ~column:interp_no_col
    end

exception UseLibrary;;

let interactive_error_interp ~all_passes
  (source_buffer:GSourceView2.source_buffer) notify_exn offset errorll filename
= 
  (* hook to save a script for each disambiguation error *)
  if false then
   (let text =
     source_buffer#get_text ~start:source_buffer#start_iter
      ~stop:source_buffer#end_iter () in
    let md5 = Digest.to_hex (Digest.string text) in
    let filename =
     Filename.chop_extension filename ^ ".error." ^ md5 ^ ".ma"  in
    let ch = open_out filename in
     output_string ch text;
    close_out ch
   );
  assert (List.flatten errorll <> []);
  let errorll' =
   let remove_non_significant =
     List.filter (fun (_env,_diff,_loc_msg,significant) -> significant) in
   let annotated_errorll () =
    List.rev
     (snd
       (List.fold_left (fun (pass,res) item -> pass+1,(pass+1,item)::res) (0,[])
         errorll)) in
   if all_passes then annotated_errorll () else
     let safe_list_nth l n = try List.nth l n with Failure _ -> [] in
    (* We remove passes 1,2 and 5,6 *)
     let res =
      (1,[])::(2,[])
      ::(3,remove_non_significant (safe_list_nth errorll 2))
      ::(4,remove_non_significant (safe_list_nth errorll 3))
      ::(5,[])::(6,[])::[]
     in
      if List.flatten (List.map snd res) <> [] then res
      else
       (* all errors (if any) are not significant: we keep them *)
       let res =
        (1,[])::(2,[])
        ::(3,(safe_list_nth errorll 2))
        ::(4,(safe_list_nth errorll 3))
        ::(5,[])::(6,[])::[]
       in
        if List.flatten (List.map snd res) <> [] then
	 begin
          HLog.warn
	   "All disambiguation errors are not significant. Showing them anyway." ;
	  res
	 end
	else
         begin
          HLog.warn
	   "No errors in phases 2 and 3. Showing all errors in all phases" ;
          annotated_errorll ()
         end
   in
  let choices = MatitaExcPp.compact_disambiguation_errors all_passes errorll' in
   match choices with
      [] -> assert false
    | [loffset,[_,envs_and_diffs,msg,significant]] ->
        let _,env,diff = List.hd envs_and_diffs in
         notify_exn
          (MultiPassDisambiguator.DisambiguationError
            (offset,[[env,diff,lazy (loffset,Lazy.force msg),significant]]));
    | _::_ ->
       let dialog = new disambiguationErrors () in
       if all_passes then
        dialog#disambiguationErrorsMoreErrors#misc#set_sensitive false;
       let model = new interpErrorModel dialog#treeview choices in
       dialog#disambiguationErrors#set_title "Disambiguation error";
       dialog#disambiguationErrorsLabel#set_label
        "Click on an error to see the corresponding message:";
       ignore (dialog#treeview#connect#cursor_changed
        (fun _ ->
          let tree_path =
           match fst (dialog#treeview#get_cursor ()) with
              None -> assert false
           | Some tp -> tp in
          let idx1,idx2,idx3 = model#get_interp_no tree_path in
          let loffset,lll = List.nth choices idx1 in
          let _,envs_and_diffs,msg,significant =
           match idx2 with
              Some idx2 -> List.nth lll idx2
            | None ->
                [],[],lazy "Multiple error messages. Please select one.",true
          in
          let _,env,diff =
           match idx3 with
              Some idx3 -> List.nth envs_and_diffs idx3
            | None -> [],[],[] (* dymmy value, used *) in
          let script = MatitaScript.current () in
          let error_tag = script#error_tag in
           source_buffer#remove_tag error_tag
             ~start:source_buffer#start_iter
             ~stop:source_buffer#end_iter;
           notify_exn
            (MultiPassDisambiguator.DisambiguationError
              (offset,[[env,diff,lazy(loffset,Lazy.force msg),significant]]))
           ));
       let return _ =
         dialog#disambiguationErrors#destroy ();
         GMain.Main.quit ()
       in
       let fail _ = return () in
       ignore(dialog#disambiguationErrors#event#connect#delete (fun _ -> true));
       connect_button dialog#disambiguationErrorsOkButton
        (fun _ ->
          let tree_path =
           match fst (dialog#treeview#get_cursor ()) with
              None -> assert false
           | Some tp -> tp in
          let idx1,idx2,idx3 = model#get_interp_no tree_path in
          let diff =
           match idx2,idx3 with
              Some idx2, Some idx3 ->
               let _,lll = List.nth choices idx1 in
               let _,envs_and_diffs,_,_ = List.nth lll idx2 in
               let _,_,diff = List.nth envs_and_diffs idx3 in
                diff
            | _,_ -> assert false
          in
           let newtxt =
            String.concat "\n"
             ("" ::
               List.map
                (fun k,desc -> 
                  let alias =
                   match k with
                   | DisambiguateTypes.Id id ->
                       GrafiteAst.Ident_alias (id, desc)
                   | DisambiguateTypes.Symbol (symb, i)-> 
                       GrafiteAst.Symbol_alias (symb, i, desc)
                   | DisambiguateTypes.Num i ->
                       GrafiteAst.Number_alias (i, desc)
                  in
                   GrafiteAstPp.pp_alias alias)
                diff) ^ "\n"
           in
            source_buffer#insert
             ~iter:
               (source_buffer#get_iter_at_mark
                (`NAME "beginning_of_statement")) newtxt ;
            return ()
        );
       connect_button dialog#disambiguationErrorsMoreErrors
        (fun _ -> return () ; raise UseLibrary);
       connect_button dialog#disambiguationErrorsCancelButton fail;
       dialog#disambiguationErrors#show ();
       GtkThread.main ()


class gui () =
    (* creation order _is_ relevant for windows placement *)
  let main = new mainWin () in
  let sequents_viewer =
   MatitaMathView.sequentsViewer_instance main#sequentsNotebook in
  let fileSel = new fileSelectionWin () in
  let findRepl = new findReplWin () in
  let keyBindingBoxes = (* event boxes which should receive global key events *)
    [ main#mainWinEventBox ]
  in
  let console = new console ~buffer:main#logTextView#buffer () in
  object (self)
    val mutable chosen_file = None
    val mutable _ok_not_exists = false
    val mutable _only_directory = false
    val mutable current_page = -1
      
    initializer
      let s () = MatitaScript.current () in
        (* key bindings *)
      List.iter (* global key bindings *)
        (fun (key, modifiers, callback) -> 
                self#addKeyBinding key ~modifiers callback)
(*
        [ GdkKeysyms._F3,
            toggle_win ~check:main#showProofMenuItem proof#proofWin;
          GdkKeysyms._F4,
            toggle_win ~check:main#showCheckMenuItem check#checkWin;
*)
        [ 
          GdkKeysyms._Page_Down, [`CONTROL], main#scriptNotebook#next_page;
          GdkKeysyms._Page_Up,   [`CONTROL], main#scriptNotebook#previous_page
        ];
        (* about win *)
      let parse_txt_file file =
       let ch = open_in (BuildTimeConf.runtime_base_dir ^ "/" ^ file) in
       let l_rev = ref [] in
       try
        while true do
         l_rev := input_line ch :: !l_rev;
        done;
        assert false
       with
        End_of_file ->
         close_in ch;
         List.rev !l_rev in 
      let about_dialog =
       GWindow.about_dialog
        ~authors:(parse_txt_file "AUTHORS")
        (*~comments:"comments"*)
        ~copyright:"Copyright (C) 2005, the HELM team"
        ~license:(String.concat "\n" (parse_txt_file "LICENSE"))
        ~logo:(GdkPixbuf.from_file (MatitaMisc.image_path "/matita_medium.png"))
        ~name:"Matita"
        ~version:BuildTimeConf.version
        ~website:"http://matita.cs.unibo.it"
        ()
      in
      ignore(about_dialog#connect#response (fun _ ->about_dialog#misc#hide ()));
      connect_menu_item main#contentsMenuItem (fun () ->
        if 0 = Sys.command "which gnome-help" then
          let cmd =
            sprintf "gnome-help ghelp://%s/C/matita.xml &" BuildTimeConf.help_dir
          in
           ignore (Sys.command cmd)
        else
          MatitaGtkMisc.report_error ~title:"help system error"
           ~message:(
              "The program gnome-help is not installed\n\n"^
              "To browse the user manal it is necessary to install "^
              "the gnome help syste (also known as yelp)") 
           ~parent:main#toplevel ());
      connect_menu_item main#aboutMenuItem about_dialog#present;
        (* findRepl win *)
      let show_find_Repl () = 
        findRepl#toplevel#misc#show ();
        findRepl#toplevel#misc#grab_focus ()
      in
      let hide_find_Repl () = findRepl#toplevel#misc#hide () in
      let find_forward _ = 
          let source_view = (s ())#source_view in
          let highlight start end_ =
            source_view#source_buffer#move_mark `INSERT ~where:start;
            source_view#source_buffer#move_mark `SEL_BOUND ~where:end_;
            source_view#scroll_mark_onscreen `INSERT
          in
          let text = findRepl#findEntry#text in
          let iter = source_view#source_buffer#get_iter `SEL_BOUND in
          match iter#forward_search text with
          | None -> 
              (match source_view#source_buffer#start_iter#forward_search text with
              | None -> ()
              | Some (start,end_) -> highlight start end_)
          | Some (start,end_) -> highlight start end_ 
      in
      let replace _ =
        let source_view = (s ())#source_view in
        let text = findRepl#replaceEntry#text in
        let ins = source_view#source_buffer#get_iter `INSERT in
        let sel = source_view#source_buffer#get_iter `SEL_BOUND in
        if ins#compare sel < 0 then 
          begin
            ignore(source_view#source_buffer#delete_selection ());
            source_view#source_buffer#insert text
          end
      in
      connect_button findRepl#findButton find_forward;
      connect_button findRepl#findReplButton replace;
      connect_button findRepl#cancelButton (fun _ -> hide_find_Repl ());
      ignore(findRepl#toplevel#event#connect#delete 
        ~callback:(fun _ -> hide_find_Repl ();true));
      connect_menu_item main#undoMenuItem
       (fun () -> (MatitaScript.current ())#safe_undo);
(*CSC: XXX
      ignore(source_view#source_buffer#connect#can_undo
        ~callback:main#undoMenuItem#misc#set_sensitive);
*) main#undoMenuItem#misc#set_sensitive true;
      connect_menu_item main#redoMenuItem
       (fun () -> (MatitaScript.current ())#safe_redo);
(*CSC: XXX
      ignore(source_view#source_buffer#connect#can_redo
        ~callback:main#redoMenuItem#misc#set_sensitive);
*) main#redoMenuItem#misc#set_sensitive true;
      connect_menu_item main#editMenu (fun () ->
        main#copyMenuItem#misc#set_sensitive
         (MatitaScript.current ())#canCopy;
        main#cutMenuItem#misc#set_sensitive
         (MatitaScript.current ())#canCut;
        main#deleteMenuItem#misc#set_sensitive
         (MatitaScript.current ())#canDelete;
        main#pasteMenuItem#misc#set_sensitive
         (MatitaScript.current ())#canPaste;
        main#pastePatternMenuItem#misc#set_sensitive
         (MatitaScript.current ())#canPastePattern);
      connect_menu_item main#copyMenuItem
         (fun () -> (MatitaScript.current ())#copy ());
      connect_menu_item main#cutMenuItem
         (fun () -> (MatitaScript.current ())#cut ());
      connect_menu_item main#deleteMenuItem
         (fun () -> (MatitaScript.current ())#delete ());
      connect_menu_item main#pasteMenuItem
         (fun () -> (MatitaScript.current ())#paste ());
      connect_menu_item main#pastePatternMenuItem
         (fun () -> (MatitaScript.current ())#pastePattern ());
      connect_menu_item main#selectAllMenuItem (fun () ->
       let source_view = (s ())#source_view in
        source_view#source_buffer#move_mark `INSERT source_view#source_buffer#start_iter;
        source_view#source_buffer#move_mark `SEL_BOUND source_view#source_buffer#end_iter);
      connect_menu_item main#findReplMenuItem show_find_Repl;
      connect_menu_item main#externalEditorMenuItem self#externalEditor;
      connect_menu_item main#ligatureButton
       (fun () -> (MatitaScript.current ())#nextSimilarSymbol);
      ignore (findRepl#findEntry#connect#activate find_forward);
        (* interface lockers *)
      let lock_world _ =
       let source_view = (s ())#source_view in
        main#buttonsToolbar#misc#set_sensitive false;
        main#scriptMenu#misc#set_sensitive false;
        source_view#set_editable false
      in
      let unlock_world _ =
       let source_view = (s ())#source_view in
        main#buttonsToolbar#misc#set_sensitive true;
        main#scriptMenu#misc#set_sensitive true;
        source_view#set_editable true;
        (*The next line seems sufficient to avoid some unknown race condition *)
        GtkThread.sync (fun () -> ()) ()
      in
      let worker_thread = ref None in
      let notify_exn (source_view : GSourceView2.source_view) exn =
       let floc, msg = MatitaExcPp.to_string exn in
        begin
         match floc with
            None -> ()
          | Some floc ->
             let (x, y) = HExtlib.loc_of_floc floc in
             let script = MatitaScript.current () in
             let locked_mark = script#locked_mark in
             let error_tag = script#error_tag in
             let baseoffset =
              (source_view#source_buffer#get_iter_at_mark (`MARK locked_mark))#offset in
             let x' = baseoffset + x in
             let y' = baseoffset + y in
             let x_iter = source_view#source_buffer#get_iter (`OFFSET x') in
             let y_iter = source_view#source_buffer#get_iter (`OFFSET y') in
             source_view#source_buffer#apply_tag error_tag ~start:x_iter ~stop:y_iter;
             let id = ref None in
             id := Some (source_view#source_buffer#connect#changed ~callback:(fun () ->
               source_view#source_buffer#remove_tag error_tag
                 ~start:source_view#source_buffer#start_iter
                 ~stop:source_view#source_buffer#end_iter;
               match !id with
               | None -> assert false (* a race condition occurred *)
               | Some id ->
                   source_view#source_buffer#misc#disconnect id));
             source_view#source_buffer#place_cursor
              (source_view#source_buffer#get_iter (`OFFSET x'));
        end;
        HLog.error msg in
      let locker f script =
       let source_view = script#source_view in
       let thread_main =
        fun () -> 
          lock_world ();
          let saved_use_library= !MultiPassDisambiguator.use_library in
          try
           MultiPassDisambiguator.use_library := !all_disambiguation_passes;
           f script;
           MultiPassDisambiguator.use_library := saved_use_library;
           unlock_world ()
          with
           | MultiPassDisambiguator.DisambiguationError (offset,errorll) ->
              (try
                interactive_error_interp 
                 ~all_passes:!all_disambiguation_passes source_view#source_buffer
                 (notify_exn source_view) offset errorll (s())#filename
               with
                | UseLibrary ->
                   MultiPassDisambiguator.use_library := true;
                   (try f script
                    with
                    | MultiPassDisambiguator.DisambiguationError (offset,errorll) ->
                       interactive_error_interp ~all_passes:true source_view#source_buffer
                        (notify_exn source_view) offset errorll (s())#filename
                    | exc ->
                       notify_exn source_view exc);
                | exc -> notify_exn source_view exc);
              MultiPassDisambiguator.use_library := saved_use_library;
              unlock_world ()
           | exc ->
              (try notify_exn source_view exc
               with Sys.Break as e -> notify_exn source_view e);
              unlock_world ()
       in
       (*thread_main ();*)
       worker_thread := Some (Thread.create thread_main ())
      in
      let kill_worker =
       (* the following lines are from Xavier Leroy: http://alan.petitepomme.net/cwn/2005.11.08.html *)
       let interrupt = ref None in
       let old_callback = ref (function _ -> ()) in
       let force_interrupt n =
         (* This function is called just before the thread's timeslice ends *)
         !old_callback n;
         if Some(Thread.id(Thread.self())) = !interrupt then
          (interrupt := None; raise Sys.Break) in
       let _ =
        match Sys.signal Sys.sigvtalrm (Sys.Signal_handle force_interrupt) with
           Sys.Signal_handle f -> old_callback := f
         | Sys.Signal_ignore
         | Sys.Signal_default -> assert false
       in
        fun () ->
         match !worker_thread with
            None -> assert false
          | Some t -> interrupt := Some (Thread.id t) in
      let keep_focus f (script: MatitaScript.script) =
         try
          f script; script#source_view#misc#grab_focus ()
         with
          exc -> script#source_view#misc#grab_focus (); raise exc in
      
        (* file selection win *)
      ignore (fileSel#fileSelectionWin#event#connect#delete (fun _ -> true));
      ignore (fileSel#fileSelectionWin#connect#response (fun event ->
        let return r =
          chosen_file <- r;
          fileSel#fileSelectionWin#misc#hide ();
          GMain.Main.quit ()
        in
        match event with
        | `OK ->
            let fname = fileSel#fileSelectionWin#filename in
            if Sys.file_exists fname then
              begin
                if HExtlib.is_regular fname && not (_only_directory) then 
                  return (Some fname) 
                else if _only_directory && HExtlib.is_dir fname then 
                  return (Some fname)
              end
            else
              begin
                if _ok_not_exists then 
                  return (Some fname)
              end
        | `CANCEL -> return None
        | `HELP -> ()
        | `DELETE_EVENT -> return None));
        (* menus *)
      List.iter (fun w -> w#misc#set_sensitive false) [ main#saveMenuItem ];
        (* console *)
      let adj = main#logScrolledWin#vadjustment in
        ignore (adj#connect#changed
                (fun _ -> adj#set_value (adj#upper -. adj#page_size)));
      console#message (sprintf "\tMatita version %s\n" BuildTimeConf.version);
        (* natural deduction palette *)
      main#tacticsButtonsHandlebox#misc#hide ();
      MatitaGtkMisc.toggle_callback
        ~callback:(fun b -> 
          if b then main#tacticsButtonsHandlebox#misc#show ()
          else main#tacticsButtonsHandlebox#misc#hide ())
        ~check:main#menuitemPalette;
      connect_button main#butImpl_intro
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (⇒#i […] (…));\n");
      connect_button main#butAnd_intro
        (fun () -> (s ())#source_view#source_buffer#insert 
          "apply rule (∧#i (…) (…));\n\t[\n\t|\n\t]\n");
      connect_button main#butOr_intro_left
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (∨#i_l (…));\n");
      connect_button main#butOr_intro_right
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (∨#i_r (…));\n");
      connect_button main#butNot_intro
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (¬#i […] (…));\n");
      connect_button main#butTop_intro
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (⊤#i);\n");
      connect_button main#butImpl_elim
        (fun () -> (s ())#source_view#source_buffer#insert 
          "apply rule (⇒#e (…) (…));\n\t[\n\t|\n\t]\n");
      connect_button main#butAnd_elim_left
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (∧#e_l (…));\n");
      connect_button main#butAnd_elim_right
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (∧#e_r (…));\n");
      connect_button main#butOr_elim
        (fun () -> (s ())#source_view#source_buffer#insert 
          "apply rule (∨#e (…) […] (…) […] (…));\n\t[\n\t|\n\t|\n\t]\n");
      connect_button main#butNot_elim
        (fun () -> (s ())#source_view#source_buffer#insert 
          "apply rule (¬#e (…) (…));\n\t[\n\t|\n\t]\n");
      connect_button main#butBot_elim
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (⊥#e (…));\n");
      connect_button main#butRAA
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (RAA […] (…));\n");
      connect_button main#butUseLemma
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (lem #premises name …);\n");
      connect_button main#butDischarge
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (discharge […]);\n");
      
      connect_button main#butForall_intro
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (∀#i {…} (…));\n");
      connect_button main#butForall_elim
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (∀#e {…} (…));\n");
      connect_button main#butExists_intro
        (fun () -> (s ())#source_view#source_buffer#insert "apply rule (∃#i {…} (…));\n");
      connect_button main#butExists_elim
        (fun () -> (s ())#source_view#source_buffer#insert 
          "apply rule (∃#e (…) {…} […] (…));\n\t[\n\t|\n\t]\n");

    
      let module Hr = Helm_registry in
      MatitaGtkMisc.toggle_callback ~check:main#fullscreenMenuItem
        ~callback:(function 
          | true -> main#toplevel#fullscreen () 
          | false -> main#toplevel#unfullscreen ());
      main#fullscreenMenuItem#set_active false;
      MatitaGtkMisc.toggle_callback ~check:main#ppNotationMenuItem
        ~callback:(function b ->
          let s = s () in
          let _status = Interpretations.toggle_active_interpretations s#status b
          in
           assert false (* MATITA 1.0 ???
           s#set_grafite_status status*)
         );
      MatitaGtkMisc.toggle_callback ~check:main#hideCoercionsMenuItem
        ~callback:(fun enabled -> Interpretations.hide_coercions := enabled);
      MatitaGtkMisc.toggle_callback ~check:main#unicodeAsTexMenuItem
        ~callback:(fun enabled ->
          Helm_registry.set_bool "matita.paste_unicode_as_tex" enabled);
      main#unicodeAsTexMenuItem#set_active
        (Helm_registry.get_bool "matita.paste_unicode_as_tex");
        (* log *)
      HLog.set_log_callback (fun tag msg -> GtkThread.async (self#console#log_callback tag) msg);
      GtkSignal.user_handler :=
        (function 
        | MatitaScript.ActionCancelled s -> HLog.error s
        | exn ->
          if not (Helm_registry.get_bool "matita.debug") then
           (* MatitaScript.current is problably wrong, but what else
              can we do? *)
           notify_exn (MatitaScript.current ())#source_view exn
          else raise exn);
      let loadScript () =
        try 
          match self#chooseFile () with
          | Some f -> self#loadScript f
          | None -> ()
        with MatitaTypes.Cancel -> ()
      in
      let cursor () =
       let source_view = (s ())#source_view in
        source_view#source_buffer#place_cursor
          (source_view#source_buffer#get_iter_at_mark (`NAME "locked")) in
      let advance (script: MatitaScript.script) = script#advance (); cursor () in
      let retract (script: MatitaScript.script) = script#retract (); cursor () in
      let top (script: MatitaScript.script) = script#goto `Top (); cursor () in
      let bottom (script: MatitaScript.script) = script#goto `Bottom (); cursor () in
      let jump (script: MatitaScript.script) = script#goto `Cursor (); cursor () in
      let advance () = locker (keep_focus advance) (MatitaScript.current ()) in
      let retract () = locker (keep_focus retract) (MatitaScript.current ()) in
      let top () = locker (keep_focus top) (MatitaScript.current ()) in
      let bottom () = locker (keep_focus bottom) (MatitaScript.current ()) in
      let jump () = locker (keep_focus jump) (MatitaScript.current ()) in
        (* quit *)
      self#setQuitCallback (fun () -> 
       let cancel = ref false in
        MatitaScript.iter_scripts
         (fun script ->
           if not !cancel then
            if not (self#closeScript0 script) then
             cancel := true);
        if not !cancel then
         GMain.Main.quit ());
      connect_button main#scriptAdvanceButton advance;
      connect_button main#scriptRetractButton retract;
      connect_button main#scriptTopButton top;
      connect_button main#scriptBottomButton bottom;
      connect_button main#scriptJumpButton jump;
      connect_button main#scriptAbortButton kill_worker;
      connect_menu_item main#scriptAdvanceMenuItem advance;
      connect_menu_item main#scriptRetractMenuItem retract;
      connect_menu_item main#scriptTopMenuItem top;
      connect_menu_item main#scriptBottomMenuItem bottom;
      connect_menu_item main#scriptJumpMenuItem jump;
      connect_menu_item main#openMenuItem   loadScript;
      connect_menu_item main#saveMenuItem 
       (fun () -> self#saveScript (MatitaScript.current ()));
      connect_menu_item main#saveAsMenuItem
       (fun () -> self#saveAsScript (MatitaScript.current ()));
      connect_menu_item main#newMenuItem self#newScript;
      connect_menu_item main#closeMenuItem self#closeCurrentScript;
      connect_menu_item main#showCoercionsGraphMenuItem 
        (fun _ -> MatitaMathView.cicBrowser (Some (`About `Coercions)));
      connect_menu_item main#showHintsDbMenuItem 
        (fun _ -> MatitaMathView.cicBrowser (Some (`About `Hints)));
      connect_menu_item main#showTermGrammarMenuItem 
        (fun _ -> MatitaMathView.cicBrowser (Some (`About `Grammar)));
      connect_menu_item main#showUnicodeTable
        (fun _ -> MatitaMathView.cicBrowser (Some (`About `TeX)));
        (* debug menu *)
      main#debugMenu#misc#hide ();
        (* HBUGS *)
      main#hintNotebook#misc#hide ();
      (*
      main#hintLowImage#set_file (image_path "matita-bulb-low.png");
      main#hintMediumImage#set_file (image_path "matita-bulb-medium.png");
      main#hintHighImage#set_file (image_path "matita-bulb-high.png");
      *)
        (* main win dimension *)
      let width = Gdk.Screen.width ~screen:(Gdk.Screen.default ()) () in
      let height = Gdk.Screen.height ~screen:(Gdk.Screen.default ()) () in
      (* hack for xinerama, no proper support of monitors from lablgtk *)
      let width = if width > 1600 then width / 2 else width in
      let height = if height > 1200 then height / 2 else height in
      let main_w = width * 90 / 100 in 
      let main_h = height * 80 / 100 in
      let script_w = main_w * 6 / 10 in
      main#toplevel#resize ~width:main_w ~height:main_h;
      main#hpaneScriptSequent#set_position script_w;
      (* math view handling *)
      connect_menu_item main#newCicBrowserMenuItem (fun () ->
        ignore(MatitaMathView.cicBrowser None));
      connect_menu_item main#increaseFontSizeMenuItem
        MatitaMisc.increase_font_size;
      connect_menu_item main#decreaseFontSizeMenuItem
        MatitaMisc.decrease_font_size;
      connect_menu_item main#normalFontSizeMenuItem
        MatitaMisc.reset_font_size;
      ignore (main#scriptNotebook#connect#switch_page (fun page ->
        self#save_page ();
        current_page <- page;
        let script = MatitaScript.at_page page in
        script#activate;
        main#saveMenuItem#misc#set_sensitive script#has_name))

    method private externalEditor () =
     let script = MatitaScript.current () in
     let source_view = script#source_view in
      let cmd = Helm_registry.get "matita.external_editor" in
(* ZACK uncomment to enable interactive ask of external editor command *)
(*      let cmd =
         let msg =
          "External editor command:
%f  will be substitute for the script name,
%p  for the cursor position in bytes,
%l  for the execution point in bytes."
        in
        ask_text ~gui:self ~title:"External editor" ~msg ~multiline:false
          ~default:(Helm_registry.get "matita.external_editor") ()
      in *)
      let fname = script#filename in
      let slice mark =
        source_view#source_buffer#start_iter#get_slice
          ~stop:(source_view#source_buffer#get_iter_at_mark mark)
      in
      let locked = `MARK script#locked_mark in
      let string_pos mark = string_of_int (String.length (slice mark)) in
      let cursor_pos = string_pos `INSERT in
      let locked_pos = string_pos locked in
      let cmd =
        Pcre.replace ~pat:"%f" ~templ:fname
          (Pcre.replace ~pat:"%p" ~templ:cursor_pos
            (Pcre.replace ~pat:"%l" ~templ:locked_pos
              cmd))
      in
      let locked_before = slice locked in
      let locked_offset = (source_view#source_buffer#get_iter_at_mark locked)#offset in
      ignore (Unix.system cmd);
      source_view#source_buffer#set_text (HExtlib.input_file fname);
      let locked_iter = source_view#source_buffer#get_iter (`OFFSET locked_offset) in
      source_view#source_buffer#move_mark locked locked_iter;
      source_view#source_buffer#apply_tag script#locked_tag
        ~start:source_view#source_buffer#start_iter ~stop:locked_iter;
      let locked_after = slice locked in
      let line = ref 0 in
      let col = ref 0 in
      try
        for i = 0 to String.length locked_before - 1 do
          if locked_before.[i] <> locked_after.[i] then begin
            source_view#source_buffer#place_cursor
              ~where:(source_view#source_buffer#get_iter (`LINEBYTE (!line, !col)));
            script#goto `Cursor ();
            raise Exit
          end else if locked_before.[i] = '\n' then begin
            incr line;
            col := 0
          end
        done
      with
      | Exit -> ()
      | Invalid_argument _ -> script#goto `Bottom ()

    method private saveAsScript script = 
     match self#chooseFile ~ok_not_exists:true () with
     | Some f -> 
           HExtlib.touch f;
           script#assignFileName (Some f);
           script#saveToFile (); 
           console#message ("'"^f^"' saved.\n");
           self#_enableSaveTo f
     | None -> ()

    method private saveScript script = 
     if script#has_name then 
       (script#saveToFile (); 
        console#message ("'"^script#filename^"' saved.\n"))
     else self#saveAsScript script
    
    (* returns false if closure is aborted by the user *)
    method private closeScript0 script = 
      if script#source_view#buffer#modified then
        match
         ask_unsaved main#toplevel (Filename.basename script#filename)
        with
        | `YES -> 
             self#saveScript script;
             save_moo script#status;
             true
        | `NO -> true
        | `CANCEL -> false
      else 
       (save_moo script#status; true)

    method private closeScript page script = 
     if self#closeScript0 script then
      begin
       MatitaScript.destroy page;
       ignore (main#scriptNotebook#remove_page page)
      end

    method private closeCurrentScript () = 
     let page = main#scriptNotebook#current_page in
     let script = MatitaScript.at_page page in 
      self#closeScript page script

    method private save_page () =
      if current_page >= 0 then
        let old_script = MatitaScript.at_page current_page in
        save_moo0 ~do_clean:false old_script old_script#status

    method newScript () = 
       self#save_page ();
       let scrolledWindow = GBin.scrolled_window () in
       let hbox = GPack.hbox () in
       let tab_label = GMisc.label ~text:"foo" ~packing:hbox#pack () in
       let _ =
        GMisc.label ~text:"" ~packing:(hbox#pack ~expand:true ~fill:true) () in
       let closebutton =
        GButton.button ~relief:`NONE ~packing:hbox#pack () in
       let image = GMisc.image ~stock:`CLOSE ~icon_size:`MENU () in
       closebutton#set_image image#coerce;
       let script = MatitaScript.script ~parent:scrolledWindow ~tab_label () in
        ignore (main#scriptNotebook#prepend_page ~tab_label:hbox#coerce
         scrolledWindow#coerce);
        ignore (closebutton#connect#clicked (fun () ->
         self#closeScript
          (main#scriptNotebook#page_num scrolledWindow#coerce) script));
        main#scriptNotebook#goto_page 0;
        sequents_viewer#reset;
        sequents_viewer#load_logo;
        let browser_observer _ = MatitaMathView.refresh_all_browsers () in
        let sequents_observer status =
          sequents_viewer#reset;
          match status#ng_mode with
             `ProofMode ->
              sequents_viewer#nload_sequents status;
              (try
                let goal =
                 Continuationals.Stack.find_goal status#stack
                in
                 sequents_viewer#goto_sequent status goal
              with Failure _ -> ());
           | `CommandMode -> sequents_viewer#load_logo
        in
        script#addObserver sequents_observer;
        script#addObserver browser_observer

    method loadScript file =       
     let page = main#scriptNotebook#current_page in
     let script = MatitaScript.at_page page in
      if script#source_view#buffer#modified || script#has_name then
       self#newScript ();
     let script = MatitaScript.current () in
     let source_view = script#source_view in
      script#reset (); 
      script#assignFileName (Some file);
      let file = script#filename in
      let content =
       if Sys.file_exists file then file
       else BuildTimeConf.script_template
      in
      source_view#source_buffer#begin_not_undoable_action ();
      script#loadFromFile content;
      source_view#source_buffer#end_not_undoable_action ();
      source_view#buffer#move_mark `INSERT source_view#buffer#start_iter;
      source_view#buffer#place_cursor source_view#buffer#start_iter;
      console#message ("'"^file^"' loaded.");
      self#_enableSaveTo file

    method private _enableSaveTo file =
      self#main#saveMenuItem#misc#set_sensitive true
        
    method private console = console
    method private fileSel = fileSel
    method private findRepl = findRepl
    method main = main

    method private addKeyBinding key ?modifiers callback =
(*       List.iter (fun evbox -> add_key_binding key callback evbox) *)
      List.iter (fun evbox -> connect_key evbox#event key ?modifiers callback)
        keyBindingBoxes

    method private setQuitCallback callback =
      connect_menu_item main#quitMenuItem callback;
      ignore (main#toplevel#event#connect#delete 
        (fun _ -> callback ();true));
      self#addKeyBinding GdkKeysyms._q callback

    method private chooseFile ?(ok_not_exists = false) () =
      _ok_not_exists <- ok_not_exists;
      _only_directory <- false;
      fileSel#fileSelectionWin#show ();
      GtkThread.main ();
      chosen_file

    method private chooseDir ?(ok_not_exists = false) () =
      _ok_not_exists <- ok_not_exists;
      _only_directory <- true;
      fileSel#fileSelectionWin#show ();
      GtkThread.main ();
      (* we should check that this is a directory *)
      chosen_file
  
  end

let gui () = 
  let g = new gui () in
  let rg = (g :> MatitaGuiTypes.gui) in
  MatitaMisc.set_gui rg;
  g#newScript ();
  rg
  
let instance = singleton gui

let non p x = not (p x)

class interpModel =
  let cols = new GTree.column_list in
  let id_col = cols#add Gobject.Data.string in
  let dsc_col = cols#add Gobject.Data.string in
  let interp_no_col = cols#add Gobject.Data.int in
  let tree_store = GTree.tree_store cols in
  let id_renderer = GTree.cell_renderer_text [], ["text", id_col] in
  let dsc_renderer = GTree.cell_renderer_text [], ["text", dsc_col] in
  let id_view_col = GTree.view_column ~renderer:id_renderer () in
  let dsc_view_col = GTree.view_column ~renderer:dsc_renderer () in
  fun tree_view choices ->
    object
      initializer
        tree_view#set_model (Some (tree_store :> GTree.model));
        ignore (tree_view#append_column id_view_col);
        ignore (tree_view#append_column dsc_view_col);
        let name_of_interp =
          (* try to find a reasonable name for an interpretation *)
          let idx = ref 0 in
          fun interp ->
            try
              List.assoc "0" interp
            with Not_found ->
              incr idx; string_of_int !idx
        in
        tree_store#clear ();
        let idx = ref ~-1 in
        List.iter
          (fun interp ->
            incr idx;
            let interp_row = tree_store#append () in
            tree_store#set ~row:interp_row ~column:id_col
              (name_of_interp interp);
            tree_store#set ~row:interp_row ~column:interp_no_col !idx;
            List.iter
              (fun (id, dsc) ->
                let row = tree_store#append ~parent:interp_row () in
                tree_store#set ~row ~column:id_col id;
                tree_store#set ~row ~column:dsc_col dsc;
                tree_store#set ~row ~column:interp_no_col !idx)
              interp)
          choices

      method get_interp_no tree_path =
        let iter = tree_store#get_iter tree_path in
        tree_store#get ~row:iter ~column:interp_no_col
    end


let interactive_string_choice 
  text prefix_len ?(title = "") ?(msg = "") () ~id locs uris 
= 
 let dialog = new uriChoiceDialog () in
 dialog#uriEntryHBox#misc#hide ();
 dialog#uriChoiceSelectedButton#misc#hide ();
 dialog#uriChoiceAutoButton#misc#hide ();
 dialog#uriChoiceConstantsButton#misc#hide ();
 dialog#uriChoiceTreeView#selection#set_mode
   (`SINGLE :> Gtk.Tags.selection_mode);
 let model = new stringListModel dialog#uriChoiceTreeView in
 let choices = ref None in
 dialog#uriChoiceDialog#set_title title; 
 let hack_len = MatitaGtkMisc.utf8_string_length text in
 let rec colorize acc_len = function
   | [] -> 
       let floc = HExtlib.floc_of_loc (acc_len,hack_len) in
       escape_pango_markup (fst(MatitaGtkMisc.utf8_parsed_text text floc))
   | he::tl -> 
       let start, stop =  HExtlib.loc_of_floc he in
       let floc1 = HExtlib.floc_of_loc (acc_len,start) in
       let str1,_=MatitaGtkMisc.utf8_parsed_text text floc1 in
       let str2,_ = MatitaGtkMisc.utf8_parsed_text text he in
       escape_pango_markup str1 ^ "<b>" ^ 
       escape_pango_markup str2 ^ "</b>" ^ 
       colorize stop tl
 in
(*     List.iter (fun l -> let start, stop = HExtlib.loc_of_floc l in
              Printf.eprintf "(%d,%d)" start stop) locs; *)
  let locs = 
    List.sort 
      (fun loc1 loc2 -> 
        fst (HExtlib.loc_of_floc loc1) - fst (HExtlib.loc_of_floc loc2)) 
      locs 
  in
(*     prerr_endline "XXXXXXXXXXXXXXXXXXXX";
  List.iter (fun l -> let start, stop = HExtlib.loc_of_floc l in
              Printf.eprintf "(%d,%d)" start stop) locs;
  prerr_endline "XXXXXXXXXXXXXXXXXXXX2"; *)
  dialog#uriChoiceLabel#set_use_markup true;
  let txt = colorize 0 locs in
  let txt,_ = MatitaGtkMisc.utf8_parsed_text txt
    (HExtlib.floc_of_loc (prefix_len,MatitaGtkMisc.utf8_string_length txt))
  in
  dialog#uriChoiceLabel#set_label txt;
  List.iter model#easy_append uris;
  let return v =
    choices := v;
    dialog#uriChoiceDialog#destroy ();
    GMain.Main.quit ()
  in
  ignore (dialog#uriChoiceDialog#event#connect#delete (fun _ -> true));
  connect_button dialog#uriChoiceForwardButton (fun _ ->
    match model#easy_selection () with
    | [] -> ()
    | uris -> return (Some uris));
  connect_button dialog#uriChoiceAbortButton (fun _ -> return None);
  dialog#uriChoiceDialog#show ();
  GtkThread.main ();
  (match !choices with 
  | None -> raise MatitaTypes.Cancel
  | Some uris -> uris)

let interactive_interp_choice () text prefix_len choices =
(*List.iter (fun l -> prerr_endline "==="; List.iter (fun (_,id,dsc) -> prerr_endline (id ^ " = " ^ dsc)) l) choices;*)
 let filter_choices filter =
  let rec is_compatible filter =
   function
      [] -> true
    | ([],_,_)::tl -> is_compatible filter tl
    | (loc::tlloc,id,dsc)::tl ->
       try
        if List.assoc (loc,id) filter = dsc then
         is_compatible filter ((tlloc,id,dsc)::tl)
        else
         false
       with
        Not_found -> true
  in
   List.filter (fun (_,interp) -> is_compatible filter interp)
 in
 let rec get_choices loc id =
  function
     [] -> []
   | (_,he)::tl ->
      let _,_,dsc =
       List.find (fun (locs,id',_) -> id = id' && List.mem loc locs) he
      in
       dsc :: (List.filter (fun dsc' -> dsc <> dsc') (get_choices loc id tl))
 in
 let example_interp =
  match choices with
     [] -> assert false
   | he::_ -> he in
 let ask_user id locs choices =
  interactive_string_choice
   text prefix_len
   ~title:"Ambiguous input"
   ~msg:("Choose an interpretation for " ^ id) () ~id locs choices
 in
 let rec classify ids filter partial_interpretations =
  match ids with
     [] -> List.map fst partial_interpretations
   | ([],_,_)::tl -> classify tl filter partial_interpretations
   | (loc::tlloc,id,dsc)::tl ->
      let choices = get_choices loc id partial_interpretations in
      let chosen_dsc =
       match choices with
          [] -> prerr_endline ("NO CHOICES FOR " ^ id); assert false
        | [dsc] -> dsc
        | _ ->
          match ask_user id [loc] choices with
             [x] -> x
           | _ -> assert false
      in
       let filter = ((loc,id),chosen_dsc)::filter in
       let compatible_interps = filter_choices filter partial_interpretations in
        classify ((tlloc,id,dsc)::tl) filter compatible_interps
 in
 let enumerated_choices =
  let idx = ref ~-1 in
  List.map (fun interp -> incr idx; !idx,interp) choices
 in
  classify example_interp [] enumerated_choices

let _ =
  (* disambiguator callbacks *)
  Disambiguate.set_choose_uris_callback
   (fun ~selection_mode ?ok ?(enable_button_for_non_vars=false) ~title ~msg ->
     interactive_uri_choice ~selection_mode ?ok_label:ok ~title ~msg ());
  Disambiguate.set_choose_interp_callback (interactive_interp_choice ());
  (* gtk initialization *)
  GtkMain.Rc.add_default_file BuildTimeConf.gtkrc_file; (* loads gtk rc *)
  ignore (GMain.Main.init ())

