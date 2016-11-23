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
 * http://cs.unibo.it/helm/.
 *)

(* $Id: matitaMathView.ml 11904 2012-03-09 16:34:21Z sacerdot $ *)

open Printf

open GrafiteTypes
open MatitaGtkMisc
open MatitaGuiTypes
open CicMathView

module Stack = Continuationals.Stack

let cicBrowsers = ref []

let tab_label meta_markup =
  let rec aux =
    function
    | `Closed m -> sprintf "<s>%s</s>" (aux m)
    | `Current m -> sprintf "<b>%s</b>" (aux m)
    | `Shift (pos, m) -> sprintf "|<sub>%d</sub>: %s" pos (aux m)
    | `Meta n -> sprintf "?%d" n
  in
  let markup = aux meta_markup in
  (GMisc.label ~markup ~show:true ())#coerce

let goal_of_switch = function Stack.Open g | Stack.Closed g -> g

class sequentsViewer ~(notebook:GPack.notebook) ~(cicMathView:cicMathView) () =
  object (self)
    method cicMathView = cicMathView  (** clickableMathView accessor *)

    val mutable pages = 0
    val mutable switch_page_callback = None
    val mutable page2goal = []  (* associative list: page no -> goal no *)
    val mutable goal2page = []  (* the other way round *)
    val mutable goal2win = []   (* associative list: goal no -> scrolled win *)
    val mutable _metasenv = [],[]
    val mutable scrolledWin: GBin.scrolled_window option = None
      (* scrolled window to which the sequentViewer is currently attached *)
    val logo = (GMisc.image
      ~file:(MatitaMisc.image_path "matita_medium.png") ()
      :> GObj.widget)
            
    val logo_with_qed = (GMisc.image
      ~file:(MatitaMisc.image_path "matita_small.png") ()
      :> GObj.widget)

    method load_logo =
     notebook#set_show_tabs false;
     ignore(notebook#append_page logo)

    method load_logo_with_qed =
     notebook#set_show_tabs false;
     ignore(notebook#append_page logo_with_qed)

    method reset =
      cicMathView#remove_selections;
      (match scrolledWin with
      | Some w ->
          (* removing page from the notebook will destroy all contained widget,
          * we do not want the cicMathView to be destroyed as well *)
          w#remove cicMathView#coerce;
          scrolledWin <- None
      | None -> ());
      (match switch_page_callback with
      | Some id ->
          GtkSignal.disconnect notebook#as_widget id;
          switch_page_callback <- None
      | None -> ());
      for i = 0 to pages do notebook#remove_page 0 done; 
      notebook#set_show_tabs true;
      pages <- 0;
      page2goal <- [];
      goal2page <- [];
      goal2win <- [];
      _metasenv <- [],[]

    method nload_sequents : 'status. #GrafiteTypes.status as 'status -> unit
    = fun (status : #GrafiteTypes.status) ->
     let _,_,metasenv,subst,_ = status#obj in
      _metasenv <- metasenv,subst;
      pages <- 0;
      let win goal_switch =
        let w =
          GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`ALWAYS
            ~shadow_type:`IN ~show:true () in
        let reparent () =
          scrolledWin <- Some w;
          (match cicMathView#misc#parent with
            | None -> ()
            | Some parent ->
               let parent =
                match cicMathView#misc#parent with
                   None -> assert false
                 | Some p -> GContainer.cast_container p
               in
                parent#remove cicMathView#coerce);
          w#add cicMathView#coerce
        in
        goal2win <- (goal_switch, reparent) :: goal2win;
        w#coerce
      in
      assert (
        let stack_goals = Stack.open_goals status#stack in
        let proof_goals = List.map fst metasenv in
        if
          HExtlib.list_uniq (List.sort Pervasives.compare stack_goals)
          <> List.sort Pervasives.compare proof_goals
        then begin
          prerr_endline ("STACK GOALS = " ^ String.concat " " (List.map string_of_int stack_goals));
          prerr_endline ("PROOF GOALS = " ^ String.concat " " (List.map string_of_int proof_goals));
          false
        end
        else true
      );
      let render_switch =
        function Stack.Open i ->`Meta i | Stack.Closed i ->`Closed (`Meta i)
      in
      let page = ref 0 in
      let added_goals = ref [] in
        (* goals can be duplicated on the tack due to focus, but we should avoid
         * multiple labels in the user interface *)
      let add_tab markup goal_switch =
        let goal = Stack.goal_of_switch goal_switch in
        if not (List.mem goal !added_goals) then begin
          ignore(notebook#append_page 
            ~tab_label:(tab_label markup) (win goal_switch));
          page2goal <- (!page, goal_switch) :: page2goal;
          goal2page <- (goal_switch, !page) :: goal2page;
          incr page;
          pages <- pages + 1;
          added_goals := goal :: !added_goals
        end
      in
      let add_switch _ _ (_, sw) = add_tab (render_switch sw) sw in
      Stack.iter  (** populate notebook with tabs *)
        ~env:(fun depth tag (pos, sw) ->
          let markup =
            match depth, pos with
            | 0, 0 -> `Current (render_switch sw)
            | 0, _ -> `Shift (pos, `Current (render_switch sw))
            | 1, pos when Stack.head_tag status#stack = `BranchTag ->
                `Shift (pos, render_switch sw)
            | _ -> render_switch sw
          in
          add_tab markup sw)
        ~cont:add_switch ~todo:add_switch
        status#stack;
      switch_page_callback <-
        Some (notebook#connect#switch_page ~callback:(fun page ->
          let goal_switch =
            try List.assoc page page2goal with Not_found -> assert false
          in
          self#render_page status ~page ~goal_switch))

    method private render_page:
     'status. #ApplyTransformation.status as 'status -> page:int ->
       goal_switch:Stack.switch -> unit
     = fun status ~page ~goal_switch ->
      (match goal_switch with
      | Stack.Open goal ->
         let menv,subst = _metasenv in
          cicMathView#nload_sequent status menv subst goal
      | Stack.Closed goal ->
          let root = Lazy.force closed_goal_mathml in
          cicMathView#load_root ~root);
      (try
        cicMathView#set_selection None;
        List.assoc goal_switch goal2win ();
        (match cicMathView#misc#parent with
           None -> assert false
         | Some p ->
            (* The text widget dinamycally inserts the text in a separate
               thread. We need to wait for it to terminate before we can
               move the scrollbar to the end *)
            while Glib.Main.pending()do ignore(Glib.Main.iteration false); done;
            let w =
             new GBin.scrolled_window
              (Gobject.try_cast p#as_widget "GtkScrolledWindow") in
            (* The double change upper/lower is to trigger the emission of
               changed :-( *)
            w#hadjustment#set_value w#hadjustment#upper;
            w#hadjustment#set_value w#hadjustment#lower;
            w#vadjustment#set_value w#vadjustment#lower;
            w#vadjustment#set_value
             (w#vadjustment#upper -. w#vadjustment#page_size));
      with Not_found -> assert false)

    method goto_sequent: 'status. #ApplyTransformation.status as 'status -> int -> unit
     = fun status goal ->
      let goal_switch, page =
        try
          List.find
            (function Stack.Open g, _ | Stack.Closed g, _ -> g = goal)
            goal2page
        with Not_found -> assert false
      in
      notebook#goto_page page;
      self#render_page status ~page ~goal_switch
  end

let blank_uri = BuildTimeConf.blank_uri
let current_proof_uri = BuildTimeConf.current_proof_uri

type term_source =
  [ `Ast of NotationPt.term
  | `NCic of NCic.term * NCic.context * NCic.metasenv * NCic.substitution
  | `String of string
  ]

class cicBrowser_impl ~(history:MatitaTypes.mathViewer_entry MatitaMisc.history)
  ()
=
  let uri_RE =
    Pcre.regexp
      "^cic:/([^/]+/)*[^/]+\\.(con|ind|var)(#xpointer\\(\\d+(/\\d+)+\\))?$"
  in
  let dir_RE = Pcre.regexp "^cic:((/([^/]+/)*[^/]+(/)?)|/|)$" in
  let is_uri txt = Pcre.pmatch ~rex:uri_RE txt in
  let is_dir txt = Pcre.pmatch ~rex:dir_RE txt in
  let gui = MatitaMisc.get_gui () in
  let win = new MatitaGeneratedGui.browserWin () in
  let _ = win#browserUri#misc#grab_focus () in
  let gviz = LablGraphviz.graphviz ~packing:win#graphScrolledWin#add () in
  let searchText = 
    GSourceView2.source_view ~auto_indent:false ~editable:false ()
  in
  let _ =
     win#scrolledwinContent#add (searchText :> GObj.widget);
     let callback () = 
       let text = win#entrySearch#text in
       let highlight start end_ =
         searchText#source_buffer#move_mark `INSERT ~where:start;
         searchText#source_buffer#move_mark `SEL_BOUND ~where:end_;
         searchText#scroll_mark_onscreen `INSERT
       in
       let iter = searchText#source_buffer#get_iter `SEL_BOUND in
       match iter#forward_search text with
       | None -> 
           (match searchText#source_buffer#start_iter#forward_search text with
           | None -> ()
           | Some (start,end_) -> highlight start end_)
       | Some (start,end_) -> highlight start end_
     in
     ignore(win#entrySearch#connect#activate ~callback);
     ignore(win#buttonSearch#connect#clicked ~callback);
  in
  let toplevel = win#toplevel in
  let mathView = cicMathView ~packing:win#scrolledBrowser#add () in
  let fail message = 
    MatitaGtkMisc.report_error ~title:"Cic browser" ~message 
      ~parent:toplevel ()  
  in
  let tags =
    [ "dir", GdkPixbuf.from_file (MatitaMisc.image_path "matita-folder.png");
      "obj", GdkPixbuf.from_file (MatitaMisc.image_path "matita-object.png") ]
  in
  let b = (not (Helm_registry.get_bool "matita.debug")) in
  let handle_error f =
    try
      f ()
    with exn ->
      if b then
        fail (snd (MatitaExcPp.to_string exn))
      else raise exn
  in
  let handle_error' f = (fun () -> handle_error (fun () -> f ())) in
  let load_easter_egg = lazy (
    win#browserImage#set_file (MatitaMisc.image_path "meegg.png"))
  in
  let load_hints () =
      let module Pp = GraphvizPp.Dot in
      let filename, oc = Filename.open_temp_file "matita" ".dot" in
      let fmt = Format.formatter_of_out_channel oc in
      let status = (get_matita_script_current ())#status in
      Pp.header 
        ~name:"Hints"
        ~graph_type:"graph"
        ~graph_attrs:["overlap", "false"]
        ~node_attrs:["fontsize", "9"; "width", ".4"; 
            "height", ".4"; "shape", "box"]
        ~edge_attrs:["fontsize", "10"; "len", "2"] fmt;
      NCicUnifHint.generate_dot_file status fmt;
      Pp.trailer fmt;
      Pp.raw "@." fmt;
      close_out oc;
      gviz#load_graph_from_file ~gviz_cmd:"neato -Tpng" filename;
      (*HExtlib.safe_remove filename*)
  in
  let load_coerchgraph tred () = 
      let module Pp = GraphvizPp.Dot in
      let filename, oc = Filename.open_temp_file "matita" ".dot" in
      let fmt = Format.formatter_of_out_channel oc in
      Pp.header 
        ~name:"Coercions"
        ~node_attrs:["fontsize", "9"; "width", ".4"; "height", ".4"]
        ~edge_attrs:["fontsize", "10"] fmt;
      let status = (get_matita_script_current ())#status in
      NCicCoercion.generate_dot_file status fmt;
      Pp.trailer fmt;
      Pp.raw "@." fmt;
      close_out oc;
      if tred then
        gviz#load_graph_from_file 
          ~gviz_cmd:"dot -Txdot | tred |gvpack -gv | dot" filename
      else
        gviz#load_graph_from_file 
          ~gviz_cmd:"dot -Txdot | gvpack -gv | dot" filename;
      HExtlib.safe_remove filename
  in
  object (self)
    val mutable gviz_uri =
      let uri = NUri.uri_of_string "cic:/dummy/dec.con" in
      NReference.reference_of_spec uri NReference.Decl;

    val dep_contextual_menu = GMenu.menu ()

    initializer
      win#mathOrListNotebook#set_show_tabs false;
      win#browserForwardButton#misc#set_sensitive false;
      win#browserBackButton#misc#set_sensitive false;
      ignore (win#browserUri#connect#activate (handle_error' (fun () ->
        self#loadInput win#browserUri#text)));
      ignore (win#browserHomeButton#connect#clicked (handle_error' (fun () ->
        self#load (`About `Current_proof))));
      ignore (win#browserRefreshButton#connect#clicked
        (handle_error' (self#refresh ~force:true)));
      ignore (win#browserBackButton#connect#clicked (handle_error' self#back));
      ignore (win#browserForwardButton#connect#clicked
        (handle_error' self#forward));
      ignore (win#toplevel#event#connect#delete (fun _ ->
        let my_id = Oo.id self in
        cicBrowsers := List.filter (fun b -> Oo.id b <> my_id) !cicBrowsers;
        false));
      ignore(win#whelpResultTreeview#connect#row_activated 
        ~callback:(fun _ _ ->
          handle_error (fun () -> self#loadInput (self#_getSelectedUri ()))));
      mathView#set_href_callback (Some (fun uri ->
        handle_error (fun () ->
         let uri = `NRef (NReference.reference_of_string uri) in
          self#load uri)));
      gviz#connect_href (fun button_ev attrs ->
        let time = GdkEvent.Button.time button_ev in
        let uri = List.assoc "href" attrs in
        gviz_uri <- NReference.reference_of_string uri;
        match GdkEvent.Button.button button_ev with
        | button when button = MatitaMisc.left_button -> self#load (`NRef gviz_uri)
        | button when button = MatitaMisc.right_button ->
            dep_contextual_menu#popup ~button ~time
        | _ -> ());
      connect_menu_item win#browserCloseMenuItem (fun () ->
        let my_id = Oo.id self in
        cicBrowsers := List.filter (fun b -> Oo.id b <> my_id) !cicBrowsers;
        win#toplevel#misc#hide(); win#toplevel#destroy ());
      connect_menu_item win#browserUrlMenuItem (fun () ->
        win#browserUri#misc#grab_focus ());

      self#_load (`About `Blank);
      toplevel#show ()

    val mutable current_entry = `About `Blank 

      (** @return None if no object uri can be built from the current entry *)
    method private currentCicUri =
      match current_entry with
      | `NRef uri -> Some uri
      | _ -> None

    val model =
      new MatitaGtkMisc.taggedStringListModel tags win#whelpResultTreeview

    val mutable lastDir = ""  (* last loaded "directory" *)

    method mathView = mathView

    method private _getSelectedUri () =
      match model#easy_selection () with
      | [sel] when is_uri sel -> sel  (* absolute URI selected *)
(*       | [sel] -> win#browserUri#entry#text ^ sel  |+ relative URI selected +| *)
      | [sel] -> lastDir ^ sel
      | _ -> assert false

    (** history RATIONALE 
     *
     * All operations about history are done using _historyFoo.
     * Only toplevel functions (ATM load and loadInput) call _historyAdd.
     *)
          
    method private _historyAdd item = 
      history#add item;
      win#browserBackButton#misc#set_sensitive true;
      win#browserForwardButton#misc#set_sensitive false

    method private _historyPrev () =
      let item = history#previous in
      if history#is_begin then win#browserBackButton#misc#set_sensitive false;
      win#browserForwardButton#misc#set_sensitive true;
      item
    
    method private _historyNext () =
      let item = history#next in
      if history#is_end then win#browserForwardButton#misc#set_sensitive false;
      win#browserBackButton#misc#set_sensitive true;
      item

    (** notebook RATIONALE 
     * 
     * Use only these functions to switch between the tabs
     *)
    method private _showMath = win#mathOrListNotebook#goto_page   0
    method private _showList = win#mathOrListNotebook#goto_page   1
    method private _showEgg  = win#mathOrListNotebook#goto_page   2
    method private _showGviz = win#mathOrListNotebook#goto_page   3
    method private _showSearch = win#mathOrListNotebook#goto_page 4

    method private back () =
      try
        self#_load (self#_historyPrev ())
      with MatitaMisc.History_failure -> ()

    method private forward () =
      try
        self#_load (self#_historyNext ())
      with MatitaMisc.History_failure -> ()

      (* loads a uri which can be a cic uri or an about:* uri
      * @param uri string *)
    method private _load ?(force=false) entry =
      handle_error (fun () ->
       if entry <> current_entry || entry = `About `Current_proof || entry =
         `About `Coercions || entry = `About `CoercionsFull || force then
        begin
          (match entry with
          | `About `Current_proof -> self#home ()
          | `About `Blank -> self#blank ()
          | `About `Us -> self#egg ()
          | `About `CoercionsFull -> self#coerchgraph false ()
          | `About `Coercions -> self#coerchgraph true ()
          | `About `Hints -> self#hints ()
          | `About `TeX -> self#tex ()
          | `About `Grammar -> self#grammar () 
          | `Check term -> self#_loadCheck term
          | `NCic (term, ctx, metasenv, subst) -> 
               self#_loadTermNCic term metasenv subst ctx
          | `Dir dir -> self#_loadDir dir
          | `NRef nref -> self#_loadNReference nref);
          self#setEntry entry
        end)

    method private blank () =
      self#_showMath;
      mathView#load_root (Lazy.force empty_mathml)

    method private _loadCheck term =
      failwith "not implemented _loadCheck";
(*       self#_showMath *)

    method private egg () =
      self#_showEgg;
      Lazy.force load_easter_egg

    method private redraw_gviz ?center_on () =
      if Sys.command "which dot" = 0 then
       let tmpfile, oc = Filename.open_temp_file "matita" ".dot" in
       let fmt = Format.formatter_of_out_channel oc in
       (* MATITA 1.0 MetadataDeps.DepGraph.render fmt gviz_graph;*)
       close_out oc;
       gviz#load_graph_from_file ~gviz_cmd:"tred | dot" tmpfile;
       (match center_on with
       | None -> ()
       | Some uri -> gviz#center_on_href (NReference.string_of_reference uri));
       HExtlib.safe_remove tmpfile
      else
       MatitaGtkMisc.report_error ~title:"graphviz error"
        ~message:("Graphviz is not installed but is necessary to render "^
         "the graph of dependencies amoung objects. Please install it.")
        ~parent:win#toplevel ()

    method private dependencies direction uri () =
      assert false (* MATITA 1.0
      let dbd = LibraryDb.instance () in
      let graph =
        match direction with
        | `Fwd -> MetadataDeps.DepGraph.direct_deps ~dbd uri
        | `Back -> MetadataDeps.DepGraph.inverse_deps ~dbd uri in
      gviz_graph <- graph;  (** XXX check this for memory consuption *)
      self#redraw_gviz ~center_on:uri ();
      self#_showGviz *)

    method private coerchgraph tred () =
      load_coerchgraph tred ();
      self#_showGviz

    method private hints () =
      load_hints ();
      self#_showGviz

    method private tex () =
      let b = Buffer.create 1000 in
      Printf.bprintf b "UTF-8 equivalence classes (rotate with ALT-L):\n\n";
      List.iter 
        (fun l ->
           List.iter (fun sym ->
             Printf.bprintf b "  %s" (Glib.Utf8.from_unichar sym) 
           ) l;
           Printf.bprintf b "\n";
        )
        (List.sort 
          (fun l1 l2 -> compare (List.hd l1) (List.hd l2))
          (Virtuals.get_all_eqclass ()));
      Printf.bprintf b "\n\nVirtual keys (trigger with ALT-L):\n\n";
      List.iter 
        (fun tag, items -> 
           Printf.bprintf b "  %s:\n" tag;
           List.iter 
             (fun names, symbol ->
                Printf.bprintf b "  \t%s\t%s\n" 
                  (Glib.Utf8.from_unichar symbol)
                  (String.concat ", " names))
             (List.sort 
               (fun (_,a) (_,b) -> compare a b)
               items);
           Printf.bprintf b "\n")
        (List.sort 
          (fun (a,_) (b,_) -> compare a b)
          (Virtuals.get_all_virtuals ()));
      self#_loadText (Buffer.contents b)

    method private _loadText text =
      searchText#source_buffer#set_text text;
      win#entrySearch#misc#grab_focus ();
      self#_showSearch

    method private grammar () =
      self#_loadText
       (Print_grammar.ebnf_of_term (get_matita_script_current ())#status);

    method private home () =
      self#_showMath;
      let status = (get_matita_script_current ())#status in
       match status#ng_mode with
          `ProofMode -> self#_loadNObj status status#obj
        | _ -> self#blank ()

    method private _loadNReference (NReference.Ref (uri,_)) =
      let status = (get_matita_script_current ())#status in
      let obj = NCicEnvironment.get_checked_obj status uri in
      self#_loadNObj status obj

    method private _loadDir dir = 
      let content = Http_getter.ls ~local:false dir in
      let l =
        List.fast_sort
          Pervasives.compare
          (List.map
            (function 
              | Http_getter_types.Ls_section s -> "dir", s
              | Http_getter_types.Ls_object o -> "obj", o.Http_getter_types.uri)
            content)
      in
      lastDir <- dir;
      self#_loadList l

    method private setEntry entry =
      win#browserUri#set_text (MatitaTypes.string_of_entry entry);
      current_entry <- entry

    method private _loadNObj status obj =
      (* showMath must be done _before_ loading the document, since if the
       * widget is not mapped (hidden by the notebook) the document is not
       * rendered *)
      self#_showMath;
      mathView#load_nobject status obj

    method private _loadTermNCic term m s c =
      let d = 0 in
      let m = (0,([],c,term))::m in
      let status = (get_matita_script_current ())#status in
      mathView#nload_sequent status m s d;
      self#_showMath

    method private _loadList l =
      model#list_store#clear ();
      List.iter (fun (tag, s) -> model#easy_append ~tag s) l;
      self#_showList

    (** { public methods, all must call _load!! } *)
      
    method load entry =
      handle_error (fun () -> self#_load entry; self#_historyAdd entry)

    (**  this is what the browser does when you enter a string an hit enter *)
    method loadInput txt =
      let txt = HExtlib.trim_blanks txt in
      (* (* ZACK: what the heck? *)
      let fix_uri txt =
        UriManager.string_of_uri
          (UriManager.strip_xpointer (UriManager.uri_of_string txt))
      in
      *)
        let entry =
          match txt with
          | txt when is_uri txt ->
              `NRef (NReference.reference_of_string ((*fix_uri*) txt))
          | txt when is_dir txt -> `Dir (MatitaMisc.normalize_dir txt)
          | txt ->
             (try
               MatitaTypes.entry_of_string txt
              with Invalid_argument _ ->
               raise
                (GrafiteTypes.Command_error(sprintf "unsupported uri: %s" txt)))
        in
        self#_load entry;
        self#_historyAdd entry

      (** {2 methods used by constructor only} *)

    method win = win
    method history = history
    method currentEntry = current_entry
    method refresh ~force () = self#_load ~force current_entry

  end
  
let sequentsViewer ~(notebook:GPack.notebook) ~(cicMathView:cicMathView) ():
  MatitaGuiTypes.sequentsViewer
=
  (new sequentsViewer ~notebook ~cicMathView ():> MatitaGuiTypes.sequentsViewer)

let new_cicBrowser () =
  let size = BuildTimeConf.browser_history_size in
  let rec aux history =
    let browser = new cicBrowser_impl ~history () in
    let win = browser#win in
    ignore (win#browserNewButton#connect#clicked (fun () ->
      let history =
        new MatitaMisc.browser_history ~memento:history#save size
          (`About `Blank)
      in
      let newBrowser = aux history in
      newBrowser#load browser#currentEntry));
(*
      (* attempt (failed) to close windows on CTRL-W ... *)
    MatitaGtkMisc.connect_key win#browserWinEventBox#event ~modifiers:[`CONTROL]
      GdkKeysyms._W (fun () -> win#toplevel#destroy ());
*)
    cicBrowsers := browser :: !cicBrowsers;
    browser
  in
  let history = new MatitaMisc.browser_history size (`About `Blank) in
  aux history

(** @param reuse if set reused last opened cic browser otherwise 
*  opens a new one. default is false *)
let cicBrowser ?(reuse=false) t =
 let browser =
  if reuse then
   (match !cicBrowsers with [] -> new_cicBrowser () | b :: _ -> b)
  else
   new_cicBrowser ()
 in
  match t with
     None -> ()
   | Some t -> browser#load t
;;

let default_cicMathView () =
 let res = cicMathView ~show:true () in
  res#set_href_callback
    (Some (fun uri ->
      let uri = `NRef (NReference.reference_of_string uri) in
       cicBrowser (Some uri)));
  res

let cicMathView_instance =
 MatitaMisc.singleton default_cicMathView

let default_sequentsViewer notebook =
  let cicMathView = cicMathView_instance () in
  sequentsViewer ~notebook ~cicMathView ()

let sequentsViewer_instance =
 let already_used = ref false in
  fun notebook ->
   if !already_used then assert false
   else
    (already_used := true;
     default_sequentsViewer notebook)

let refresh_all_browsers () =
  List.iter (fun b -> b#refresh ~force:false ()) !cicBrowsers

let get_math_views () =
  (cicMathView_instance ()) :: (List.map (fun b -> b#mathView) !cicBrowsers)

let find_selection_owner () =
  let rec aux =
    function
    | [] -> raise Not_found
    | mv :: tl ->
        (match mv#get_selections with
        | [] -> aux tl
        | sel :: _ -> mv)
  in
  aux (get_math_views ())

let has_selection () =
  try ignore (find_selection_owner ()); true
  with Not_found -> false

let math_view_clipboard = ref None (* associative list target -> string *)
let has_clipboard () = !math_view_clipboard <> None
let empty_clipboard () = math_view_clipboard := None

let copy_selection () =
  try
    math_view_clipboard :=
      Some ((find_selection_owner ())#strings_of_selection)
  with Not_found -> failwith "no selection"

let paste_clipboard paste_kind =
  match !math_view_clipboard with
  | None -> failwith "empty clipboard"
  | Some cb ->
      (try List.assoc paste_kind cb with Not_found -> assert false)

