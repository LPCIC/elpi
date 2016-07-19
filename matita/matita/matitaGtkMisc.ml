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

(* $Id: matitaGtkMisc.ml 11179 2011-01-11 22:25:40Z tassi $ *)

exception PopupClosed
open Printf

let wrap_callback0 f = fun _ -> try f () with Not_found -> assert false
let wrap_callback1 f = fun _ -> try f () with Not_found -> assert false
let wrap_callback2 f = fun _ -> try f () with Not_found -> assert false

let connect_button (button: #GButton.button) callback =
  ignore (button#connect#clicked (wrap_callback0 callback))

let connect_toggle_button (button: #GButton.toggle_button) callback =
  ignore (button#connect#toggled (wrap_callback1 callback))

let connect_menu_item (menu_item: #GMenu.menu_item) callback =
  ignore (menu_item#connect#activate (wrap_callback2 callback))

let connect_key (ev:GObj.event_ops) ?(modifiers = []) ?(stop = false) key
  callback
=
  ignore (ev#connect#key_press (fun key' ->
    let modifiers' = GdkEvent.Key.state key' in
    (match key' with
    | key' when GdkEvent.Key.keyval key' = key
          && List.for_all (fun m -> List.mem m modifiers') modifiers ->
        callback ();
        stop
    | _ -> false)))

let toggle_widget_visibility ~(widget: GObj.widget) 
                              ~(check: GMenu.check_menu_item) 
=
  ignore (check#connect#toggled (fun _ ->
    if check#active then widget#misc#show () else widget#misc#hide ()))

let toggle_window_visibility ~(window: GWindow.window) 
                              ~(check: GMenu.check_menu_item) 
=
  ignore (check#connect#toggled (fun _ ->
    if check#active then window#show () else window#misc#hide ()));
  ignore (window#event#connect#delete (fun _ ->
    window#misc#hide ();
    check#set_active false;
    true))

let toggle_win ?(check: GMenu.check_menu_item option) (win: GWindow.window) () =
  if win#is_active then win#misc#hide () else win#show ();
  match check with
  | None -> ()
  | Some check -> check#set_active (not check#active)

let toggle_callback ~callback ~(check: GMenu.check_menu_item) =
  ignore (check#connect#toggled (fun _ -> callback check#active))
  
class multiStringListModel ~cols (tree_view: GTree.view) =
  let column_list = new GTree.column_list in
  let text_columns = 
    let rec aux = function
      | 0 -> []
      | n -> column_list#add Gobject.Data.string :: aux (n - 1)
    in
    aux cols
  in
  let list_store = GTree.list_store column_list in
  let renderers = 
    List.map
    (fun text_column -> 
      (GTree.cell_renderer_text [], ["text", text_column]))
    text_columns
  in
  let view_columns = 
    List.map 
      (fun renderer -> GTree.view_column ~renderer ())
      renderers
  in
  object (self)
    val text_columns = text_columns
    
    initializer
      tree_view#set_model (Some (list_store :> GTree.model));
      List.iter
        (fun view_column -> ignore (tree_view#append_column view_column)) 
        view_columns

    method list_store = list_store

    method easy_mappend slist =
      let tree_iter = list_store#append () in
      List.iter2 
        (fun s text_column ->
        list_store#set ~row:tree_iter ~column:text_column s)
        slist text_columns

    method easy_minsert pos s =
      let tree_iter = list_store#insert pos in
      List.iter2 
        (fun s text_column ->
        list_store#set ~row:tree_iter ~column:text_column s)
        s text_columns

    method easy_mselection () =
      List.map
        (fun tree_path ->
          let iter = list_store#get_iter tree_path in
          List.map 
            (fun text_column -> 
            list_store#get ~row:iter ~column:text_column) 
          text_columns)
        tree_view#selection#get_selected_rows
  end

class stringListModel (tree_view: GTree.view) =
  object (self)
    inherit multiStringListModel ~cols:1 tree_view as multi

    method list_store = multi#list_store

    method easy_append s =
      multi#easy_mappend [s]

    method easy_insert pos s =
      multi#easy_minsert pos [s]

    method easy_selection () =
      let m = List.map
        (fun tree_path ->
          let iter = self#list_store#get_iter tree_path in
          List.map 
            (fun text_column -> 
            self#list_store#get ~row:iter ~column:text_column) 
          text_columns)
        tree_view#selection#get_selected_rows
      in
      List.map (function [x] -> x | _ -> assert false) m
  end

class taggedStringListModel ~(tags:(string * GdkPixbuf.pixbuf) list)
  (tree_view: GTree.view)
=
  let column_list = new GTree.column_list in
  let tag_column = column_list#add Gobject.Data.gobject in
  let text_column = column_list#add Gobject.Data.string in
  let list_store = GTree.list_store column_list in
  let text_renderer = (GTree.cell_renderer_text [], ["text", text_column]) in
  let tag_renderer = (GTree.cell_renderer_pixbuf [], ["pixbuf", tag_column]) in
  let text_vcolumn = GTree.view_column ~renderer:text_renderer () in
  let tag_vcolumn = GTree.view_column ~renderer:tag_renderer () in
  let lookup_pixbuf tag =
    try List.assoc tag tags with Not_found -> assert false
  in
  object (self)
    initializer
      tree_view#set_model (Some (list_store :> GTree.model));
      ignore (tree_view#append_column tag_vcolumn);
      ignore (tree_view#append_column text_vcolumn)

    method list_store = list_store

    method easy_append ~tag s =
      let tree_iter = list_store#append () in
      list_store#set ~row:tree_iter ~column:text_column s;
      list_store#set ~row:tree_iter ~column:tag_column (lookup_pixbuf tag)

    method easy_insert pos ~tag s =
      let tree_iter = list_store#insert pos in
      list_store#set ~row:tree_iter ~column:text_column s;
      list_store#set ~row:tree_iter ~column:tag_column (lookup_pixbuf tag)

    method easy_selection () =
      List.map
        (fun tree_path ->
          let iter = list_store#get_iter tree_path in
          list_store#get ~row:iter ~column:text_column)
        tree_view#selection#get_selected_rows
  end

class recordModel (tree_view:GTree.view) =
  let cols_list = new GTree.column_list in
  let text_col = cols_list#add Gobject.Data.string in
(*   let combo_col = cols_list#add (Gobject.Data.gobject_by_name "GtkListStore") in *)
  let combo_col = cols_list#add Gobject.Data.int in
  let toggle_col = cols_list#add Gobject.Data.boolean in
  let list_store = GTree.list_store cols_list in
  let text_rend = (GTree.cell_renderer_text [], ["text", text_col]) in
  let combo_rend = GTree.cell_renderer_combo [] in
(*   let combo_rend = (GTree.cell_renderer_combo [], [|+"model", combo_col+|]) in *)
  let toggle_rend =
    (GTree.cell_renderer_toggle [`ACTIVATABLE true], ["active", toggle_col])
  in
  let text_vcol = GTree.view_column ~renderer:text_rend () in
  let combo_vcol = GTree.view_column ~renderer:(combo_rend, []) () in
  let _ =
    combo_vcol#set_cell_data_func combo_rend
      (fun _ _ ->
        prerr_endline "qui";
        let model, col =
          GTree.store_of_list Gobject.Data.string ["a"; "b"; "c"]
        in
        combo_rend#set_properties [
          `MODEL (Some (model :> GTree.model));
          `TEXT_COLUMN col
        ])
  in
  let toggle_vcol = GTree.view_column ~renderer:toggle_rend () in
  object (self)
    initializer
      tree_view#set_model (Some (list_store :> GTree.model));
      ignore (tree_view#append_column text_vcol);
      ignore (tree_view#append_column combo_vcol);
      ignore (tree_view#append_column toggle_vcol)

    method list_store = list_store

    method easy_append s (combo:int) (toggle:bool) =
      let tree_iter = list_store#append () in
      list_store#set ~row:tree_iter ~column:text_col s;
      list_store#set ~row:tree_iter ~column:combo_col combo;
      list_store#set ~row:tree_iter ~column:toggle_col toggle
  end

class type gui =
  object
    method newUriDialog:          unit -> MatitaGeneratedGui.uriChoiceDialog
    method newConfirmationDialog: unit -> MatitaGeneratedGui.confirmationDialog
    method newEmptyDialog:        unit -> MatitaGeneratedGui.emptyDialog
  end

let popup_message 
  ~title ~message ~buttons ~callback
  ?(message_type=`QUESTION) ?parent ?(use_markup=true)
  ?(destroy_with_parent=true) ?(allow_grow=false) ?(allow_shrink=false)
  ?icon ?(modal=true) ?(resizable=false) ?screen ?type_hint
  ?(position=`CENTER_ON_PARENT) ?wm_name ?wm_class ?border_width ?width 
  ?height ?(show=true) ()
=
  let m = 
    GWindow.message_dialog 
      ~message ~use_markup ~message_type ~buttons ?parent ~destroy_with_parent 
      ~title ~allow_grow ~allow_shrink ?icon ~modal ~resizable ?screen 
      ?type_hint ~position ?wm_name ?wm_class ?border_width ?width ?height 
      ~show () 
  in 
  ignore(m#connect#response 
    ~callback:(fun a ->  GMain.Main.quit ();callback a));
  ignore(m#connect#close 
    ~callback:(fun _ -> GMain.Main.quit ();raise PopupClosed));
  GtkThread.main ();
  m#destroy () 

let popup_message_lowlevel
  ~title ~message ?(no_separator=true) ~callback ~message_type ~buttons
  ?parent  ?(destroy_with_parent=true) ?(allow_grow=false) ?(allow_shrink=false)
  ?icon ?(modal=true) ?(resizable=false) ?screen ?type_hint
  ?(position=`CENTER_ON_PARENT) ?wm_name ?wm_class ?border_width ?width 
  ?height ?(show=true) ()
=
  let m = 
    GWindow.dialog 
      ~no_separator 
      ?parent ~destroy_with_parent 
      ~title ~allow_grow ~allow_shrink ?icon ~modal ~resizable ?screen 
      ?type_hint ~position ?wm_name ?wm_class ?border_width ?width ?height 
      ~show:false () 
  in
  let stock = 
    match message_type with
    | `WARNING -> `DIALOG_WARNING
    | `INFO -> `DIALOG_INFO
    | `ERROR ->`DIALOG_ERROR 
    | `QUESTION -> `DIALOG_QUESTION
  in
  let image = GMisc.image ~stock ~icon_size:`DIALOG () in
  let label = GMisc.label ~markup:message () in
  label#set_line_wrap true;
  let hbox = GPack.hbox ~spacing:10 () in
  hbox#pack ~from:`START ~expand:true ~fill:true (image:>GObj.widget);
  hbox#pack ~from:`START ~expand:true ~fill:true (label:>GObj.widget);
  m#vbox#pack ~from:`START 
    ~padding:20 ~expand:true ~fill:true (hbox:>GObj.widget);
  List.iter (fun (x, y) -> 
    m#add_button_stock x y;
    if y = `CANCEL then 
      m#set_default_response y
  ) buttons;
  ignore(m#connect#response 
    ~callback:(fun a ->  GMain.Main.quit ();callback a));
  ignore(m#connect#close 
    ~callback:(fun _ -> GMain.Main.quit ();callback `POPUPCLOSED));
  if show = true then 
      m#show ();
  GtkThread.main ();
  m#destroy () 


let ask_confirmation ~title ~message ?parent () =
  let rc = ref `YES in
  let callback = 
    function 
    | `YES -> rc := `YES
    | `NO -> rc := `NO
    | `CANCEL -> rc := `CANCEL
    | `DELETE_EVENT -> rc := `CANCEL
    | `POPUPCLOSED -> rc := `CANCEL
  in
  let buttons = [`YES,`YES ; `NO,`NO ; `CANCEL,`CANCEL] in
    popup_message_lowlevel 
      ~title ~message ~message_type:`WARNING ~callback ~buttons ?parent ();
    !rc

let report_error ~title ~message ?parent () =
  let callback _ = () in
  let buttons = GWindow.Buttons.ok in
  try 
    popup_message 
      ~title ~message ~message_type:`ERROR ~callback ~buttons ?parent ()
  with
  | PopupClosed -> ()


let ask_text ~(gui:#gui) ?(title = "") ?(message = "") ?(multiline = false)
  ?default ()
=
  let dialog = gui#newEmptyDialog () in
  dialog#emptyDialog#set_title title;
  dialog#emptyDialogLabel#set_label message;
  let result = ref None in
  let return r =
    result := r;
    dialog#emptyDialog#destroy ();
    GMain.Main.quit ()
  in
  ignore (dialog#emptyDialog#event#connect#delete (fun _ -> true));
  if multiline then begin (* multiline input required: use a TextView widget *)
    let win =
      GBin.scrolled_window ~width:400 ~height:150 ~hpolicy:`NEVER
        ~vpolicy:`ALWAYS ~packing:dialog#emptyDialogVBox#add ()
    in
    let view = GText.view ~wrap_mode:`CHAR ~packing:win#add () in
    let buffer = view#buffer in
    (match default with
    | None -> ()
    | Some text ->
        buffer#set_text text;
        buffer#select_range buffer#start_iter buffer#end_iter);
    view#misc#grab_focus ();
    connect_button dialog#emptyDialogOkButton (fun _ ->
      return (Some (buffer#get_text ())))
  end else begin (* monoline input required: use a TextEntry widget *)
    let entry = GEdit.entry ~packing:dialog#emptyDialogVBox#add () in
    (match default with
    | None -> ()
    | Some text ->
        entry#set_text text;
        entry#select_region ~start:0 ~stop:max_int);
    entry#misc#grab_focus ();
    connect_button dialog#emptyDialogOkButton (fun _ ->
      return (Some entry#text))
  end;
  connect_button dialog#emptyDialogCancelButton (fun _ ->return None);
  dialog#emptyDialog#show ();
  GtkThread.main ();
  (match !result with None -> raise MatitaTypes.Cancel | Some r -> r)

let utf8_parsed_text s floc = 
  let start, stop = HExtlib.loc_of_floc floc in
  let start_bytes = Glib.Utf8.offset_to_pos s ~pos:0 ~off:start in
  let stop_bytes = Glib.Utf8.offset_to_pos s ~pos:0 ~off:stop in
  if (stop_bytes < start_bytes) then
    Printf.sprintf "ERROR (%d > %d)" start_bytes stop_bytes, 0
  else
  let bytes = stop_bytes - start_bytes in
  try
    String.sub s start_bytes bytes, bytes
  with Invalid_argument _ -> 
    Printf.sprintf "ERROR (%s/%d/%d)" s start_bytes bytes, 0
  
let utf8_string_length s = 
  if BuildTimeConf.debug then
    assert(Glib.Utf8.validate s);
  Glib.Utf8.length s

let escape_pango_markup text =
   let text = Pcre.replace ~pat:"&" ~templ:"&amp;" text in
   let text = Pcre.replace ~pat:"<" ~templ:"&lt;" text in
   let text = Pcre.replace ~pat:"'" ~templ:"&apos;" text in
   let text = Pcre.replace ~pat:"\"" ~templ:"&quot;" text in
   text
;;

let matita_lang =
 let source_language_manager =
  GSourceView2.source_language_manager ~default:true in
 source_language_manager#set_search_path
  (BuildTimeConf.runtime_base_dir ::
    source_language_manager#search_path);
 match source_language_manager#language "grafite" with
 | None ->
     HLog.error(sprintf "can't load a language file for \"grafite\" in %s"
      BuildTimeConf.runtime_base_dir);
     assert false
 | Some x -> x
;;
