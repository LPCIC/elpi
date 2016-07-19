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

(* $Id: matitaScript.ml 13100 2015-10-29 22:46:45Z fguidi $ *)

open Printf
open GrafiteTypes

module TA = GrafiteAst

let debug = false
let debug_print = if debug then prerr_endline else ignore

  (** raised when one of the script margins (top or bottom) is reached *)
exception Margin
exception NoUnfinishedProof
exception ActionCancelled of string

let safe_substring s i j =
  try String.sub s i j with Invalid_argument _ -> assert false

let heading_nl_RE = Pcre.regexp "^\\s*\n\\s*"
let heading_nl_RE' = Pcre.regexp "^(\\s*\n\\s*)"
let only_dust_RE = Pcre.regexp "^(\\s|\n|%%[^\n]*\n)*$"
let multiline_RE = Pcre.regexp "^\n[^\n]+$"
let newline_RE = Pcre.regexp "\n"
let comment_RE = Pcre.regexp "\\(\\*(.|\n)*\\*\\)\n?" ~flags:[`UNGREEDY]
 
let comment str =
  if Pcre.pmatch ~rex:multiline_RE str then
    "\n(** " ^ (Pcre.replace ~rex:newline_RE str) ^ " *)"
  else
    "\n(**\n" ^ str ^ "\n*)"

let strip_comments str =
  Pcre.qreplace ~templ:"\n" ~pat:"\n\n" (Pcre.qreplace ~rex:comment_RE str)
;;
                     
let first_line s =
  let s = Pcre.replace ~rex:heading_nl_RE s in
  try
    let nl_pos = String.index s '\n' in
    String.sub s 0 nl_pos
  with Not_found -> s

let eval_with_engine include_paths status skipped_txt nonskipped_txt st
=
  let parsed_text_length =
    String.length skipped_txt + String.length nonskipped_txt 
  in
  let text = skipped_txt ^ nonskipped_txt in
  let prefix_len = MatitaGtkMisc.utf8_string_length skipped_txt in
  let enriched_history_fragment =
   MatitaEngine.eval_ast ~include_paths ~do_heavy_checks:(Helm_registry.get_bool
     "matita.do_heavy_checks")
    status (text,prefix_len,st)
  in
  let enriched_history_fragment = List.rev enriched_history_fragment in
  (* really fragile *)
  let res,_ = 
    List.fold_left 
      (fun (acc, to_prepend) (status,alias) ->
       match alias with
       | None -> (status,to_prepend ^ nonskipped_txt)::acc,""
       | Some (k,value) ->
            let newtxt = GrafiteAstPp.pp_alias value in
            (status,to_prepend ^ newtxt ^ "\n")::acc, "")
      ([],skipped_txt) enriched_history_fragment
  in
  res,"",parsed_text_length
;;

let pp_eager_statement_ast = GrafiteAstPp.pp_statement 

let eval_nmacro include_paths (buffer : GText.buffer) status unparsed_text parsed_text script mac =
  let parsed_text_length = String.length parsed_text in
  match mac with
  | TA.Screenshot (_,name) -> 
       let status = script#status in
       let _,_,menv,subst,_ = status#obj in
       let name = Filename.dirname (script#filename) ^ "/" ^ name in
       let sequents = 
         let selected = Continuationals.Stack.head_goals status#stack in
         List.filter (fun x,_ -> List.mem x selected) menv         
       in
       CicMathView.screenshot status sequents menv subst name;
       [status, parsed_text], "", parsed_text_length
  | TA.NCheck (_,t) ->
      let status = script#status in
      let _,_,menv,subst,_ = status#obj in
      let ctx = 
       match Continuationals.Stack.head_goals status#stack with
          [] -> []
        | g::tl ->
           if tl <> [] then
            HLog.warn
             "Many goals focused. Using the context of the first one\n";
           let ctx = try
             let _, ctx, _ = NCicUtils.lookup_meta g menv in ctx
             with NCicUtils.Meta_not_found _ -> 
               HLog.warn "Current goal is closed. Using empty context.";
               [ ]
           in ctx
      in
      let m, s, status, t = 
        GrafiteDisambiguate.disambiguate_nterm 
          status `XTNone ctx menv subst (parsed_text,parsed_text_length,
            NotationPt.Cast (t,NotationPt.Implicit `JustOne))  
          (* XXX use the metasenv, if possible *)
      in
      MatitaMathView.cicBrowser (Some (`NCic (t,ctx,m,s)));
      [status, parsed_text], "", parsed_text_length
  | TA.NIntroGuess _loc ->
      let names_ref = ref [] in
      let s = NTactics.intros_tac ~names_ref [] script#status in
      let rex = Pcre.regexp ~flags:[`MULTILINE] "\\A([\\n\\t\\r ]*).*\\Z" in
      let nl = Pcre.replace ~rex ~templ:"$1" parsed_text in
      [s, nl ^ "#" ^ String.concat " #" !names_ref], "", parsed_text_length
  | TA.NAutoInteractive (_loc, (None,a)) -> 
      let trace_ref = ref [] in
      let s = NnAuto.auto_tac ~params:(None,a) ~trace_ref script#status in
      let depth = 
        try List.assoc "depth" a
        with Not_found -> ""
      in
      let width = 
        try List.assoc "width" a
        with Not_found -> ""
      in
      let trace = "/"^(if int_of_string depth > 1 then depth ^ " width=" ^ width else "")^" by " in
      let thms = 
        match !trace_ref with
        | [] -> ""
        | thms -> 
           String.concat ", "  
             (HExtlib.filter_map (function 
               | NotationPt.NRef r -> Some (NCicPp.r2s status true r) 
               | _ -> None) 
             thms)
      in
      let rex = Pcre.regexp ~flags:[`MULTILINE] "\\A([\\n\\t\\r ]*).*\\Z" in
      let nl = Pcre.replace ~rex ~templ:"$1" parsed_text in
      [s, nl ^ trace ^ thms ^ "/"], "", parsed_text_length
  | TA.NAutoInteractive (_, (Some _,_)) -> assert false

let rec eval_executable include_paths (buffer : GText.buffer)
status unparsed_text skipped_txt nonskipped_txt script ex loc
=
  try
   ignore (buffer#move_mark (`NAME "beginning_of_statement")
    ~where:((buffer#get_iter_at_mark (`NAME "locked"))#forward_chars
       (Glib.Utf8.length skipped_txt))) ;
   eval_with_engine include_paths status skipped_txt nonskipped_txt
    (TA.Executable (loc, ex))
  with
     MatitaTypes.Cancel -> [], "", 0
   | GrafiteEngine.NMacro (_loc,macro) ->
       eval_nmacro include_paths buffer status
        unparsed_text (skipped_txt ^ nonskipped_txt) script macro


and eval_statement include_paths (buffer : GText.buffer) status script
 statement
=
  let st,unparsed_text =
    match statement with
    | `Raw text ->
        if Pcre.pmatch ~rex:only_dust_RE text then raise Margin;
        let strm =
         GrafiteParser.parsable_statement status
          (Ulexing.from_utf8_string text) in
        let ast = MatitaEngine.get_ast status include_paths strm in
         ast, text
    | `Ast (st, text) -> st, text
  in
  let text_of_loc floc = 
    let nonskipped_txt,_ = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    let start, stop = HExtlib.loc_of_floc floc in 
    let floc = HExtlib.floc_of_loc (0, start) in
    let skipped_txt,_ = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    let floc = HExtlib.floc_of_loc (0, stop) in
    let txt,len = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    txt,nonskipped_txt,skipped_txt,len
  in 
  match st with
  | GrafiteAst.Executable (loc, ex) ->
     let _, nonskipped, skipped, parsed_text_length = text_of_loc loc in
      eval_executable include_paths buffer status unparsed_text
       skipped nonskipped script ex loc
  | GrafiteAst.Comment (loc, GrafiteAst.Code (_, ex))
    when Helm_registry.get_bool "matita.execcomments" ->
     let _, nonskipped, skipped, parsed_text_length = text_of_loc loc in
      eval_executable include_paths buffer status unparsed_text
       skipped nonskipped script ex loc
  | GrafiteAst.Comment (loc, _) -> 
      let parsed_text, _, _, parsed_text_length = text_of_loc loc in
      let remain_len = String.length unparsed_text - parsed_text_length in
      let s = String.sub unparsed_text parsed_text_length remain_len in
      let s,text,len = 
       try
        eval_statement include_paths buffer status script (`Raw s)
       with
          HExtlib.Localized (floc, exn) ->
           HExtlib.raise_localized_exception 
             ~offset:(MatitaGtkMisc.utf8_string_length parsed_text) floc exn
        | MultiPassDisambiguator.DisambiguationError (offset,errorll) ->
           raise
            (MultiPassDisambiguator.DisambiguationError
              (offset+parsed_text_length, errorll))
      in
      assert (text=""); (* no macros inside comments, please! *)
      (match s with
      | (statuses,text)::tl ->
         (statuses,parsed_text ^ text)::tl,"",parsed_text_length + len
      | [] -> [], "", 0)
  
let fresh_script_id =
  let i = ref 0 in
  fun () -> incr i; !i

(** Selection handling
 * Two clipboards are used: "clipboard" and "primary".
 * "primary" is used by X, when you hit the middle button mouse is content is
 *    pasted between applications. In Matita this selection always contain the
 *    textual version of the selected term.
 * "clipboard" is used inside Matita only and support ATM two different targets:
 *    "TERM" and "PATTERN", in the future other targets like "MATHMLCONTENT" may
 *    be added
 *)
class script ~(parent:GBin.scrolled_window) ~tab_label () =
let source_view =
  GSourceView2.source_view
    ~auto_indent:true
    ~insert_spaces_instead_of_tabs:true ~tab_width:2
    ~right_margin_position:80 ~show_right_margin:true
    ~smart_home_end:`AFTER
    ~packing:parent#add
    () in
let buffer = source_view#buffer in
let source_buffer = source_view#source_buffer in
let similarsymbols_tag_name = "similarsymbolos" in
let similarsymbols_tag = `NAME similarsymbols_tag_name in
let initial_statuses current baseuri =
 let status = new MatitaEngine.status baseuri in
 (match current with
     Some current -> NCicLibrary.time_travel status;
(*
      (* MATITA 1.0: there is a known bug in invalidation; temporary fix here *)
      NCicEnvironment.invalidate () *)
   | None -> ());
  status
in
let default_buri = "cic:/matita/tests" in
let default_fname = ".unnamed.ma" in
object (self)
  val mutable include_paths_ = []
  val clipboard = GData.clipboard Gdk.Atom.clipboard
  (*val primary = GData.clipboard Gdk.Atom.primary*)
  val mutable similarsymbols = []
  val mutable similarsymbols_orig = []
  val similar_memory = Hashtbl.create 97
  val mutable old_used_memory = false

  val scriptId = fresh_script_id ()

  val mutable filename_ = (None : string option)

  method has_name = filename_ <> None

  method source_view = source_view
  
  method include_paths =
    include_paths_ @ 
    Helm_registry.get_list Helm_registry.string "matita.includes"

  method private curdir =
    try
     let root, _buri, _fname, _tgt = 
      Librarian.baseuri_of_script ~include_paths:self#include_paths
       self#filename 
     in 
     root
    with Librarian.NoRootFor _ -> Sys.getcwd ()

  method buri_of_current_file =
    match filename_ with
    | None -> default_buri 
    | Some f ->
        try 
          let _root, buri, _fname, _tgt = 
            Librarian.baseuri_of_script ~include_paths:self#include_paths f 
          in 
          buri
        with Librarian.NoRootFor _ | Librarian.FileNotFound _ -> default_buri

  method filename = match filename_ with None -> default_fname | Some f -> f

  initializer 
    ignore
     (source_view#source_buffer#begin_not_undoable_action ();
      self#reset (); 
      self#template (); 
      source_view#source_buffer#end_not_undoable_action ());
    MatitaMisc.observe_font_size (fun font_size ->
     source_view#misc#modify_font_by_name
        (sprintf "%s %d" BuildTimeConf.script_font font_size));
    source_view#misc#grab_focus ();
    ignore(source_view#source_buffer#set_language
     (Some MatitaGtkMisc.matita_lang));
    ignore(source_view#source_buffer#set_highlight_syntax true);
    ignore(source_view#connect#after#paste_clipboard 
        ~callback:(fun () -> self#clean_dirty_lock));
    ignore (GMain.Timeout.add ~ms:300000 
       ~callback:(fun _ -> self#_saveToBackupFile ();true));
    ignore (buffer#connect#modified_changed 
      (fun _ -> self#set_star buffer#modified));
    (* clean_locked is set to true only "during" a PRIMARY paste
       operation (i.e. by clicking with the second mouse button) *)
    let clean_locked = ref false in
    ignore(source_view#event#connect#button_press
      ~callback:
        (fun button ->
          if GdkEvent.Button.button button = 2 then
           clean_locked := true;
          false
        ));
    ignore(source_view#event#connect#button_release
      ~callback:(fun button -> clean_locked := false; false));
    ignore(source_view#buffer#connect#after#apply_tag
     ~callback:(
       fun tag ~start:_ ~stop:_ ->
        if !clean_locked &&
           tag#get_oid = self#locked_tag#get_oid
        then
         begin
          clean_locked := false;
          self#clean_dirty_lock;
          clean_locked := true
         end));
    ignore(source_view#source_buffer#connect#after#insert_text 
     ~callback:(fun iter str -> 
        if (MatitaMisc.get_gui ())#main#menuitemAutoAltL#active && (str = " " || str = "\n") then 
          ignore(self#expand_virtual_if_any iter str)));
    ignore(source_view#connect#after#populate_popup
     ~callback:(fun pre_menu ->
       let menu = new GMenu.menu pre_menu in
       let menuItems = menu#children in
       let undoMenuItem, redoMenuItem =
        match menuItems with
           [undo;redo;sep1;cut;copy;paste;delete;sep2;
            selectall;sep3;inputmethod;insertunicodecharacter] ->
              List.iter menu#remove [ copy; cut; delete; paste ];
              undo,redo
         | _ -> assert false in
       let add_menu_item =
         let i = ref 2 in (* last occupied position *)
         fun ?label ?stock () ->
           incr i;
           GMenu.image_menu_item ?label ?stock ~packing:(menu#insert ~pos:!i)
            ()
       in
       let copy = add_menu_item ~stock:`COPY () in
       let cut = add_menu_item ~stock:`CUT () in
       let delete = add_menu_item ~stock:`DELETE () in
       let paste = add_menu_item ~stock:`PASTE () in
       let paste_pattern = add_menu_item ~label:"Paste as pattern" () in
       copy#misc#set_sensitive self#canCopy;
       cut#misc#set_sensitive self#canCut;
       delete#misc#set_sensitive self#canDelete;
       paste#misc#set_sensitive self#canPaste;
       paste_pattern#misc#set_sensitive self#canPastePattern;
       MatitaGtkMisc.connect_menu_item copy self#copy;
       MatitaGtkMisc.connect_menu_item cut self#cut;
       MatitaGtkMisc.connect_menu_item delete self#delete;
       MatitaGtkMisc.connect_menu_item paste self#paste;
       MatitaGtkMisc.connect_menu_item paste_pattern self#pastePattern;
       let new_undoMenuItem =
        GMenu.image_menu_item
         ~image:(GMisc.image ~stock:`UNDO ())
         ~use_mnemonic:true
         ~label:"_Undo"
         ~packing:(menu#insert ~pos:0) () in
       new_undoMenuItem#misc#set_sensitive
        (undoMenuItem#misc#get_flag `SENSITIVE);
       menu#remove (undoMenuItem :> GMenu.menu_item);
       MatitaGtkMisc.connect_menu_item new_undoMenuItem
        (fun () -> self#safe_undo);
       let new_redoMenuItem =
        GMenu.image_menu_item
         ~image:(GMisc.image ~stock:`REDO ())
         ~use_mnemonic:true
         ~label:"_Redo"
         ~packing:(menu#insert ~pos:1) () in
       new_redoMenuItem#misc#set_sensitive
        (redoMenuItem#misc#get_flag `SENSITIVE);
        menu#remove (redoMenuItem :> GMenu.menu_item);
        MatitaGtkMisc.connect_menu_item new_redoMenuItem
         (fun () -> self#safe_redo)));

  val mutable statements = []    (** executed statements *)

  val mutable history = [ initial_statuses None default_buri ]
    (** list of states before having executed statements. Head element of this
      * list is the current state, last element is the state at the beginning of
      * the script.
      * Invariant: this list length is 1 + length of statements *)

  (** text mark and tag representing locked part of a script *)
  val locked_mark =
    buffer#create_mark ~name:"locked" ~left_gravity:true buffer#start_iter
  val beginning_of_statement_mark =
    buffer#create_mark ~name:"beginning_of_statement"
     ~left_gravity:true buffer#start_iter
  val locked_tag = buffer#create_tag [`BACKGROUND "lightblue"; `EDITABLE false]
  val error_tag = buffer#create_tag [`UNDERLINE `SINGLE; `FOREGROUND "red"]

  (** unicode handling *)
  method nextSimilarSymbol = 
    let write_similarsymbol s =
      let s = Glib.Utf8.from_unichar s in
      let iter = source_view#source_buffer#get_iter_at_mark `INSERT in
      assert(Glib.Utf8.validate s);
      source_view#source_buffer#delete ~start:iter ~stop:(iter#copy#backward_chars 1);
      source_view#source_buffer#insert ~iter:(source_view#source_buffer#get_iter_at_mark `INSERT) s;
      (try source_view#source_buffer#delete_mark similarsymbols_tag
       with GText.No_such_mark _ -> ());
      ignore(source_view#source_buffer#create_mark ~name:similarsymbols_tag_name
        (source_view#source_buffer#get_iter_at_mark `INSERT));
    in
    let new_similarsymbol =
      try
        let iter_ins = source_view#source_buffer#get_iter_at_mark `INSERT in
        let iter_lig = source_view#source_buffer#get_iter_at_mark similarsymbols_tag in
        not (iter_ins#equal iter_lig)
      with GText.No_such_mark _ -> true
    in
    if new_similarsymbol then
      (if not(self#expand_virtual_if_any (source_view#source_buffer#get_iter_at_mark `INSERT) "")then
        let last_symbol = 
          let i = source_view#source_buffer#get_iter_at_mark `INSERT in
          Glib.Utf8.first_char (i#get_slice ~stop:(i#copy#backward_chars 1))
        in
        (match Virtuals.similar_symbols last_symbol with
        | [] ->  ()
        | eqclass ->
            similarsymbols_orig <- eqclass;
            let is_used = 
              try Hashtbl.find similar_memory similarsymbols_orig  
              with Not_found -> 
                let is_used = List.map (fun x -> x,false) eqclass in
                Hashtbl.add similar_memory eqclass is_used; 
                is_used
            in
            let hd, next, tl = 
              let used, unused = 
                List.partition (fun s -> List.assoc s is_used) eqclass 
              in
              match used @ unused with a::b::c -> a,b,c | _ -> assert false
            in
            let hd, tl = 
              if hd = last_symbol then next, tl @ [hd] else hd, (next::tl)
            in
            old_used_memory <- List.assoc hd is_used;
            let is_used = 
              (hd,true) :: List.filter (fun (x,_) -> x <> hd) is_used
            in
            Hashtbl.replace similar_memory similarsymbols_orig is_used;
            write_similarsymbol hd;
            similarsymbols <- tl @ [ hd ]))
    else 
      match similarsymbols with
      | [] -> ()
      | hd :: tl ->
          let is_used = Hashtbl.find similar_memory similarsymbols_orig in
          let last = HExtlib.list_last tl in
          let old_used_for_last = old_used_memory in
          old_used_memory <- List.assoc hd is_used;
          let is_used = 
            (hd, true) :: (last,old_used_for_last) ::
              List.filter (fun (x,_) -> x <> last && x <> hd) is_used 
          in
          Hashtbl.replace similar_memory similarsymbols_orig is_used;
          similarsymbols <- tl @ [ hd ];
          write_similarsymbol hd

  method private reset_similarsymbols =
   similarsymbols <- []; 
   similarsymbols_orig <- []; 
   try source_view#source_buffer#delete_mark similarsymbols_tag
   with GText.No_such_mark _ -> ()
 
  method private expand_virtual_if_any iter tok =
    try
     let len = MatitaGtkMisc.utf8_string_length tok in
     let last_word =
      let prev = iter#copy#backward_chars len in
       prev#get_slice ~stop:(prev#copy#backward_find_char 
        (fun x -> Glib.Unichar.isspace x || x = Glib.Utf8.first_char "\\"))
     in
     let inplaceof, symb = Virtuals.symbol_of_virtual last_word in
     self#reset_similarsymbols;
     let s = Glib.Utf8.from_unichar symb in
     assert(Glib.Utf8.validate s);
     source_view#source_buffer#delete ~start:iter 
       ~stop:(iter#copy#backward_chars
         (MatitaGtkMisc.utf8_string_length inplaceof + len));
     source_view#source_buffer#insert ~iter
       (if inplaceof.[0] = '\\' then s else (s ^ tok));
     true
    with Virtuals.Not_a_virtual -> false
    
  (** selections / clipboards handling *)

  method markupSelected = MatitaMathView.has_selection ()
  method private textSelected =
    (source_view#source_buffer#get_iter_at_mark `INSERT)#compare
      (source_view#source_buffer#get_iter_at_mark `SEL_BOUND) <> 0
  method private markupStored = MatitaMathView.has_clipboard ()
  method private textStored = clipboard#text <> None
  method canCopy = self#textSelected
  method canCut = self#textSelected
  method canDelete = self#textSelected
  (*CSC: WRONG CODE: we should look in the clipboard instead! *)
  method canPaste = self#markupStored || self#textStored
  method canPastePattern = self#markupStored

  method safe_undo =
   (* phase 1: we save the actual status of the marks and we undo *)
   let locked_mark = `MARK (self#locked_mark) in
   let locked_iter = source_view#buffer#get_iter_at_mark locked_mark in
   let locked_iter_offset = locked_iter#offset in
   let mark2 =
    `MARK
      (source_view#buffer#create_mark ~name:"lock_point"
        ~left_gravity:true locked_iter) in
   source_view#source_buffer#undo ();
   (* phase 2: we save the cursor position and we redo, restoring
      the previous status of all the marks *)
   let cursor_iter = source_view#buffer#get_iter_at_mark `INSERT in
   let mark =
    `MARK
      (source_view#buffer#create_mark ~name:"undo_point"
        ~left_gravity:true cursor_iter)
   in
    source_view#source_buffer#redo ();
    let mark_iter = source_view#buffer#get_iter_at_mark mark in
    let mark2_iter = source_view#buffer#get_iter_at_mark mark2 in
    let mark2_iter = mark2_iter#set_offset locked_iter_offset in
     source_view#buffer#move_mark locked_mark ~where:mark2_iter;
     source_view#buffer#delete_mark mark;
     source_view#buffer#delete_mark mark2;
     (* phase 3: if after the undo the cursor was in the locked area,
        then we move it there again and we perform a goto *)
     if mark_iter#offset < locked_iter_offset then
      begin
       source_view#buffer#move_mark `INSERT ~where:mark_iter;
       self#goto `Cursor ();
      end;
     (* phase 4: we perform again the undo. This time we are sure that
        the text to undo is not locked *)
     source_view#source_buffer#undo ();
     source_view#misc#grab_focus ()

  method safe_redo =
   (* phase 1: we save the actual status of the marks, we redo and
      we undo *)
   let locked_mark = `MARK (self#locked_mark) in
   let locked_iter = source_view#buffer#get_iter_at_mark locked_mark in
   let locked_iter_offset = locked_iter#offset in
   let mark2 =
    `MARK
      (source_view#buffer#create_mark ~name:"lock_point"
        ~left_gravity:true locked_iter) in
   source_view#source_buffer#redo ();
   source_view#source_buffer#undo ();
   (* phase 2: we save the cursor position and we restore
      the previous status of all the marks *)
   let cursor_iter = source_view#buffer#get_iter_at_mark `INSERT in
   let mark =
    `MARK
      (source_view#buffer#create_mark ~name:"undo_point"
        ~left_gravity:true cursor_iter)
   in
    let mark_iter = source_view#buffer#get_iter_at_mark mark in
    let mark2_iter = source_view#buffer#get_iter_at_mark mark2 in
    let mark2_iter = mark2_iter#set_offset locked_iter_offset in
     source_view#buffer#move_mark locked_mark ~where:mark2_iter;
     source_view#buffer#delete_mark mark;
     source_view#buffer#delete_mark mark2;
     (* phase 3: if after the undo the cursor is in the locked area,
        then we move it there again and we perform a goto *)
     if mark_iter#offset < locked_iter_offset then
      begin
       source_view#buffer#move_mark `INSERT ~where:mark_iter;
       self#goto `Cursor ();
      end;
     (* phase 4: we perform again the redo. This time we are sure that
        the text to redo is not locked *)
     source_view#source_buffer#redo ();
     source_view#misc#grab_focus ()
   

  method copy () =
   if self#textSelected
   then begin
     MatitaMathView.empty_clipboard ();
     source_view#buffer#copy_clipboard clipboard;
   end else
     MatitaMathView.copy_selection ()

  method cut () =
   source_view#buffer#cut_clipboard clipboard;
   MatitaMathView.empty_clipboard ()

  method delete () =
   ignore (source_view#buffer#delete_selection ())

  method paste () =
    if MatitaMathView.has_clipboard ()
    then source_view#buffer#insert (MatitaMathView.paste_clipboard `Term)
    else source_view#buffer#paste_clipboard clipboard;
    self#clean_dirty_lock

  method pastePattern () =
    source_view#buffer#insert (MatitaMathView.paste_clipboard `Pattern)

  method locked_mark = locked_mark
  method locked_tag = locked_tag
  method error_tag = error_tag

    (* history can't be empty, the invariant above grant that it contains at
     * least the init grafite_status *)
  method status = match history with s::_ -> s | _ -> assert false

  method private _advance ?statement () =
   let s = match statement with Some s -> s | None -> self#getFuture in
   if self#bos then LibraryClean.clean_baseuris [self#buri_of_current_file];
   HLog.debug ("evaluating: " ^ first_line s ^ " ...");
   let time1 = Unix.gettimeofday () in
   let entries, newtext, parsed_len = 
    try
     eval_statement self#include_paths buffer self#status self (`Raw s)
    with End_of_file -> raise Margin
   in
   let time2 = Unix.gettimeofday () in
   HLog.debug ("... done in " ^ string_of_float (time2 -. time1) ^ "s");
   let new_statuses, new_statements =
     let statuses, texts = List.split entries in
     statuses, texts
   in
   history <- new_statuses @ history;
   statements <- new_statements @ statements;
   let start = buffer#get_iter_at_mark (`MARK locked_mark) in
   let new_text = String.concat "" (List.rev new_statements) in
   if statement <> None then
     buffer#insert ~iter:start new_text
   else begin
     let parsed_text = String.sub s 0 parsed_len in
     if new_text <> parsed_text then begin
       let stop = start#copy#forward_chars (Glib.Utf8.length parsed_text) in
       buffer#delete ~start ~stop;
       buffer#insert ~iter:start new_text;
     end;
   end;
   self#moveMark (Glib.Utf8.length new_text);
   buffer#insert ~iter:(buffer#get_iter_at_mark (`MARK locked_mark)) newtext

  method private _retract offset status new_statements new_history =
    NCicLibrary.time_travel status;
    statements <- new_statements;
    history <- new_history;
    self#moveMark (- offset)

  method advance ?statement () =
    try
      self#_advance ?statement ();
      self#notify
    with 
    | Margin -> self#notify
    | Not_found -> assert false
    | Invalid_argument "Array.make" -> HLog.error "The script is too big!\n"
    | exc -> self#notify; raise exc

  method retract () =
    try
      let cmp,new_statements,new_history,status =
       match statements,history with
          stat::statements, _::(status::_ as history) ->
           assert (Glib.Utf8.validate stat);
           Glib.Utf8.length stat, statements, history, status
       | [],[_] -> raise Margin
       | _,_ -> assert false
      in
       self#_retract cmp status new_statements new_history;
       self#notify
    with 
    | Margin -> self#notify
    | Invalid_argument "Array.make" -> HLog.error "The script is too big!\n"
    | exc -> self#notify; raise exc

  method private getFuture =
    let lock = buffer#get_iter_at_mark (`MARK locked_mark) in
    let text = buffer#get_text ~start:lock ~stop:buffer#end_iter () in
    text

  method expandAllVirtuals =
    let lock = buffer#get_iter_at_mark (`MARK locked_mark) in
    let text = buffer#get_text ~start:lock ~stop:buffer#end_iter () in
    buffer#delete ~start:lock ~stop:buffer#end_iter;
    let text = Pcre.replace ~pat:":=" ~templ:"\\def" text in
    let text = Pcre.replace ~pat:"->" ~templ:"\\to" text in
    let text = Pcre.replace ~pat:"=>" ~templ:"\\Rightarrow" text in
    let text = 
      Pcre.substitute_substrings 
        ~subst:(fun str -> 
           let pristine = Pcre.get_substring str 0 in
           let input = 
             if pristine.[0] = ' ' then
               String.sub pristine 1 (String.length pristine -1) 
             else pristine 
           in
           let input = 
             if input.[String.length input-1] = ' ' then
               String.sub input 0 (String.length input -1) 
             else input
           in
           let before, after =  
             if input = "\\forall" || 
                input = "\\lambda" || 
                input = "\\exists" then "","" else " ", " " 
           in
           try 
             before ^ Glib.Utf8.from_unichar 
               (snd (Virtuals.symbol_of_virtual input)) ^ after
           with Virtuals.Not_a_virtual -> pristine) 
        ~pat:" ?\\\\[a-zA-Z]+ ?" text
    in
    buffer#insert ~iter:lock text
      
  (** @param rel_offset relative offset from current position of locked_mark *)
  method private moveMark rel_offset =
    let mark = `MARK locked_mark in
    let old_insert = buffer#get_iter_at_mark `INSERT in
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    let current_mark_pos = buffer#get_iter_at_mark mark in
    let new_mark_pos =
      match rel_offset with
      | 0 -> current_mark_pos
      | n when n > 0 -> current_mark_pos#forward_chars n
      | n (* when n < 0 *) -> current_mark_pos#backward_chars (abs n)
    in
    buffer#move_mark mark ~where:new_mark_pos;
    buffer#apply_tag locked_tag ~start:buffer#start_iter ~stop:new_mark_pos;
    buffer#move_mark `INSERT old_insert;
    let mark_position = buffer#get_iter_at_mark mark in
    if source_view#move_mark_onscreen mark then
     begin
      buffer#move_mark mark mark_position;
      source_view#scroll_to_mark ~use_align:true ~xalign:1.0 ~yalign:0.1 mark;
     end;
    let time0 = Unix.gettimeofday () in
    GtkThread.sync (fun () -> while Glib.Main.pending () do ignore(Glib.Main.iteration false); done) ();
    let time1 = Unix.gettimeofday () in
    HLog.debug ("... refresh done in " ^ string_of_float (time1 -. time0) ^ "s")

  method clean_dirty_lock =
    let lock_mark_iter = buffer#get_iter_at_mark (`MARK locked_mark) in
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#apply_tag locked_tag ~start:buffer#start_iter ~stop:lock_mark_iter

  val mutable observers = []

  method addObserver (o: GrafiteTypes.status -> unit) =
    observers <- o :: observers

  method private notify =
    let status = self#status in
    List.iter (fun o -> o status) observers

  method activate =
    NCicLibrary.replace self#status;
    self#notify

  method loadFromFile f =
    buffer#set_text (HExtlib.input_file f);
    self#reset_buffer;
    buffer#set_modified false

  method assignFileName file =
   match file with
      None ->
       tab_label#set_text default_fname;
       filename_ <- None;
       include_paths_ <- [];
       self#reset_buffer
    | Some file ->
       let f = Librarian.absolutize file in
        tab_label#set_text (Filename.basename f);
        filename_ <- Some f;
        include_paths_ <- MatitaEngine.read_include_paths ~include_paths:[] f;
        self#reset_buffer

  method set_star b =
   tab_label#set_text ((if b then "*" else "")^Filename.basename self#filename);
   tab_label#misc#set_tooltip_text
    ("URI: " ^ self#buri_of_current_file ^ "\nPATH: " ^ self#filename);
    
  method saveToFile () =
    if self#has_name then
      let oc = open_out self#filename in
      output_string oc (buffer#get_text ~start:buffer#start_iter
                        ~stop:buffer#end_iter ());
      close_out oc;
      self#set_star false;
      buffer#set_modified false
    else
      HLog.error "Can't save, no filename selected"
  
  method private _saveToBackupFile () =
    if buffer#modified then
      begin
        let f = self#filename ^ "~" in
        let oc = open_out f in
        output_string oc (buffer#get_text ~start:buffer#start_iter
                            ~stop:buffer#end_iter ());
        close_out oc;
        HLog.debug ("backup " ^ f ^ " saved")
      end
  
  method private reset_buffer = 
    statements <- [];
    history <- [ initial_statuses (Some self#status) self#buri_of_current_file ];
    self#notify;
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#move_mark (`MARK locked_mark) ~where:buffer#start_iter

  method reset () =
    self#reset_buffer;
    source_buffer#begin_not_undoable_action ();
    buffer#delete ~start:buffer#start_iter ~stop:buffer#end_iter;
    source_buffer#end_not_undoable_action ();
    buffer#set_modified false;
  
  method template () =
    let template = HExtlib.input_file BuildTimeConf.script_template in 
    buffer#insert ~iter:(buffer#get_iter `START) template;
    buffer#set_modified false;
    self#set_star false;

  method goto (pos: [`Top | `Bottom | `Cursor]) () =
  try  
    let old_locked_mark =
     `MARK
       (buffer#create_mark ~name:"old_locked_mark"
         ~left_gravity:true (buffer#get_iter_at_mark (`MARK locked_mark))) in
    let getpos _ = buffer#get_iter_at_mark (`MARK locked_mark) in 
    let getoldpos _ = buffer#get_iter_at_mark old_locked_mark in 
    let dispose_old_locked_mark () = buffer#delete_mark old_locked_mark in
    match pos with
    | `Top -> 
        dispose_old_locked_mark (); 
        self#reset_buffer;
        self#notify
    | `Bottom ->
        (try 
          let rec dowhile () =
            self#_advance ();
            let newpos = getpos () in
            if (getoldpos ())#compare newpos < 0 then
              begin
                buffer#move_mark old_locked_mark newpos;
                dowhile ()
              end
          in
          dowhile ();
          dispose_old_locked_mark ();
          self#notify 
        with 
        | Margin -> dispose_old_locked_mark (); self#notify
        | exc -> dispose_old_locked_mark (); self#notify; raise exc)
    | `Cursor ->
        let locked_iter () = buffer#get_iter_at_mark (`NAME "locked") in
        let cursor_iter () = buffer#get_iter_at_mark `INSERT in
        let remember =
         `MARK
           (buffer#create_mark ~name:"initial_insert"
             ~left_gravity:true (cursor_iter ())) in
        let dispose_remember () = buffer#delete_mark remember in
        let remember_iter () =
         buffer#get_iter_at_mark (`NAME "initial_insert") in
        let cmp () = (locked_iter ())#offset - (remember_iter ())#offset in
        let icmp = cmp () in
        let forward_until_cursor () = (* go forward until locked > cursor *)
          let rec aux () =
            self#_advance ();
            if cmp () < 0 && (getoldpos ())#compare (getpos ()) < 0 
            then
             begin
              buffer#move_mark old_locked_mark (getpos ());
              aux ()
             end
          in
          aux ()
        in
        let rec back_until_cursor len = (* go backward until locked < cursor *)
         function
            statements, ((status)::_ as history)
            when len <= 0 ->
             self#_retract (icmp - len) status statements
              history
          | statement::tl1, _::tl2 ->
             back_until_cursor (len - MatitaGtkMisc.utf8_string_length statement) (tl1,tl2)
          | _,_ -> assert false
        in
        (try
          begin
           if icmp < 0 then       (* locked < cursor *)
             (forward_until_cursor (); self#notify)
           else if icmp > 0 then  (* locked > cursor *)
             (back_until_cursor icmp (statements,history); self#notify)
           else                  (* cursor = locked *)
               ()
          end ;
          dispose_remember ();
          dispose_old_locked_mark ();
        with 
        | Margin -> dispose_remember (); dispose_old_locked_mark (); self#notify
        | exc -> dispose_remember (); dispose_old_locked_mark ();
                 self#notify; raise exc)
  with Invalid_argument "Array.make" ->
     HLog.error "The script is too big!\n"
  
  method bos = 
    match history with
    | _::[] -> true
    | _ -> false

  method eos = 
    let rec is_there_only_comments status s = 
      if Pcre.pmatch ~rex:only_dust_RE s then raise Margin;
      let strm =
       GrafiteParser.parsable_statement status
        (Ulexing.from_utf8_string s)in
      match GrafiteParser.parse_statement status strm with
      | GrafiteAst.Comment (loc,_) -> 
          let _,parsed_text_length = MatitaGtkMisc.utf8_parsed_text s loc in
          (* CSC: why +1 in the following lines ???? *)
          let parsed_text_length = parsed_text_length + 1 in
          let remain_len = String.length s - parsed_text_length in
          let next = String.sub s parsed_text_length remain_len in
          is_there_only_comments status next
      | GrafiteAst.Executable _ -> false
    in
    try is_there_only_comments self#status self#getFuture
    with 
    | NCicLibrary.IncludedFileNotCompiled _
    | HExtlib.Localized _
    | CicNotationParser.Parse_error _ -> false
    | Margin | End_of_file -> true
    | Invalid_argument "Array.make" -> false

  (* debug *)
  method dump () =
    HLog.debug "script status:";
    HLog.debug ("history size: " ^ string_of_int (List.length history));
    HLog.debug (sprintf "%d statements:" (List.length statements));
    List.iter HLog.debug statements;
    HLog.debug ("Current file name: " ^ self#filename);

  method has_parent (p : GObj.widget) = parent#coerce#misc#get_oid = p#misc#get_oid
end

let _script = ref []

let script ~parent ~tab_label ()
=
  let s = new script ~parent ~tab_label () in
  _script := s::!_script;
  s

let at_page page =
 let notebook = (MatitaMisc.get_gui ())#main#scriptNotebook in
 let parent = notebook#get_nth_page page in
  try
   List.find (fun s -> s#has_parent parent) !_script
  with
   Not_found -> assert false
;;

let current () =
 at_page ((MatitaMisc.get_gui ())#main#scriptNotebook#current_page)

let destroy page =
 let s = at_page page in
  _script := List.filter ((<>) s) !_script
;;

let iter_scripts f = List.iter f !_script;;

let _ =
 CicMathView.register_matita_script_current (current :> unit -> < advance: ?statement:string -> unit -> unit; status: GrafiteTypes.status >)
;;
