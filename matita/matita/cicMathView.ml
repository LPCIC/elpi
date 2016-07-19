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

open Printf

open GrafiteTypes
open MatitaGtkMisc
open MatitaGuiTypes
open GtkSourceView2

let matita_script_current = ref (fun _ -> (assert false : < advance: ?statement:string -> unit -> unit; status: GrafiteTypes.status >));;
let register_matita_script_current f = matita_script_current := f;;
let get_matita_script_current () = !matita_script_current ();;

type document_element = (int * int * string) list * string (* hyperlinks,text *)

class type cicMathView =
object
  inherit GObj.widget

  method load_root : root:document_element -> unit
  method remove_selections: unit
  method set_selection: document_element option -> unit
  method get_selections: document_element list

    (** @raise Failure "no selection" *)
  method strings_of_selection: (MatitaGuiTypes.paste_kind * string) list

    (** set hyperlink callback. None disable hyperlink handling *)
  method set_href_callback: (string -> unit) option -> unit

    (** load a sequent and render it into parent widget *)
  method nload_sequent:
   #ApplyTransformation.status -> NCic.metasenv -> NCic.substitution -> int -> unit

  method load_nobject: #ApplyTransformation.status -> NCic.obj -> unit
end

(*
let xlink_ns = Gdome.domString "http://www.w3.org/1999/xlink"
let helm_ns = Gdome.domString "http://www.cs.unibo.it/helm"
let href_ds = Gdome.domString "href"
let xref_ds = Gdome.domString "xref"
*)

  (** Gdome.element of a MathML document whose rendering should be blank. Used
  * by cicBrowser to render "about:blank" document *)
let empty_mathml = lazy ([],"")

  (** shown for goals closed by side effects *)
let closed_goal_mathml = lazy ([],"chiuso per side effect...")

(*
let rec has_maction (elt :Gdome.element) = 
  (* fix this comparison *)
  if elt#get_tagName#to_string = "m:maction" ||
   elt#get_tagName#to_string = "b:action" then
    true
  else 
    match elt#get_parentNode with
    | Some node when node#get_nodeType = GdomeNodeTypeT.ELEMENT_NODE -> 
        has_maction (new Gdome.element_of_node node)
    | _ -> false
;;

let hrefs_of_elt elt =
  let localName = href_ds in
  if elt#hasAttributeNS ~namespaceURI:xlink_ns ~localName then
    let text =
      (elt#getAttributeNS ~namespaceURI:xlink_ns ~localName)#to_string in
    Some (HExtlib.split text)
  else
    None

let id_of_node (node: Gdome.element) =
  let xref_attr =
    node#getAttributeNS ~namespaceURI:helm_ns ~localName:xref_ds in
  try
    List.hd (HExtlib.split ~sep:' ' xref_attr#to_string)
  with Failure _ -> assert false

type selected_term =
  | SelTerm of NCic.term * string option (* term, parent hypothesis (if any) *)
  | SelHyp of string * NCic.context (* hypothesis, context *)
*)

let near (x1, y1) (x2, y2) =
  let distance = sqrt (((x2 -. x1) ** 2.) +. ((y2 -. y1) ** 2.)) in
  (distance < 4.)

(*
let name_of_hypothesis = function
  | Some (Cic.Name s, _) -> s
  | _ -> assert false

let domImpl = Gdome.domImplementation ()

(* ids_to_terms should not be passed here, is just for debugging *)
let find_root_id annobj id ids_to_father_ids ids_to_terms ids_to_inner_types =
  assert false (* MATITA 1.0
  let find_parent id ids =
    let rec aux id =
(*       (prerr_endline (sprintf "id %s = %s" id
        (try
          CicPp.ppterm (Hashtbl.find ids_to_terms id)
        with Not_found -> "NONE"))); *)
      if List.mem id ids then Some id
      else
        (match
          (try Hashtbl.find ids_to_father_ids id with Not_found -> None)
        with
        | None -> None
        | Some id' -> aux id')
    in
    aux id
  in
  let return_father id ids =
    match find_parent id ids with
    | None -> assert false
    | Some parent_id -> parent_id
  in
  let mk_ids terms = List.map CicUtil.id_of_annterm terms in
  let inner_types =
   Hashtbl.fold
    (fun _ types acc ->
      match types.Cic2acic.annexpected with
         None -> types.Cic2acic.annsynthesized :: acc
       | Some ty -> ty :: types.Cic2acic.annsynthesized :: acc
    ) ids_to_inner_types [] in
  match annobj with
  | Cic.AConstant (_, _, _, Some bo, ty, _, _)
  | Cic.AVariable (_, _, Some bo, ty, _, _)
  | Cic.ACurrentProof (_, _, _, _, bo, ty, _, _) ->
      return_father id (mk_ids (ty :: bo :: inner_types))
  | Cic.AConstant (_, _, _, None, ty, _, _)
  | Cic.AVariable (_, _, None, ty, _, _) ->
      return_father id (mk_ids (ty::inner_types))
  | Cic.AInductiveDefinition _ ->
      assert false  (* TODO *)
      *)

  (** @return string content of a dom node having a single text child node, e.g.
   * <m:mi xlink:href="...">bool</m:mi> *)
let string_of_dom_node node =
  match node#get_firstChild with
  | None -> ""
  | Some node ->
      (try
        let text = new Gdome.text_of_node node in
        text#get_data#to_string
      with GdomeInit.DOMCastException _ -> "")
*)

class clickableMathView obj =
let text_width = 80 in
object (self)
  inherit GSourceView2.source_view obj

  method strings_of_selection = (assert false : (paste_kind * string) list)

  val mutable href_callback: (string -> unit) option = None
  method set_href_callback f = href_callback <- f

  val mutable href_statusbar_msg:
    (GMisc.statusbar_context * Gtk.statusbar_message) option = None
    (* <statusbar ctxt, statusbar msg> *)

  method private set_cic_info = (function _ -> () : unit (*(Cic.conjecture option * (Cic.id, Cic.term) Hashtbl.t *
         (Cic.id, Cic.hypothesis) Hashtbl.t *
         (Cic.id, Cic.id option) Hashtbl.t * ('a, 'b) Hashtbl.t * 'c option)*) option -> unit)
  (* dal widget di Luca *)
  method load_root ~root:(hyperlinks,text) =
    self#buffer#set_text text;
    let all_tag = self#buffer#create_tag [] in
    self#buffer#apply_tag all_tag ~start:(self#buffer#get_iter `START)
     ~stop:(self#buffer#get_iter `END);
    ignore(all_tag#connect#event
      ~callback:(fun ~origin event pos ->
        match GdkEvent.get_type event with
         | `MOTION_NOTIFY -> 
             Gdk.Window.set_cursor
              (match self#get_window `TEXT with None -> assert false | Some x -> x)
              (Gdk.Cursor.create `ARROW);
             HExtlib.iter_option (fun (ctxt, msg) -> ctxt#remove msg)
              href_statusbar_msg;
             false
         | _ -> false));
     let hyperlink_tag = self#buffer#create_tag [] in
     ignore(hyperlink_tag#connect#event
       ~callback:(fun ~origin event pos ->
         let offset = (new GText.iter pos)#offset in
         let _,_,href =
          try
           List.find
            (fun (start,stop,href) -> start <= offset && offset <= stop
            ) hyperlinks
          with
           Not_found -> assert false
         in
         match GdkEvent.get_type event with
            `BUTTON_PRESS -> 
              (match href_callback with
                  None -> ()
                | Some f -> f href);
              true
          | `MOTION_NOTIFY -> 
              Gdk.Window.set_cursor
               (match self#get_window `TEXT with None -> assert false | Some x -> x)
               (Gdk.Cursor.create `HAND1);
              let ctxt = (MatitaMisc.get_gui ())#main#statusBar#new_context ~name:"href" in
              let msg = ctxt#push href in
              href_statusbar_msg <- Some (ctxt, msg);
              false
          | _ -> false));
     List.iter
      ( fun (start,stop,(href : string)) ->
          self#buffer#apply_tag hyperlink_tag
           ~start:(self#buffer#get_iter_at_char start)
           ~stop:(self#buffer#get_iter_at_char (stop+1));
      ) hyperlinks


  method action_toggle = (fun _ -> assert false : document_element -> bool)
  method remove_selections = (() : unit)
  method set_selection = (fun _ -> () : document_element option -> unit)
  method get_selections = (assert false : document_element list)

  initializer
    self#source_buffer#set_language (Some MatitaGtkMisc.matita_lang);
    self#source_buffer#set_highlight_syntax true;
    self#set_editable false;
    MatitaMisc.observe_font_size
     (fun size ->
       self#misc#modify_font_by_name
        (sprintf "%s %d" BuildTimeConf.script_font size))

(* MATITA 1.0
  inherit GMathViewAux.multi_selection_math_view obj

  val mutable href_callback: (string -> unit) option = None
  method set_href_callback f = href_callback <- f

  val mutable _cic_info = None
  method private set_cic_info info = _cic_info <- info
  method private cic_info = _cic_info

  val normal_cursor = Gdk.Cursor.create `LEFT_PTR
  val href_cursor = Gdk.Cursor.create `HAND2
  val maction_cursor = Gdk.Cursor.create `QUESTION_ARROW

  initializer
    ignore (self#connect#selection_changed self#choose_selection_cb);
    ignore (self#event#connect#button_press self#button_press_cb);
    ignore (self#event#connect#button_release self#button_release_cb);
    ignore (self#event#connect#selection_clear self#selection_clear_cb);
    ignore (self#connect#element_over self#element_over_cb);
    ignore (self#coerce#misc#connect#selection_get self#selection_get_cb)

  val mutable button_press_x = -1.
  val mutable button_press_y = -1.
  val mutable selection_changed = false
  val mutable href_statusbar_msg:
    (GMisc.statusbar_context * Gtk.statusbar_message) option = None
    (* <statusbar ctxt, statusbar msg> *)

  method private selection_get_cb ctxt ~info ~time =
    let text =
      match ctxt#target with
      | "PATTERN" -> self#text_of_selection `Pattern
      | "TERM" | _ -> self#text_of_selection `Term
    in
    match text with
    | None -> ()
    | Some s -> ctxt#return s

  method private text_of_selection fmt =
    match self#get_selections with
    | [] -> None
    | node :: _ -> Some (self#string_of_node ~paste_kind:fmt node)

  method private selection_clear_cb sel_event =
    self#remove_selections;
    (GData.clipboard Gdk.Atom.clipboard)#clear ();
    false

  method private button_press_cb gdk_button =
    let button = GdkEvent.Button.button gdk_button in
    if  button = MatitaMisc.left_button then begin
      button_press_x <- GdkEvent.Button.x gdk_button;
      button_press_y <- GdkEvent.Button.y gdk_button;
      selection_changed <- false
    end else if button = MatitaMisc.right_button then
      self#popup_contextual_menu 
        (self#get_element_at 
          (int_of_float (GdkEvent.Button.x gdk_button)) 
          (int_of_float (GdkEvent.Button.y gdk_button)))  
        (GdkEvent.Button.time gdk_button);
    false

  method private element_over_cb (elt_opt, _, _, _) =
    let win () = self#misc#window in
    let leave_href () =
      Gdk.Window.set_cursor (win ()) normal_cursor;
      HExtlib.iter_option (fun (ctxt, msg) -> ctxt#remove msg)
        href_statusbar_msg
    in
    match elt_opt with
    | Some elt ->
        if has_maction elt then
          Gdk.Window.set_cursor (win ()) maction_cursor
        else
        (match hrefs_of_elt elt with
        | Some ((_ :: _) as hrefs) ->
            Gdk.Window.set_cursor (win ()) href_cursor;
            let msg_text = (* now create statusbar msg and store it *)
              match hrefs with
              | [ href ] -> sprintf "Hyperlink to %s" href
              | _ -> sprintf "Hyperlinks to: %s" (String.concat ", " hrefs) in
            let ctxt = (get_gui ())#main#statusBar#new_context ~name:"href" in
            let msg = ctxt#push msg_text in
            href_statusbar_msg <- Some (ctxt, msg)
        | _ -> leave_href ())
    | None -> leave_href ()

  method private tactic_text_pattern_of_node node =
   let id = id_of_node node in
   let cic_info, unsh_sequent = self#get_cic_info id in
   match self#get_term_by_id cic_info id with
   | SelTerm (t, father_hyp) ->
       let sequent = self#sequent_of_id ~paste_kind:`Pattern id in
       let text = self#string_of_cic_sequent ~output_type:`Pattern sequent in
       (match father_hyp with
       | None -> None, [], Some text
       | Some hyp_name -> None, [ hyp_name, text ], None)
   | SelHyp (hyp_name, _ctxt) -> None, [ hyp_name, "%" ], None

  method private tactic_text_of_node node =
   let id = id_of_node node in
   let cic_info, unsh_sequent = self#get_cic_info id in
   match self#get_term_by_id cic_info id with
   | SelTerm (t, father_hyp) ->
       let sequent = self#sequent_of_id ~paste_kind:`Term id in
       let text = self#string_of_cic_sequent ~output_type:`Term sequent in
       text
   | SelHyp (hyp_name, _ctxt) -> hyp_name

    (** @return a pattern structure which contains pretty printed terms *)
  method private tactic_text_pattern_of_selection =
    match self#get_selections with
    | [] -> assert false (* this method is invoked only if there's a sel. *)
    | node :: _ -> self#tactic_text_pattern_of_node node

  method private popup_contextual_menu element time =
    let menu = GMenu.menu () in
    let add_menu_item ?(menu = menu) ?stock ?label () =
      GMenu.image_menu_item ?stock ?label ~packing:menu#append () in
    let check = add_menu_item ~label:"Check" () in
    let reductions_menu_item = GMenu.menu_item ~label:"βδιζ-reduce" () in
    let tactics_menu_item = GMenu.menu_item ~label:"Apply tactic" () in
    let hyperlinks_menu_item = GMenu.menu_item ~label:"Hyperlinks" () in
    menu#append reductions_menu_item;
    menu#append tactics_menu_item;
    menu#append hyperlinks_menu_item;
    let reductions = GMenu.menu () in
    let tactics = GMenu.menu () in
    let hyperlinks = GMenu.menu () in
    reductions_menu_item#set_submenu reductions;
    tactics_menu_item#set_submenu tactics;
    hyperlinks_menu_item#set_submenu hyperlinks;
    let normalize = add_menu_item ~menu:reductions ~label:"Normalize" () in
    let simplify = add_menu_item ~menu:reductions ~label:"Simplify" () in
    let whd = add_menu_item ~menu:reductions ~label:"Weak head" () in
    (match element with 
    | None -> hyperlinks_menu_item#misc#set_sensitive false
    | Some elt -> 
        match hrefs_of_elt elt, href_callback with
        | Some l, Some f ->
            List.iter 
              (fun h ->
                let item = add_menu_item ~menu:hyperlinks ~label:h () in
                connect_menu_item item (fun () -> f h)) l
        | _ -> hyperlinks_menu_item#misc#set_sensitive false);
    menu#append (GMenu.separator_item ());
    let copy = add_menu_item ~stock:`COPY () in
    let gui = get_gui () in
    List.iter (fun item -> item#misc#set_sensitive gui#canCopy)
      [ copy; check; normalize; simplify; whd ];
    let reduction_action kind () =
      let pat = self#tactic_text_pattern_of_selection in
      let statement =
        let loc = HExtlib.dummy_floc in
        "\n" ^
        GrafiteAstPp.pp_executable ~term_pp:(fun s -> s)
          ~lazy_term_pp:(fun _ -> assert false) ~obj_pp:(fun _ -> assert false)
          ~map_unicode_to_tex:(Helm_registry.get_bool
            "matita.paste_unicode_as_tex")
          (GrafiteAst.Tactic (loc,
            Some (GrafiteAst.Reduce (loc, kind, pat)),
            GrafiteAst.Semicolon loc)) in
      (get_matita_script_current ())#advance ~statement () in
    connect_menu_item copy gui#copy;
    connect_menu_item normalize (reduction_action `Normalize);
    connect_menu_item simplify (reduction_action `Simpl);
    connect_menu_item whd (reduction_action `Whd);
    menu#popup ~button:MatitaMisc.right_button ~time

  method private button_release_cb gdk_button =
    if GdkEvent.Button.button gdk_button = MatitaMisc.left_button then begin
      let button_release_x = GdkEvent.Button.x gdk_button in
      let button_release_y = GdkEvent.Button.y gdk_button in
      if selection_changed then
        ()
      else  (* selection _not_ changed *)
        if near (button_press_x, button_press_y)
          (button_release_x, button_release_y)
        then
          let x = int_of_float button_press_x in
          let y = int_of_float button_press_y in
          (match self#get_element_at x y with
          | None -> ()
          | Some elt ->
              if has_maction elt then ignore(self#action_toggle elt) else
              (match hrefs_of_elt elt with
              | Some hrefs -> self#invoke_href_callback hrefs gdk_button
              | None -> ()))
    end;
    false

  method private invoke_href_callback hrefs gdk_button =
    let button = GdkEvent.Button.button gdk_button in
    if button = MatitaMisc.left_button then
      let time = GdkEvent.Button.time gdk_button in
      match href_callback with
      | None -> ()
      | Some f ->
          (match hrefs with
          | [ uri ] ->  f uri
          | uris ->
              let menu = GMenu.menu () in
              List.iter
                (fun uri ->
                  let menu_item =
                    GMenu.menu_item ~label:uri ~packing:menu#append () in
                  connect_menu_item menu_item 
                  (fun () -> try f uri with Not_found -> assert false))
                uris;
              menu#popup ~button ~time)

  method private choose_selection_cb gdome_elt =
    let set_selection elt =
      let misc = self#coerce#misc in
      self#set_selection (Some elt);
      misc#add_selection_target ~target:"STRING" Gdk.Atom.primary;
      ignore (misc#grab_selection Gdk.Atom.primary);
    in
    let rec aux elt =
      if (elt#getAttributeNS ~namespaceURI:helm_ns
            ~localName:xref_ds)#to_string <> ""
      then
        set_selection elt
      else
        try
          (match elt#get_parentNode with
          | None -> assert false
          | Some p -> aux (new Gdome.element_of_node p))
        with GdomeInit.DOMCastException _ -> ()
    in
    (match gdome_elt with
    | Some elt when (elt#getAttributeNS ~namespaceURI:xlink_ns
        ~localName:href_ds)#to_string <> "" ->
          set_selection elt
    | Some elt -> aux elt
    | None -> self#set_selection None);
    selection_changed <- true

    (** find a term by id from stored CIC infos @return either `Hyp if the id
     * correspond to an hypothesis or `Term (cic, hyp) if the id correspond to a
     * term. In the latter case hyp is either None (if the term is a subterm of
     * the sequent conclusion) or Some hyp_name if the term belongs to an
     * hypothesis *)
  method private get_term_by_id cic_info id =
    let unsh_item, ids_to_terms, ids_to_hypotheses, ids_to_father_ids, _, _ =
      cic_info in
    let rec find_father_hyp id =
      if Hashtbl.mem ids_to_hypotheses id
      then Some (name_of_hypothesis (Hashtbl.find ids_to_hypotheses id))
      else
        let father_id =
          try Hashtbl.find ids_to_father_ids id
          with Not_found -> assert false in
        match father_id with
        | Some id -> find_father_hyp id
        | None -> None
    in
    try
      let term = Hashtbl.find ids_to_terms id in
      let father_hyp = find_father_hyp id in
      SelTerm (term, father_hyp)
    with Not_found ->
      try
        let hyp = Hashtbl.find ids_to_hypotheses id in
        let _, context, _ =
          match unsh_item with Some seq -> seq | None -> assert false in
        let context' = MatitaMisc.list_tl_at hyp context in
        SelHyp (name_of_hypothesis hyp, context')
      with Not_found -> assert false
    
  method private find_obj_conclusion id =
    match self#cic_info with
    | None
    | Some (_, _, _, _, _, None) -> assert false
    | Some (_, ids_to_terms, _, ids_to_father_ids, ids_to_inner_types, Some annobj) ->
        let id =
         find_root_id annobj id ids_to_father_ids ids_to_terms ids_to_inner_types
        in
         (try Hashtbl.find ids_to_terms id with Not_found -> assert false)

  method private string_of_node ~(paste_kind:paste_kind) node =
    if node#hasAttributeNS ~namespaceURI:helm_ns ~localName:xref_ds
    then
      match paste_kind with
      | `Pattern ->
          let tactic_text_pattern =  self#tactic_text_pattern_of_node node in
          GrafiteAstPp.pp_tactic_pattern
            ~term_pp:(fun s -> s) ~lazy_term_pp:(fun _ -> assert false)
            ~map_unicode_to_tex:(Helm_registry.get_bool
              "matita.paste_unicode_as_tex")
            tactic_text_pattern
      | `Term -> self#tactic_text_of_node node
    else string_of_dom_node node

  method private string_of_cic_sequent ~output_type cic_sequent =
    let script = get_matita_script_current () in
    let metasenv =
      if script#onGoingProof () then script#proofMetasenv else [] in
    let map_unicode_to_tex =
      Helm_registry.get_bool "matita.paste_unicode_as_tex" in
    ApplyTransformation.txt_of_cic_sequent_conclusion ~map_unicode_to_tex
     ~output_type text_width metasenv cic_sequent

  method private pattern_of term father_hyp unsh_sequent =
    let _, unsh_context, conclusion = unsh_sequent in
    let where =
     match father_hyp with
        None -> conclusion
      | Some name ->
         let rec aux =
          function
             [] -> assert false
           | Some (Cic.Name name', Cic.Decl ty)::_ when name' = name -> ty
           | Some (Cic.Name name', Cic.Def (bo,_))::_ when name' = name-> bo
           | _::tl -> aux tl
         in
          aux unsh_context
    in
     ProofEngineHelpers.pattern_of ~term:where [term]

  method private get_cic_info id =
    match self#cic_info with
    | Some ((Some unsh_sequent, _, _, _, _, _) as info) -> info, unsh_sequent
    | Some ((None, _, _, _, _, _) as info) ->
        let t = self#find_obj_conclusion id in
        info, (~-1, [], t) (* dummy sequent for obj *)
    | None -> assert false

  method private sequent_of_id ~(paste_kind:paste_kind) id =
    let cic_info, unsh_sequent = self#get_cic_info id in
    let cic_sequent =
      match self#get_term_by_id cic_info id with
      | SelTerm (t, father_hyp) ->
(*
IDIOTA: PRIMA SI FA LA LOCATE, POI LA PATTERN_OF. MEGLIO UN'UNICA pattern_of CHE PRENDA IN INPUT UN TERMINE E UN SEQUENTE. PER IL MOMENTO RISOLVO USANDO LA father_hyp PER RITROVARE L'IPOTESI PERDUTA
*)
          let occurrences =
            ProofEngineHelpers.locate_in_conjecture t unsh_sequent in
          (match occurrences with
          | [ context, _t ] ->
              (match paste_kind with
              | `Term -> ~-1, context, t
              | `Pattern -> ~-1, [], self#pattern_of t father_hyp unsh_sequent)
          | _ ->
              HLog.error (sprintf "found %d occurrences while 1 was expected"
                (List.length occurrences));
              assert false) (* since it uses physical equality *)
      | SelHyp (_name, context) -> ~-1, context, Cic.Rel 1 in
    cic_sequent

  method private string_of_selection ~(paste_kind:paste_kind) =
    match self#get_selections with
    | [] -> None
    | node :: _ -> Some (self#string_of_node ~paste_kind node)

    (** @return an associative list format -> string with all possible selection
     * formats. Rationale: in order to convert the selection to TERM or PATTERN
     * format we need the sequent, the metasenv, ... keeping all of them in a
     * closure would be more expensive than keeping their already converted
     * forms *)
  method strings_of_selection =
    try
      let misc = self#coerce#misc in
      List.iter
        (fun target -> misc#add_selection_target ~target Gdk.Atom.clipboard)
        [ "TERM"; "PATTERN"; "STRING" ];
      ignore (misc#grab_selection Gdk.Atom.clipboard);
      List.map
        (fun paste_kind ->
          paste_kind, HExtlib.unopt (self#string_of_selection ~paste_kind))
        [ `Term; `Pattern ]
    with Failure _ -> failwith "no selection"
*)
end

class _cicMathView obj =
object (self)
  inherit clickableMathView obj

  val mutable current_mathml = None

  method nload_sequent:
   'status. #ApplyTransformation.status as 'status -> NCic.metasenv ->
     NCic.substitution -> int -> unit
   = fun status metasenv subst metano ->
    let sequent = List.assoc metano metasenv in
    let txt =
     ApplyTransformation.ntxt_of_cic_sequent
      ~map_unicode_to_tex:false 80 status ~metasenv ~subst (metano,sequent)
    in
    (* MATITA 1.0 if BuildTimeConf.debug then begin
      let name =
       "/tmp/sequent_viewer_" ^ string_of_int (Unix.getuid ()) ^ ".xml" in
      HLog.debug ("load_sequent: dumping MathML to ./" ^ name);
      ignore (domImpl#saveDocumentToFile ~name ~doc:mathml ())
    end;*)
    self#load_root ~root:txt

  method load_nobject :
   'status. #ApplyTransformation.status as 'status -> NCic.obj -> unit
   = fun status obj ->
    let txt = ApplyTransformation.ntxt_of_cic_object ~map_unicode_to_tex:false
    80 status obj in
(*
    self#set_cic_info
      (Some (None, ids_to_terms, ids_to_hypotheses, ids_to_father_ids, ids_to_inner_types, Some annobj));
    (match current_mathml with
    | Some current_mathml when use_diff ->
        self#freeze;
        XmlDiff.update_dom ~from:current_mathml mathml;
        self#thaw
    |  _ ->
*)
        (* MATITA 1.0 if BuildTimeConf.debug then begin
          let name =
           "/tmp/cic_browser_" ^ string_of_int (Unix.getuid ()) ^ ".xml" in
          HLog.debug ("cic_browser: dumping MathML to ./" ^ name);
          ignore (domImpl#saveDocumentToFile ~name ~doc:mathml ())
        end;*)
        self#load_root ~root:txt;
        (*current_mathml <- Some mathml*)(*)*);
end

 (** constructors *)

let cicMathView (*?auto_indent ?highlight_current_line ?indent_on_tab ?indent_width ?insert_spaces_instead_of_tabs ?right_margin_position ?show_line_marks ?show_line_numbers ?show_right_margin ?smart_home_end ?tab_width ?editable ?cursor_visible ?justification ?wrap_mode ?accepts_tab ?border_width*) ?width ?height ?packing ?show () =
 ((*SourceView.make_params [] ~cont:(
    GtkText.View.make_params ~cont:( *)
      GContainer.pack_container ~create:(fun pl ->
        let obj = SourceView.new_ () in
        Gobject.set_params (Gobject.try_cast obj "GtkSourceView") pl;
        new _cicMathView obj)(*)) ?auto_indent ?highlight_current_line ?indent_on_tab ?indent_width ?insert_spaces_instead_of_tabs ?right_margin_position ?show_line_marks ?show_line_numbers ?show_right_margin ?smart_home_end ?tab_width ?editable ?cursor_visible ?justification ?wrap_mode ?accepts_tab ?border_width*) [] ?width ?height ?packing ?show () :> cicMathView)

let screenshot status sequents metasenv subst (filename as ofn) =
 () (*MATITA 1.0
  let w = GWindow.window ~title:"screenshot" () in
  let width = 500 in
  let height = 2000 in
  let m = GMathView.math_view 
     ~font_size:(MatitaMisc.get_current_font_size ()) ~width ~height
     ~packing:w#add
     ~show:true ()
  in
  w#show ();
  let filenames = 
   HExtlib.list_mapi
    (fun (mno,_ as sequent) i ->
       let mathml = 
         ApplyTransformation.nmml_of_cic_sequent 
           status metasenv subst sequent
       in
       m#load_root ~root:mathml#get_documentElement;
       let pixmap = m#get_buffer in
       let pixbuf = GdkPixbuf.create ~width ~height () in
       GdkPixbuf.get_from_drawable ~dest:pixbuf pixmap;
       let filename = 
         filename ^ "-raw" ^ string_of_int i ^ ".png" 
       in
       GdkPixbuf.save ~filename ~typ:"png" pixbuf;
       filename,mno)
    sequents
  in
  let items = 
    List.map (fun (x,mno) -> 
      ignore(Sys.command
        (Printf.sprintf
         ("convert "^^
         " '(' -gravity west -bordercolor grey -border 1 label:%d ')' "^^
         " '(' -trim -bordercolor white -border 5 "^^
           " -bordercolor grey -border 1 %s ')' -append %s ")
         mno
         (Filename.quote x)
         (Filename.quote (x ^ ".label.png"))));
        x ^ ".label.png")
    filenames
  in
  let rec div2 = function 
    | [] -> []
    | [x] -> [[x]]
    | x::y::tl -> [x;y] :: div2 tl
  in
  let items = div2 items in
  ignore(Sys.command (Printf.sprintf 
    "convert %s -append  %s" 
     (String.concat ""
       (List.map (fun items ->
         Printf.sprintf " '(' %s +append ')' "
           (String.concat 
              (" '(' -gravity center -size 10x10 xc: ')' ") items)) items))
    (Filename.quote (ofn ^ ".png")))); 
  List.iter (fun x,_ -> Sys.remove x) filenames;
  List.iter Sys.remove (List.flatten items);
  w#destroy ()*)
