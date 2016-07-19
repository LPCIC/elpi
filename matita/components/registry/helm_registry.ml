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

(* $Id: helm_registry.ml 13213 2016-06-19 12:59:00Z fguidi $ *)

open Printf

let debug = false
let debug_print s =
  if debug then prerr_endline ("Helm_registry debugging: " ^ (Lazy.force s))

  (** <helpers> *)

let list_uniq l =
  let rec aux last_element = function
    | [] -> []
    | hd :: tl ->
        (match last_element with
        | Some elt when elt = hd -> aux last_element tl
        | _ -> hd :: aux (Some hd) tl)
  in
  aux None l

let starts_with prefix =
(*
  let rex = Str.regexp (Str.quote prefix) in
  fun s -> Str.string_match rex s 0
*)
  let prefix_len = String.length prefix in
  fun s ->
    try
      String.sub s 0 prefix_len = prefix
    with Invalid_argument _ -> false

let hashtbl_keys tbl = Hashtbl.fold (fun k _ acc -> k :: acc) tbl []
let hashtbl_pairs tbl = Hashtbl.fold (fun k v acc -> (k,v) :: acc) tbl []

  (** </helpers> *)

exception Malformed_key of string
exception Key_not_found of string
exception Cyclic_definition of string
exception Type_error of string (* expected type, value, msg *)
exception Parse_error of string * int * int * string  (* file, line, col, msg *)

  (* root XML tag: used by save_to, ignored by load_from *)
let root_tag = "helm_registry"

let magic_size = 127

let backup_registry registry = Hashtbl.copy registry
let restore_registry backup registry =
  Hashtbl.clear registry;
  Hashtbl.iter (fun key value -> Hashtbl.add registry key value) backup

  (* as \\w but:
   * - no sequences of '_' longer than 1 are permitted
   *)
let valid_step_rex_raw = "[a-zA-Z0-9]+\\(_[a-z0A-Z-9]+\\)*"
let valid_key_rex_raw =
  sprintf "%s\\(\\.%s\\)*" valid_step_rex_raw valid_step_rex_raw
let valid_key_rex = Str.regexp ("^" ^ valid_key_rex_raw ^ "$")
let interpolated_key_rex = Str.regexp ("\\$(" ^ valid_key_rex_raw ^ ")")
let dot_rex = Str.regexp "\\."
let spaces_rex = Str.regexp "[ \t\n\r]+"
let heading_spaces_rex = Str.regexp "^[ \t\n\r]+"
let margin_blanks_rex =
  Str.regexp "^\\([ \t\n\r]*\\)\\([^ \t\n\r]*\\)\\([ \t\n\r]*\\)$"

let strip_blanks s = Str.global_replace margin_blanks_rex "\\2" s

let split s =
  (* trailing blanks are removed per default by split *)
  Str.split spaces_rex (Str.global_replace heading_spaces_rex "" s)
let merge l = String.concat " " l

let handle_type_error f x =
  try f x with exn -> raise (Type_error (Printexc.to_string exn))

  (** marshallers/unmarshallers *)
let string x = x
let int = handle_type_error int_of_string
let float = handle_type_error float_of_string
let bool = handle_type_error bool_of_string
let of_string x = x
let of_int = handle_type_error string_of_int
let of_float = handle_type_error string_of_float
let of_bool = handle_type_error string_of_bool

(* FG *)
let pair fst_unmarshaller snd_unmarshaller v =
  match Str.split spaces_rex v with
  | [fst; snd] -> fst_unmarshaller fst, snd_unmarshaller snd
  | _ -> raise (Type_error "not a pair")

(* FG *)
let triple fst_unmarshaller snd_unmarshaller trd_unmarshaller v =
  match Str.split spaces_rex v with
  | [fst; snd; trd] -> fst_unmarshaller fst, snd_unmarshaller snd, trd_unmarshaller trd
  | _ -> raise (Type_error "not a triple")

(* FG *)
let quad fst_unmarshaller snd_unmarshaller trd_unmarshaller fth_unmarshaller v =
  match Str.split spaces_rex v with
  | [fst; snd; trd; fth] -> fst_unmarshaller fst, snd_unmarshaller snd, trd_unmarshaller trd, fth_unmarshaller fth
  | _ -> raise (Type_error "not a quad")

  (* escapes for xml configuration file *)
let (escape, unescape) =
  let (in_enc, out_enc) = (`Enc_utf8, `Enc_utf8) in
  (Netencoding.Html.encode ~in_enc ~out_enc (),
   Netencoding.Html.decode ~in_enc ~out_enc ~entity_base:`Xml ())

let key_is_valid key =
  if not (Str.string_match valid_key_rex key 0) then
    raise (Malformed_key key)

let set' ?(replace=false) registry ~key ~value =
  debug_print (lazy(sprintf "Setting (replace: %b) %s = %s" replace key value));
  key_is_valid key;
  let add_fun = if replace then Hashtbl.replace else Hashtbl.add in
  add_fun registry key value

let unset registry = Hashtbl.remove registry

let env_var_of_key s = String.uppercase (Str.global_replace dot_rex "_" s)

let singleton = function
  | [] ->
      raise (Type_error ("empty list value found where singleton was expected"))
  | hd :: _ -> hd

let get registry key =
  let rec aux stack key =
    key_is_valid key;
    if List.mem key stack then begin
      let msg = (String.concat " -> " (List.rev stack)) ^ " -> " ^ key in
      raise (Cyclic_definition msg)
    end;
      (* internal value *)
    let registry_values = List.rev (Hashtbl.find_all registry key) in
    let env_value = (* environment value *)
      try
        Some (Sys.getenv (env_var_of_key key))
      with Not_found -> None
    in
    let values = (* resulting value *)
      match registry_values, env_value with
      | _, Some env -> [env]
      | [], None ->
          (try
            [ Sys.getenv key ]
          with Not_found -> raise (Key_not_found key))
      | values, None -> values
    in
    List.map (interpolate (key :: stack)) values
  and interpolate stack value =
    Str.global_substitute interpolated_key_rex
      (fun s ->
        let matched = Str.matched_string s in
          (* "$(var)" -> "var" *)
        let key = String.sub matched 2 (String.length matched - 3) in
        singleton (aux stack key))
      value
  in
  List.map strip_blanks (aux [] key)

let has registry key = Hashtbl.mem registry key

let get_typed registry unmarshaller key =
  let value = singleton (get registry key) in
  unmarshaller value

let set_typed registry marshaller ~key ~value =
  set' ~replace:true registry ~key ~value:(marshaller value)

let get_opt registry unmarshaller key =
  try
    Some (unmarshaller (singleton (get registry key)))
  with Key_not_found _ -> None

let get_opt_default registry unmarshaller ~default key =
  match get_opt registry unmarshaller key with
  | None -> default
  | Some v -> v

let set_opt registry marshaller ~key ~value =
  match value with
  | None -> unset registry key
  | Some value -> set' ~replace:true registry ~key ~value:(marshaller value)

let get_list registry unmarshaller key =
  try
    let tmp = get registry key in
    let rc = List.map unmarshaller tmp in
    rc
  with Key_not_found _ -> []

(* FG *)
let get_pair registry fst_unmarshaller snd_unmarshaller =
  get_typed registry (pair fst_unmarshaller snd_unmarshaller) 

(* FG *)
let get_triple registry fst_unmarshaller snd_unmarshaller trd_unmarshaller =
  get_typed registry (triple fst_unmarshaller snd_unmarshaller trd_unmarshaller) 

(* FG *)
let get_quad registry fst_unmarshaller snd_unmarshaller trd_unmarshaller fth_unmarshaller =
  get_typed registry (quad fst_unmarshaller snd_unmarshaller trd_unmarshaller fth_unmarshaller) 

let set_list registry marshaller ~key ~value =
  (* since ocaml hash table are crazy... *)
  while Hashtbl.mem registry key do
    Hashtbl.remove registry key
  done;
  List.iter (fun v -> set' registry ~key ~value:(marshaller v)) value

type xml_tree =
  | Cdata of string
  | Element of string * (string * string) list * xml_tree list

let dot_RE = Str.regexp "\\."

let xml_tree_of_registry registry =
  let has_child name elements =
    List.exists
      (function
        | Element (_, ["name", name'], _) when name = name' -> true
        | _ -> false)
      elements
  in
  let rec get_child name = function
    | [] -> assert false
    | (Element (_, ["name", name'], _) as child) :: tl when name = name' ->
        child, tl
    | hd :: tl ->
        let child, rest = get_child name tl in
        child, hd :: rest
  in
  let rec add_key path value tree =
    match path, tree with
    | [key], Element (name, attrs, children) ->
        Element (name, attrs,
          Element ("key", ["name", key],
            [Cdata (strip_blanks value)]) :: children)
    | dir :: path, Element (name, attrs, children) ->
        if has_child dir children then
          let child, rest = get_child dir children in
          Element (name, attrs, add_key path value child :: rest)
        else
          Element (name, attrs,
            ((add_key path value (Element ("section", ["name", dir], [])))
              :: children))
    | _ -> assert false
  in
  Hashtbl.fold
    (fun k v tree -> add_key ((Str.split dot_RE k)) v tree)
    registry
    (Element (root_tag, [], []))

let rec stream_of_xml_tree = function
  | Cdata s -> Xml.xml_cdata s
  | Element (name, attrs, children) ->
      Xml.xml_nempty name
        (List.map (fun (n, v) -> (None, n, v)) attrs)
        (stream_of_xml_trees children)
and stream_of_xml_trees = function
  | [] -> [< >]
  | hd :: tl -> [< stream_of_xml_tree hd; stream_of_xml_trees tl >]

let save_to registry fname =
  let token_stream = stream_of_xml_tree (xml_tree_of_registry registry) in
  let oc = open_out fname in
  Xml.pp_to_outchan token_stream oc;
  close_out oc

let rec load_from_absolute ?path registry fname =
  let _path = ref (match path with None -> [] | Some p -> p)in
    (* <section> elements entered so far *)
  let in_key = ref false in (* have we entered a <key> element? *)
  let cdata = ref "" in     (* collected cdata (inside <key> *)
  let push_path name = _path := name :: !_path in
  let pop_path () = _path := List.tl !_path in
  let start_element tag attrs =
    match tag, attrs with
    | "section", ["name", name] -> push_path name
    | "key", ["name", name] -> in_key := true; push_path name
    | "helm_registry", _ -> ()
    | "include", ["href", fname] ->
        debug_print (lazy ("including file " ^ fname));
        load_from_absolute ~path:!_path registry fname
    | tag, _ ->
        raise (Parse_error (fname, ~-1, ~-1,
          (sprintf "unexpected element <%s> or wrong attribute set" tag)))
  in
  let end_element tag =
    match tag with
    | "section" -> pop_path ()
    | "key" ->
        let key = String.concat "." (List.rev !_path) in
        set' registry ~key ~value:!cdata;
        cdata := "";
        in_key := false;
        pop_path ()
    | "include" | "helm_registry" -> ()
    | _ -> assert false
  in
  let character_data text =
    if !in_key then cdata := !cdata ^ text
  in
  let callbacks = {
    XmlPushParser.default_callbacks with
      XmlPushParser.start_element = Some start_element;
      XmlPushParser.end_element = Some end_element;
      XmlPushParser.character_data = Some character_data;
  } in
  let xml_parser = XmlPushParser.create_parser callbacks in
  let backup = backup_registry registry in
(*   if path = None then Hashtbl.clear registry; *)
  try
    XmlPushParser.parse xml_parser (`File fname)
  with exn ->
    restore_registry backup registry;
    raise exn

let load_from registry ?path fname =
  if Filename.is_relative fname then begin
    let no_file_found = ref true in
    let path =
      match path with
      | Some path -> path (* path given as argument *)
      | None -> [ Sys.getcwd () ] (* no path given, try with cwd *)
    in
    List.iter
      (fun dir ->
        let conffile = dir ^ "/" ^ fname in
        if Sys.file_exists conffile then begin
          no_file_found := false;
          load_from_absolute registry conffile
        end)
       path;
    if !no_file_found then
      failwith (sprintf
        "Helm_registry.init: no configuration file named %s in [ %s ]"
        fname (String.concat "; " path))
  end else
    load_from_absolute registry fname

let fold registry ?prefix ?(interpolate = true) f init =
  let value_of k v =
    if interpolate then singleton (get registry k) else strip_blanks v
  in
  match prefix with
  | None -> Hashtbl.fold (fun k v acc -> f acc k (value_of k v)) registry init
  | Some s ->
      let key_matches = starts_with (s ^ ".") in
      let rec fold_filter acc = function
        | [] -> acc
        | (k,v) :: tl when key_matches k ->
            fold_filter (f acc k (value_of k v)) tl
        | _ :: tl -> fold_filter acc tl
      in
      fold_filter init (hashtbl_pairs registry)

let iter registry ?prefix ?interpolate f =
  fold registry ?prefix ?interpolate (fun _ k v -> f k v) ()
let to_list registry ?prefix ?interpolate () =
  fold registry ?prefix ?interpolate (fun acc k v -> (k, v) :: acc) []

let ls registry prefix =
  let prefix = prefix ^ "." in
  let prefix_len = String.length prefix in
  let key_matches = starts_with prefix in
  let matching_keys = (* collect matching keys' _postfixes_ *)
    fold registry
      (fun acc key _ ->
        if key_matches key then
          String.sub key prefix_len (String.length key - prefix_len) :: acc
        else
          acc)
      []
  in
  let (sections, keys) =
    List.fold_left
      (fun (sections, keys) postfix ->
        match Str.split dot_rex postfix with
        | [key] -> (sections, key :: keys)
        | hd_key :: _ ->  (* length > 1 => nested section found *)
            (hd_key :: sections, keys)
        | _ -> assert false)
      ([], []) matching_keys
  in
  (list_uniq (List.sort Pervasives.compare sections), keys)

(** {2 API implementation}
 * functional methods above are wrapped so that they work on a default
 * (imperative) registry*)

let default_registry = Hashtbl.create magic_size

let get key = singleton (get default_registry key)
let set = set' ~replace:true default_registry
let has = has default_registry
let fold ?prefix ?interpolate f init =
  fold default_registry ?prefix ?interpolate f init
let iter = iter default_registry
let to_list = to_list default_registry
let ls = ls default_registry
let get_typed unmarshaller = get_typed default_registry unmarshaller
let get_opt unmarshaller = get_opt default_registry unmarshaller
let get_opt_default unmarshaller = get_opt_default default_registry unmarshaller
let get_list unmarshaller = get_list default_registry unmarshaller
let get_pair unmarshaller = get_pair default_registry unmarshaller
let get_triple unmarshaller = get_triple default_registry unmarshaller
let get_quad unmarshaller = get_quad default_registry unmarshaller
let set_typed marshaller = set_typed default_registry marshaller
let set_opt unmarshaller = set_opt default_registry unmarshaller
let set_list marshaller = set_list default_registry marshaller
let unset = unset default_registry
let save_to = save_to default_registry
let load_from = load_from default_registry
let clear () = Hashtbl.clear default_registry

let get_string = get_typed string
let get_int = get_typed int
let get_float = get_typed float
let get_bool = get_typed bool
let set_string = set_typed of_string
let set_int = set_typed of_int
let set_float = set_typed of_float
let set_bool = set_typed of_bool

