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

(* $Id: matitaMisc.ml 11133 2010-12-20 17:24:55Z sacerdot $ *)

open Printf

(** Functions "imported" from Http_getter_misc *)

let normalize_dir = Http_getter_misc.normalize_dir
let strip_suffix ~suffix s = 
  try 
    Http_getter_misc.strip_suffix ~suffix s
  with Invalid_argument _ -> s

let absolute_path file =
  if file.[0] = '/' then file else Unix.getcwd () ^ "/" ^ file
  
let is_proof_script fname = true  (** TODO Zack *)
let is_proof_object fname = true  (** TODO Zack *)

let append_phrase_sep s =
  if not (Pcre.pmatch ~pat:(sprintf "%s$" BuildTimeConf.phrase_sep) s) then
    s ^ BuildTimeConf.phrase_sep
  else
    s

exception History_failure

type 'a memento = 'a array * int * int * int  (* data, hd, tl, cur *)

class type ['a] history =
  object
    method add : 'a -> unit
    method next : 'a
    method previous : 'a
    method load: 'a memento -> unit
    method save: 'a memento
    method is_begin: bool
    method is_end: bool
  end

class basic_history (head, tail, cur) =
  object
    val mutable hd = head  (* insertion point *)
    val mutable tl = tail (* oldest inserted item *)
    val mutable cur = cur  (* current item for the history *)
    
    method is_begin = cur <= tl
    method is_end = cur >= hd
  end
  
  
class shell_history size =
  let size = size + 1 in
  let decr x = let x' = x - 1 in if x' < 0 then size + x' else x' in
  let incr x = (x + 1) mod size in
  object (self)
    val data = Array.create size ""

    inherit basic_history (0, -1 , -1)
    
    method add s =
      data.(hd) <- s;
      if tl = -1 then tl <- hd;
      hd <- incr hd;
      if hd = tl then tl <- incr tl;
      cur <- hd
    method previous =
      if cur = tl then raise History_failure;
      cur <- decr cur;
      data.(cur)
    method next =
      if cur = hd then raise History_failure;
      cur <- incr cur;
      if cur = hd then "" else data.(cur)
    method load (data', hd', tl', cur') =
      assert (Array.length data = Array.length data');
      hd <- hd'; tl <- tl'; cur <- cur';
      Array.blit data' 0 data 0 (Array.length data')
    method save = (Array.copy data, hd, tl, cur)
  end

class ['a] browser_history ?memento size init =
  object (self)
    initializer match memento with Some m -> self#load m | _ -> ()
    val data = Array.create size init

    inherit basic_history (0, 0, 0)
    
    method previous =
      if cur = tl then raise History_failure;
      cur <- cur - 1;
      if cur = ~-1 then cur <- size - 1;
      data.(cur)
    method next =
      if cur = hd then raise History_failure;
      cur <- cur + 1;
      if cur = size then cur <- 0;
      data.(cur)
    method add (e:'a) =
      if e <> data.(cur) then
        begin
          cur <- cur + 1;
          if cur = size then cur <- 0;
          if cur = tl then tl <- tl + 1;
          if tl = size then tl <- 0;
          hd <- cur;
          data.(cur) <- e
        end
    method load (data', hd', tl', cur') =
      assert (Array.length data = Array.length data');
      hd <- hd'; tl <- tl'; cur <- cur';
      Array.blit data' 0 data 0 (Array.length data')
    method save = (Array.copy data, hd, tl, cur)
  end

let singleton f =
  let instance = lazy (f ()) in
  fun () -> Lazy.force instance

let image_path n = sprintf "%s/%s" BuildTimeConf.images_dir n

let end_ma_RE = Pcre.regexp "\\.ma$"

let list_tl_at ?(equality=(==)) e l =
  let rec aux =
    function
    | [] -> raise Not_found
    | hd :: tl as l when equality hd e -> l
    | hd :: tl -> aux tl
  in
  aux l

let shutup () = 
  HLog.set_log_callback (fun _ _ -> ())
(*
  let out = open_out "/dev/null" in
  Unix.dup2 (Unix.descr_of_out_channel out) (Unix.descr_of_out_channel stderr)
*)
              
(* FG: out_preamble *********************************************************)

let out_comment och s =
   let s = if s <> "" && s.[0] = '*' then "#" ^ s else s in
   Printf.fprintf och "%s%s%s\n\n" "(*" s "*)" 
 
let out_line_comment och s =
   let l = 70 - String.length s in
   let s = Printf.sprintf " %s %s" s (String.make l '*') in
   out_comment och s

let out_preamble och =
   let rt_base_dir = Filename.dirname Sys.argv.(0) in
   let path = Filename.concat rt_base_dir "matita.ma.templ" in
   let lines = 14 in
   let ich = open_in path in
   let rec print i =
      if i > 0 then 
         let s = input_line ich in
         begin Printf.fprintf och "%s\n" s; print (pred i) end
   in 
   print lines;
   out_line_comment och "This file was automatically generated: do not edit"

  (* is there any lablgtk2 constant corresponding to the various mouse
   * buttons??? *)
let left_button = 1
let middle_button = 2
let right_button = 3

(* Font size management *)
let default_font_size () =
  Helm_registry.get_opt_default Helm_registry.int
    ~default:BuildTimeConf.default_font_size "matita.font_size"
let current_font_size = ref (default_font_size ())
let font_size_observers = ref [];;
let observe_font_size (f: int -> unit) =
 f !current_font_size;
 font_size_observers := f :: !font_size_observers;;
let observe () =
 List.iter (fun f -> f !current_font_size) !font_size_observers;;
let get_current_font_size () = !current_font_size
let increase_font_size () =
 incr current_font_size; observe ()
let decrease_font_size () =
 decr current_font_size; observe ()
let reset_font_size () =
 current_font_size := default_font_size (); observe ()

let gui_instance = ref None
let set_gui (gui : MatitaGuiTypes.gui) = gui_instance := Some gui

(** CSC: these functions should completely disappear (bad design) *)
let get_gui () =
  match !gui_instance with
  | None -> assert false
  | Some gui -> gui
