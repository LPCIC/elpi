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
 * http://cs.unibo.it/helm/.
 *)

(* $Id: hExtlib.ml 11875 2012-03-06 16:25:44Z sacerdot $ *)

(** PROFILING *)

let profiling_enabled = ref false ;; (* ComponentsConf.profiling *)

let something_profiled = ref false

let _ = 
  if !something_profiled then
    at_exit 
      (fun _ -> 
        prerr_endline 
         (Printf.sprintf "!! %39s ---------- --------- --------- ---------" 
           (String.make 39 '-'));
        prerr_endline 
         (Printf.sprintf "!! %-39s %10s %9s %9s %9s" 
           "function" "#calls" "total" "max" "average"))

let profiling_printings = ref (fun _ -> true)
let set_profiling_printings f = profiling_printings := f

type profiler = { profile : 'a 'b. ('a -> 'b) -> 'a -> 'b }
let profile ?(enable = true) s =
 if !profiling_enabled && enable then
   let total = ref 0.0 in
   let calls = ref 0 in
   let max = ref 0.0 in
   let profile f x =
    if not !profiling_enabled then f x else
    let before = Unix.gettimeofday () in
    try
     incr calls;
     let res = f x in
     let after = Unix.gettimeofday () in
     let delta = after -. before in
      total := !total +. delta;
      if delta > !max then max := delta;
      res
    with
     exc ->
      let after = Unix.gettimeofday () in
      let delta = after -. before in
       total := !total +. delta;
       if delta > !max then max := delta;
       raise exc
   in
   at_exit
    (fun () ->
      if !profiling_printings s && !calls <> 0 then
       begin
        something_profiled := true;
        prerr_endline
         (Printf.sprintf "!! %-39s %10d %9.4f %9.4f %9.4f" 
         s !calls !total !max (!total /. (float_of_int !calls)))
       end);
   { profile = profile }
 else
   { profile = fun f x -> f x }

(** {2 Optional values} *)

let map_option f = function None -> None | Some v -> Some (f v)
let iter_option f = function None -> () | Some v -> f v
let unopt = function None -> failwith "unopt: None" | Some v -> v

(** {2 String processing} *)

let split ?(sep = ' ') s =
  let pieces = ref [] in
  let rec aux idx =
    match (try Some (String.index_from s idx sep) with Not_found -> None) with
    | Some pos ->
        pieces := String.sub s idx (pos - idx) :: !pieces;
        aux (pos + 1)
    | None -> pieces := String.sub s idx (String.length s - idx) :: !pieces
  in
  aux 0;
  List.rev !pieces

let trim_blanks s =
  let rec find_left idx =
    match s.[idx] with
    | ' ' | '\t' | '\r' | '\n' -> find_left (idx + 1)
    | _ -> idx
  in
  let rec find_right idx =
    match s.[idx] with
    | ' ' | '\t' | '\r' | '\n' -> find_right (idx - 1)
    | _ -> idx
  in
  let s_len = String.length s in
  let left, right = find_left 0, find_right (s_len - 1) in
  String.sub s left (right - left + 1)

(** {2 Char processing} *)

let is_alpha c =
  let code = Char.code c in 
  (code >= 65 && code <= 90) || (code >= 97 && code <= 122)

let is_digit c =
  let code = Char.code c in 
  code >= 48 && code <= 57

let is_blank c =
  let code = Char.code c in 
  code = 9 || code = 10 || code = 13 || code = 32

let is_alphanum c = is_alpha c || is_digit c

(** {2 List processing} *)

let flatten_map f l =
  List.flatten (List.map f l)
;;

let list_mapi f l =
  let rec aux k = function
    | [] -> []
    | h::tl -> f h k :: aux (k+1) tl
  in
     aux 0 l
;;

let list_mapi_acc f a l =
  let rec aux k a res = function
    | [] -> a, List.rev res
    | h::tl -> let a,h = f h k a in aux (k+1) a (h::res) tl
  in
   aux 0 a [] l
;;

let list_index p =
 let rec aux n =
  function
     [] -> None
   | he::_ when p he -> Some (n,he)
   | _::tl -> aux (n + 1) tl
 in
  aux 0
;;

let rec list_iter_default2 f l1 def l2 = 
  match l1,l2 with
    | [], _ -> ()
    | a::ta, b::tb -> f a b; list_iter_default2 f ta def tb 
    | a::ta, [] -> f a def; list_iter_default2 f ta def [] 
;;

let rec list_forall_default3 f l1 l2 def l3 = 
  match l1,l2,l3 with
    | [], [], _ -> true
    | [], _, _
    | _, [], _ -> raise (Invalid_argument "list_forall_default3")
    | a::ta, b::tb, c::tc -> f a b c && list_forall_default3 f ta tb def tc
    | a::ta, b::tb, [] -> f a b def && list_forall_default3 f ta tb def [] 
;;

exception FailureAt of int;;

let list_forall_default3_var f l1 l2 def l3 = 
  let rec aux f l1 l2 def l3 i =
    match l1,l2,l3 with
      | [], [], _ -> true
      | [], _, _
      | _, [], _ -> raise (Invalid_argument "list_forall_default3")
      | a::ta, b::tb, c::tc -> 
      	  if f a b c then aux f ta tb def tc (i+1)
	  else raise (FailureAt i)
      | a::ta, b::tb, [] ->
      	  if f a b def then aux f ta tb def [] (i+1)
	  else raise (FailureAt i)
  in aux f l1 l2 def l3 0
;;

let sharing_map f l =
  let unchanged = ref true in
  let rec aux b = function
    | [] as t -> unchanged := b; t
    | he::tl ->
        let he1 = f he in
        he1 :: aux (b && he1 == he) tl
  in
  let l1 = aux true l in
  if !unchanged then l else l1
;;
        
let sharing_map_acc f acc l =
  let unchanged = ref true in
  let final_acc = ref acc in
  let rec aux b acc = function
    | [] as t -> unchanged := b; final_acc := acc; t
    | he::tl ->
        let acc, he1 = f acc he in
        he1 :: aux (b && he1 == he) acc tl
  in
  let l1 = aux true acc l in
  !final_acc, if !unchanged then l else l1
;;

let rec list_uniq ?(eq=(=)) = function 
  | [] -> []
  | h::[] -> [h]
  | h1::h2::tl when eq h1 h2 -> list_uniq ~eq (h2 :: tl) 
  | h1::tl (* when h1 <> h2 *) -> h1 :: list_uniq ~eq tl

let rec filter_map f =
  function
  | [] -> []
  | hd :: tl ->
      (match f hd with
      | None -> filter_map f tl
      | Some v -> v :: filter_map f tl)

let filter_map_acc f acc l =
  let acc, res = 
   List.fold_left
    (fun (acc, res) t ->
       match f acc t with
       | None -> acc, res
       | Some (acc, x) -> acc, x::res)
    (acc,[]) l
  in
   acc, List.rev res
;;

let filter_map_monad f acc l =
  let acc, res = 
   List.fold_left
    (fun (acc, res) t ->
       match f acc t with
       | acc, None -> acc, res
       | acc, Some x -> acc, x::res)
    (acc,[]) l
  in
   acc, List.rev res
;;

let list_rev_map_filter f l =
   let rec aux a = function
      | []       -> a
      | hd :: tl -> 
         begin match f hd with
	    | None   -> aux a tl
	    | Some b -> aux (b :: a) tl 
         end
   in 
   aux [] l

let list_rev_map_filter_fold f v l =
   let rec aux v a = function
      | []       -> v, a
      | hd :: tl -> 
         begin match f v hd with
	    | v, None   -> aux v a tl
	    | v, Some b -> aux v (b :: a) tl 
         end
   in 
   aux v [] l

let list_concat ?(sep = []) =
  let rec aux acc =
    function
    | [] -> []
    | [ last ] -> List.flatten (List.rev (last :: acc))
    | hd :: tl -> aux ([sep; hd] @ acc) tl
  in
  aux []
  
let list_iter_sep ~sep f =
  let rec aux =
    function
    | [] -> ()
    | [ last ] -> f last
    | hd :: tl -> f hd; sep (); aux tl
  in
  aux
  
let rec list_findopt f l = 
  let rec aux k = function 
    | [] -> None 
    | x::tl -> 
        (match f x k with
        | None -> aux (succ k) tl
        | Some _ as rc -> rc)
  in
  aux 0 l

let split_nth n l =
  let rec aux acc n l =
    match n, l with
    | 0, _ -> List.rev acc, l
    | n, [] -> raise (Failure "HExtlib.split_nth")
    | n, hd :: tl -> aux (hd :: acc) (n - 1) tl in
  aux [] n l

let list_last l =
  let l = List.rev l in 
  try List.hd l with exn -> raise (Failure "HExtlib.list_last")
;;

let rec list_assoc_all a = function
   | []                      -> []
   | (x, y) :: tl when x = a -> y :: list_assoc_all a tl
   | _ :: tl                 -> list_assoc_all a tl
;;

let rec rm_assoc_option n = function
  | [] -> None,[]
  | (x,i)::tl when n=x -> Some i,tl
  | p::tl -> let i,tl = rm_assoc_option n tl in i,p::tl
;;

let rm_assoc_assert n l =
  match rm_assoc_option n l with
  | None,_ -> assert false
  | Some i,l -> i,l
;;

(* naif implementation of the union-find merge operation
   canonicals maps elements to canonicals
   elements maps canonicals to the classes *)
let merge canonicals elements extern n m =
  let cn,canonicals = rm_assoc_option n canonicals in
  let cm,canonicals = rm_assoc_option m canonicals in
    match cn,cm with
      | None, None -> canonicals, elements, extern
      | None, Some c
      | Some c, None -> 
	  let l,elements = rm_assoc_assert c elements in
          let canonicals = 
	    List.filter (fun (_,xc) -> not (xc = c)) canonicals 
	  in
	    canonicals,elements,l@extern
      | Some cn, Some cm when cn=cm ->
	  (n,cm)::(m,cm)::canonicals, elements, extern
      | Some cn, Some cm ->
	  let ln,elements = rm_assoc_assert cn elements in
	  let lm,elements = rm_assoc_assert cm elements in
	  let canonicals = 
	    (n,cm)::(m,cm)::List.map 
	      (fun ((x,xc) as p)  -> 
		 if xc = cn then (x,cm) else p) canonicals
	  in 
	  let elements = (cm,ln@lm)::elements 
	  in
	    canonicals,elements,extern
;;

(* f x gives the direct dependencies of x.
   x must not belong to (f x). 
   All elements not in l are merged into a single extern class *)
let clusters f l =
  let canonicals = List.map (fun x -> (x,x)) l in
  let elements = List.map (fun x -> (x,[x])) l in
  let extern = [] in
  let _,elements,extern = 
    List.fold_left 
     (fun (canonicals,elements,extern) x ->
       let dep = f x in
	 List.fold_left 
	   (fun (canonicals,elements,extern) d ->
	      merge canonicals elements extern d x) 
	   (canonicals,elements,extern) dep)
     (canonicals,elements,extern) l
  in
  let c = (List.map snd elements) in
  if extern = [] then c else extern::c
;;

(** {2 File predicates} *)

let is_dir fname =
  try
    (Unix.stat fname).Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error _ -> false

let writable_dir path =
  try
    let file = path ^ "/prova_matita" in
    let oc = open_out file in
    close_out oc;
    Sys.remove file;
    true
  with Sys_error _ -> false


let is_regular fname =
  try
    (Unix.stat fname).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error _ -> false

let is_executable fname =
  try
    let stat = (Unix.stat fname) in
    stat.Unix.st_kind = Unix.S_REG &&
    (stat.Unix.st_perm land 0o001 > 0)
  with Unix.Unix_error _ -> false

let chmod mode filename =
   Unix.chmod filename mode

let mkdir path =
  let components = split ~sep:'/' path in
  let rec aux where = function
    | [] -> ()
    | piece::tl -> 
        let path =
          if where = "" then piece else where ^ "/" ^ piece in
        (try
          Unix.mkdir path 0o755; chmod 0o2775 path 
        with 
        | Unix.Unix_error (Unix.EEXIST,_,_) -> ()
        | Unix.Unix_error (Unix.EISDIR,_,_) -> () (* work-around for a bug in FreeBSD *)
        | Unix.Unix_error (e,_,_) -> 
            raise 
              (Failure 
                ("Unix.mkdir " ^ path ^ " 0o2775 :" ^ (Unix.error_message e))));
        aux path tl
  in
  let where = if path.[0] = '/' then "/" else "" in
  aux where components

(** {2 Filesystem} *)

let input_file fname =
  let size = (Unix.stat fname).Unix.st_size in
  let buf = Buffer.create size in
  let ic = open_in fname in
  Buffer.add_channel buf ic size;
  close_in ic;
  Buffer.contents buf

let input_all ic =
  let size = 10240 in
  let buf = Buffer.create size in
  let s = String.create size in
  (try
    while true do
      let bytes = input ic s 0 size in
      if bytes = 0 then raise End_of_file
      else Buffer.add_substring buf s 0 bytes
    done
  with End_of_file -> ());
  Buffer.contents buf

let output_file ~filename ~text = 
  let oc = open_out filename in
  output_string oc text;
  close_out oc;
  chmod 0o664 filename

let blank_split s =
  let len = String.length s in
  let buf = Buffer.create 0 in
  let rec aux acc i =
    if i >= len
    then begin
      if Buffer.length buf > 0
      then List.rev (Buffer.contents buf :: acc)
      else List.rev acc
    end else begin
      if is_blank s.[i] then
        if Buffer.length buf > 0 then begin
          let s = Buffer.contents buf in
          Buffer.clear buf;
          aux (s :: acc) (i + 1)
        end else
          aux acc (i + 1)
      else begin
        Buffer.add_char buf s.[i];
        aux acc (i + 1)
      end
    end
  in
  aux [] 0

  (* Rules: * "~name" -> home dir of "name"
   * "~" -> value of $HOME if defined, home dir of the current user otherwise *)
let tilde_expand s =
  let get_home login = (Unix.getpwnam login).Unix.pw_dir in
  let expand_one s =
    let len = String.length s in
    if len > 0 && s.[0] = '~' then begin
      let login_len = ref 1 in
      while !login_len < len && is_alphanum (s.[!login_len]) do
        incr login_len
      done;
      let login = String.sub s 1 (!login_len - 1) in
      try
        let home =
          if login = "" then
            try Sys.getenv "HOME" with Not_found -> get_home (Unix.getlogin ())
          else
            get_home login
        in
        home ^ String.sub s !login_len (len - !login_len)
      with Not_found | Invalid_argument _ -> s
    end else
      s
  in
  String.concat " " (List.map expand_one (blank_split s))
  
let find ?(test = fun _ -> true) path = 
  let rec aux acc todo = 
    match todo with
    | [] -> acc
    | path :: tl ->
        try
          let handle = Unix.opendir path in
          let dirs = ref [] in
          let matching_files = ref [] in 
          (try 
            while true do 
              match Unix.readdir handle with
              | "." | ".." -> ()
              | entry ->
                  let qentry = path ^ "/" ^ entry in
                  (try
                    if is_dir qentry then
                      dirs := qentry :: !dirs
                    else if test qentry then
                      matching_files := qentry :: !matching_files;
                  with Unix.Unix_error _ -> ())
            done
          with End_of_file -> Unix.closedir handle);
          aux (!matching_files @ acc) (!dirs @ tl)
        with Unix.Unix_error _ -> aux acc tl
  in
  aux [] [path]

let safe_remove fname = if Sys.file_exists fname then Sys.remove fname

let is_dir_empty d =
 try
  let od = Unix.opendir d in
  let rec aux () =
   let name = Unix.readdir od in
   if name <> "." && name <> ".." then false else aux () in
  let res = try aux () with End_of_file -> true in
   Unix.closedir od;
   res
 with
  Unix.Unix_error _ -> true (* raised by Unix.opendir, we hope :-) *)

let safe_rmdir d = try Unix.rmdir d with Unix.Unix_error _ -> ()

let rec rmdir_descend d = 
  if is_dir_empty d then
    begin
      safe_rmdir d;
      rmdir_descend (Filename.dirname d)
    end


(** {2 Exception handling} *)

let finally at_end f arg =
  let res =
    try f arg
    with exn -> at_end (); raise exn
  in
  at_end ();
  res

(** {2 Localized exceptions } *)

exception Localized of Stdpp.location * exn

let loc_of_floc floc = Stdpp.first_pos floc, Stdpp.last_pos floc;;

let floc_of_loc (loc_begin, loc_end) =
 Stdpp.make_loc (loc_begin, loc_end)

let dummy_floc = floc_of_loc (0, 0)

let raise_localized_exception ~offset floc exn =
 let x, y = loc_of_floc floc in
 let x = offset + x in
 let y = offset + y in
 let floc = floc_of_loc (x,y) in
  raise (Localized (floc, exn))

let estimate_size x = 
  4 * (String.length (Marshal.to_string x [])) / 1024

let normalize_path s = 
  let s = Str.global_replace (Str.regexp "//") "/" s in
  let l = Str.split (Str.regexp "/") s in
  let rec aux acc = function
    | [] -> acc
    | he::"."::tl -> aux acc (he::tl)
    | he::".."::tl when he <> ".." -> aux [] (acc @ tl)
    | he::tl -> aux (acc@[he]) tl
  in
  (if Str.string_match (Str.regexp "^/") s 0 then "/" else "") ^
  String.concat "/" (aux [] l)
  ^ (if Str.string_match (Str.regexp "/$") s 0 then "/" else "")
;;

let find_in paths path =
   let rec aux = function
   | [] -> raise (Failure "find_in")
   | p :: tl ->
      let path = normalize_path (p ^ "/" ^ path) in
       try
         if (Unix.stat path).Unix.st_kind = Unix.S_REG then path
         else aux tl
       with Unix.Unix_error _ -> 
               aux tl
   in
   try
     aux paths
   with Unix.Unix_error _ | Failure _ -> 
     raise 
       (Failure "find_in")
;;

let is_prefix_of_aux d1 d2 = 
  let len1 = String.length d1 in
  let len2 = String.length d2 in
  if len2 < len1 then 
    false, len1, len2
  else
    let pref = String.sub d2 0 len1 in
    pref = d1 && (len1 = len2 || d1.[len1-1] = '/' || d2.[len1] = '/'), len1, len2

let is_prefix_of d1 d2 =
  let b,_,_ = is_prefix_of_aux d1 d2 in b
;;

let chop_prefix prefix s =
  let b,lp,ls = is_prefix_of_aux prefix s in
  if b then
    String.sub s lp (ls - lp)
  else 
    s
;;

let touch s =
  try close_out(open_out s) with Sys_error _ -> ()
;;

let rec mk_list x = function
  | 0 -> []
  | n -> x :: mk_list x (n-1)
;;

let list_seq start stop =
  if start > stop then [] else
  let rec aux pos =
    if pos = stop then []
    else pos :: (aux (pos+1))
  in
    aux start
;;

let rec list_skip n l =
  match n,l with
  | 0,_ -> l
  | n,_::l -> list_skip (n-1) l
  | _, [] -> assert false
;;

