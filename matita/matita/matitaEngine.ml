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

(* $Id: matitaEngine.ml 12567 2013-03-18 21:03:54Z fguidi $ *)

module G = GrafiteAst
open GrafiteTypes
open Printf

class status baseuri =
 object
  inherit GrafiteTypes.status baseuri
  inherit ApplyTransformation.status
 end

exception TryingToAdd of string Lazy.t
exception EnrichedWithStatus of exn * status
exception AlreadyLoaded of string Lazy.t
exception FailureCompiling of string * exn
exception CircularDependency of string

let debug = false ;;
let debug_print = if debug then prerr_endline else ignore ;;

let slash_n_RE = Pcre.regexp "\\n" ;;

let pp_ast_statement status stm =
  let stm = GrafiteAstPp.pp_statement status stm
    ~map_unicode_to_tex:(Helm_registry.get_bool "matita.paste_unicode_as_tex")
  in
  let stm = Pcre.replace ~rex:slash_n_RE stm in
  let stm =
      if String.length stm > 50 then String.sub stm 0 50 ^ " ..."
      else stm
  in
    HLog.debug ("Executing: ``" ^ stm ^ "''")
;;

let clean_exit baseuri exn =
  LibraryClean.clean_baseuris ~verbose:false [baseuri];
  raise (FailureCompiling (baseuri,exn))
;;

let cut prefix s = 
  let lenp = String.length prefix in
  let lens = String.length s in
  assert (lens > lenp);
  assert (String.sub s 0 lenp = prefix);
  String.sub s lenp (lens-lenp)
;;

let print_string = 
 let indent = ref 0 in
 let print_string ~right_justify s =
  let ss =
   match right_justify with
      None -> ""
    | Some (ss,len_ss) ->
       let i = 80 - !indent - len_ss - String.length s in
       if i > 0 then String.make i ' ' ^ ss else ss
  in
   assert (!indent >=0);
   print_string (String.make !indent ' ' ^ s ^ ss) in
 fun enter ?right_justify s ->
  if enter then (print_string ~right_justify s; incr indent) else (decr indent; print_string ~right_justify s)
;;

let pp_times ss fname rc big_bang big_bang_u big_bang_s = 
  if not (Helm_registry.get_bool "matita.verbose") then
    let { Unix.tms_utime = u ; Unix.tms_stime = s} = Unix.times () in
    let r = Unix.gettimeofday () -. big_bang in
    let u = u -. big_bang_u in
    let s = s -. big_bang_s in
    let extra = try Sys.getenv "BENCH_EXTRA_TEXT" with Not_found -> "" in
    let rc = 
      if rc then "[0;32mOK[0m" else "[0;31mFAIL[0m" in
    let times = 
      let fmt t = 
        let seconds = int_of_float t in
        let cents = int_of_float ((t -. floor t) *. 100.0) in
        let minutes = seconds / 60 in
        let seconds = seconds mod 60 in
        Printf.sprintf "%dm%02d.%02ds" minutes seconds cents
      in
      Printf.sprintf "%s %s %s" (fmt r) (fmt u) (fmt s)
    in
    let s = Printf.sprintf "%-14s %s %s\n" rc times extra in
    print_string false ~right_justify:(s,31) ss;
    flush stdout;
    HLog.message ("Compilation of "^Filename.basename fname^": "^rc)
;;

let eval_ast ~include_paths ?do_heavy_checks status (text,prefix_len,ast) =
 let baseuri = status#baseuri in
 let new_aliases,new_status =
  GrafiteDisambiguate.eval_with_new_aliases status
   (fun status ->
   let time0 = Unix.gettimeofday () in
   let status =
     GrafiteEngine.eval_ast ~include_paths ?do_heavy_checks status
      (text,prefix_len,ast) in
   let time1 = Unix.gettimeofday () in
   HLog.debug ("... grafite_engine done in " ^ string_of_float (time1 -. time0) ^ "s");
   status
   ) in
 let _,intermediate_states = 
  List.fold_left
   (fun (status,acc) (k,value) -> 
     let v = GrafiteAst.description_of_alias value in
     let b =
      try
       let NReference.Ref (uri,_) = NReference.reference_of_string v in
        NUri.baseuri_of_uri uri = baseuri
      with
       NReference.IllFormedReference _ ->
        false (* v is a description, not a URI *)
     in
      if b then 
       status,acc
      else
       let status =
        GrafiteDisambiguate.set_proof_aliases status ~implicit_aliases:false
         GrafiteAst.WithPreferences [k,value]
       in
        status, (status ,Some (k,value))::acc
   ) (status,[]) new_aliases (* WARNING: this must be the old status! *)
 in
  (new_status,None)::intermediate_states
;;

let baseuri_of_script ~include_paths fname =
 try Librarian.baseuri_of_script ~include_paths fname
 with
   Librarian.NoRootFor _ -> 
    HLog.error ("The included file '"^fname^"' has no root file,");
    HLog.error "please create it.";
    raise (Failure ("No root file for "^fname))
  | Librarian.FileNotFound _ -> 
    raise (Failure ("File not found: "^fname))
;;

(* given a path to a ma file inside the include_paths, returns the
   new include_paths associated to that file *)
let read_include_paths ~include_paths file =
 try 
   let root, _buri, _fname, _tgt = 
     Librarian.baseuri_of_script ~include_paths:[] file in 
   let includes =
    try
     Str.split (Str.regexp " ") 
      (List.assoc "include_paths" (Librarian.load_root_file (root^"/root")))
    with Not_found -> []
   in
   let rc = root :: includes in
    List.iter (HLog.debug) rc; rc
 with Librarian.NoRootFor _ | Librarian.FileNotFound _ ->
  []
;;

let rec get_ast status ~compiling ~asserted ~include_paths strm = 
  match GrafiteParser.parse_statement status strm with
     (GrafiteAst.Executable
       (_,GrafiteAst.NCommand (_,GrafiteAst.Include (_,_,mafilename)))) as cmd
     ->
       let already_included = NCicLibrary.get_transitively_included status in
       let asserted,_ =
        assert_ng ~already_included ~compiling ~asserted ~include_paths
         mafilename
       in
        asserted,cmd
   | cmd -> asserted,cmd

and eval_from_stream ~compiling ~asserted ~include_paths ?do_heavy_checks status str cb =
 let matita_debug = Helm_registry.get_bool "matita.debug" in
 let rec loop asserted status str =
  let asserted,stop,status,str = 
   try
     let cont =
       try Some (get_ast status ~compiling ~asserted ~include_paths str)
       with End_of_file -> None in
     match cont with
     | None -> asserted, true, status, str
     | Some (asserted,ast) ->
        cb status ast;
        let new_statuses =
          eval_ast ~include_paths ?do_heavy_checks status ("",0,ast) in
        let status =
         match new_statuses with
            [s,None] -> s
          | _::(_,Some (_,value))::_ ->
                raise (TryingToAdd (lazy (GrafiteAstPp.pp_alias value)))
          | _ -> assert false in
        (* CSC: complex patch to re-build the lexer since the tokens may
           have changed. Note: this way we loose look-ahead tokens.
           Hence the "include" command must be terminated (no look-ahead) *)
        let str =
         match ast with
            (GrafiteAst.Executable
              (_,GrafiteAst.NCommand
                (_,(GrafiteAst.Include _ | GrafiteAst.Notation _)))) ->
              GrafiteParser.parsable_statement status
               (GrafiteParser.strm_of_parsable str)
          | _ -> str
        in
         asserted, false, status, str
   with exn when not matita_debug ->
     raise (EnrichedWithStatus (exn, status))
  in
  if stop then asserted,status else loop asserted status str
 in
  loop asserted status str

and compile ~compiling ~asserted ~include_paths fname =
  if List.mem fname compiling then raise (CircularDependency fname);
  let compiling = fname::compiling in
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  let root,baseuri,fname,_tgt = 
    Librarian.baseuri_of_script ~include_paths fname in
  if Http_getter_storage.is_read_only baseuri then assert false;
  (* MATITA 1.0: debbo fare time_travel sulla ng_library? *)
  let status = new status baseuri in
  (*CSC: bad, one imperative bit is still there!
         to be moved into functional status *)
  NCicMetaSubst.pushmaxmeta ();
  let ocamldirname = Filename.dirname fname in
  let ocamlfname = Filename.chop_extension (Filename.basename fname) in
  let status,ocamlfname =
   Common.modname_of_filename status false ocamlfname in
  let ocamlfname = ocamldirname ^ "/" ^ ocamlfname ^ ".ml" in
  let status = OcamlExtraction.open_file status ~baseuri ocamlfname in
  let big_bang = Unix.gettimeofday () in
  let { Unix.tms_utime = big_bang_u ; Unix.tms_stime = big_bang_s} = 
    Unix.times () 
  in
  let time = Unix.time () in
  let cc = 
   let rex = Str.regexp ".*opt$" in
   if Str.string_match rex Sys.argv.(0) 0 then "matitac.opt"
   else "matitac" in
  let s = Printf.sprintf "%s %s" cc (cut (root^"/") fname) in
  try
    (* cleanup of previously compiled objects *)
    if (not (Http_getter_storage.is_empty ~local:true baseuri))
      then begin
      HLog.message ("baseuri " ^ baseuri ^ " is not empty");
      HLog.message ("cleaning baseuri " ^ baseuri);
      LibraryClean.clean_baseuris [baseuri];
    end;
    HLog.message ("compiling " ^ Filename.basename fname ^ " in " ^ baseuri);
    if not (Helm_registry.get_bool "matita.verbose") then
     (print_string true (s ^ "\n"); flush stdout);
    (* we dalay this error check until we print 'matitac file ' *)
    assert (Http_getter_storage.is_empty ~local:true baseuri);
    (* create dir for XML files *)
    if not (Helm_registry.get_opt_default Helm_registry.bool "matita.nodisk"
              ~default:false) 
    then
      HExtlib.mkdir 
        (Filename.dirname 
          (Http_getter.filename ~local:true ~writable:true (baseuri ^
          "foo.con")));
    let buf =
     GrafiteParser.parsable_statement status
      (Ulexing.from_utf8_channel (open_in fname))
    in
    let print_cb =
      if not (Helm_registry.get_bool "matita.verbose") then (fun _ _ -> ())
      else pp_ast_statement
    in
    let asserted, status =
     eval_from_stream ~compiling ~asserted ~include_paths status buf print_cb in
    let status = OcamlExtraction.close_file status in
    let elapsed = Unix.time () -. time in
     (if Helm_registry.get_bool "matita.moo" then begin
       GrafiteTypes.Serializer.serialize ~baseuri:(NUri.uri_of_string baseuri)
        status
     end;
     let tm = Unix.gmtime elapsed in
     let sec = string_of_int tm.Unix.tm_sec ^ "''" in
     let min = 
       if tm.Unix.tm_min > 0 then (string_of_int tm.Unix.tm_min^"' ") else "" 
     in
     let hou = 
       if tm.Unix.tm_hour > 0 then (string_of_int tm.Unix.tm_hour^"h ") else ""
     in
     HLog.message 
       (sprintf "execution of %s completed in %s." fname (hou^min^sec));
     pp_times s fname true big_bang big_bang_u big_bang_s;
     (*CSC: bad, one imperative bit is still there!
            to be moved into functional status *)
     NCicMetaSubst.pushmaxmeta ();
(* MATITA 1.0: debbo fare time_travel sulla ng_library?
     LexiconSync.time_travel 
       ~present:lexicon_status ~past:initial_lexicon_status;
*)
     asserted)
  with 
  (* all exceptions should be wrapped to allow lexicon-undo (LS.time_travel) *)
  | exn when not matita_debug ->
(* MATITA 1.0: debbo fare time_travel sulla ng_library?
       LexiconSync.time_travel ~present:lexicon ~past:initial_lexicon_status;
 *       *)
      (*CSC: bad, one imperative bit is still there!
             to be moved into functional status *)
      NCicMetaSubst.pushmaxmeta ();
      pp_times s fname false big_bang big_bang_u big_bang_s;
      clean_exit baseuri exn

and assert_ng ~already_included ~compiling ~asserted ~include_paths mapath =
 let root,baseuri,fullmapath,_ =
  Librarian.baseuri_of_script ~include_paths mapath in
 if List.mem fullmapath asserted then asserted,false
 else
  begin
   let include_paths =
    let includes =
     try
      Str.split (Str.regexp " ") 
       (List.assoc "include_paths" (Librarian.load_root_file (root^"/root")))
     with Not_found -> []
    in
     root::includes @
      Helm_registry.get_list Helm_registry.string "matita.includes" in
   let baseuri = NUri.uri_of_string baseuri in
   let ngtime_of baseuri =
    let ngpath = NCicLibrary.ng_path_of_baseuri baseuri in
    try
     Some (Unix.stat ngpath).Unix.st_mtime
    with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = ngpath -> None in
   let matime =
    try (Unix.stat fullmapath).Unix.st_mtime
    with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = fullmapath -> assert false
   in
   let ngtime = ngtime_of baseuri in
   let asserted,to_be_compiled =
    match ngtime with
       Some ngtime ->
        let preamble = GrafiteTypes.Serializer.dependencies_of baseuri in
        let asserted,children_bad =
         List.fold_left
          (fun (asserted,b) mapath -> 
	    let asserted,b1 =
              try 
	       assert_ng ~already_included ~compiling ~asserted ~include_paths
                mapath
	      with Librarian.NoRootFor _ | Librarian.FileNotFound _ ->
	        asserted, true 
            in
             asserted, b || b1
              || let _,baseuri,_,_ =
                   (*CSC: bug here? include_paths should be empty and
                          mapath should be absolute *)
                   Librarian.baseuri_of_script ~include_paths mapath in
                 let baseuri = NUri.uri_of_string baseuri in
                  (match ngtime_of baseuri with
                      Some child_ngtime -> child_ngtime > ngtime
                    | None -> assert false)
          ) (asserted,false) preamble
        in
         asserted, children_bad || matime > ngtime
     | None -> asserted,true
   in
    if not to_be_compiled then fullmapath::asserted,false
    else
     if List.mem baseuri already_included then
       (* maybe recompiling it I would get the same... *)
       raise (AlreadyLoaded (lazy mapath))
     else
      let asserted = compile ~compiling ~asserted ~include_paths fullmapath in
       fullmapath::asserted,true
  end
;;

let assert_ng ~include_paths mapath =
 snd (assert_ng ~include_paths ~already_included:[] ~compiling:[] ~asserted:[]
  mapath)
let get_ast status ~include_paths strm =
 snd (get_ast status ~compiling:[] ~asserted:[] ~include_paths strm)
