(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: nCicLibrary.ml 13176 2016-04-18 15:29:33Z fguidi $ *)

exception LibraryOutOfSync of string Lazy.t
exception IncludedFileNotCompiled of string * string 

let magic = 2;;

let refresh_uri uri = NUri.uri_of_string (NUri.string_of_uri uri);;

let refresh_uri_in_universe =
 List.map (fun (x,u) -> x, refresh_uri u)
;;

let refresh_uri_in_reference (NReference.Ref (uri,spec)) =
 NReference.reference_of_spec (refresh_uri uri) spec

let refresh_uri_in_term status =
 let rec aux =
  function
  | NCic.Meta (i,(n,NCic.Ctx l)) ->
     NCic.Meta (i,(n,NCic.Ctx (List.map aux l)))
  | NCic.Meta _ as t -> t
  | NCic.Const ref -> NCic.Const (refresh_uri_in_reference ref)
  | NCic.Sort (NCic.Type l) -> NCic.Sort (NCic.Type (refresh_uri_in_universe l))
  | NCic.Match (NReference.Ref (uri,spec),outtype,term,pl) ->
     let r = NReference.reference_of_spec (refresh_uri uri) spec in
     let outtype = aux outtype in
     let term = aux term in
     let pl = List.map aux pl in
      NCic.Match (r,outtype,term,pl)
  | t -> NCicUtils.map status (fun _ _ -> ()) () (fun _ -> aux) t
in
 aux
;;

let refresh_uri_in_obj status (uri,height,metasenv,subst,obj_kind) =
 assert (metasenv = []);
 assert (subst = []);
 refresh_uri uri,height,metasenv,subst,
  NCicUntrusted.map_obj_kind (refresh_uri_in_term status) obj_kind
;;

let ng_path_of_baseuri ?(no_suffix=false) baseuri =
 let uri = NUri.string_of_uri baseuri in
 let path = String.sub uri 4 (String.length uri - 4) in
 let path = Helm_registry.get "matita.basedir" ^ path in
 let dirname = Filename.dirname path in
  HExtlib.mkdir dirname;
  if no_suffix then
   path
  else
   path ^ ".ng"
;;

let require_path path =
 let ch = open_in path in
 let mmagic,dump = Marshal.from_channel ch in
  close_in ch;
  if mmagic <> magic then
   raise (LibraryOutOfSync (lazy "The library is out of sync with the implementation. Please recompile the library."))
  else
   dump
;;

let require0 ~baseuri = require_path (ng_path_of_baseuri baseuri)

let db_path () = Helm_registry.get "matita.basedir" ^ "/ng_db.ng";;

type timestamp =
 [ `Obj of NUri.uri * NCic.obj 
 | `Constr of NCic.universe * NCic.universe] list *
 (NUri.uri * string * NReference.reference) list
;;

let time0 = [],[];;
let storage = ref [];;
let local_aliases = ref [];;

let load_db,set_global_aliases,get_global_aliases,add_deps,get_deps,remove_deps=
 let global_aliases = ref [] in
 let rev_includes_map = ref NUri.UriMap.empty in
 let store_db () =
  let ch = open_out (db_path ()) in
  Marshal.to_channel ch (magic,(!global_aliases,!rev_includes_map)) [];
  close_out ch in
 let load_db () =
  HExtlib.mkdir (Helm_registry.get "matita.basedir");
  try
   let ga,im = require_path (db_path ()) in
   let ga =
    List.map
     (fun (uri,name,NReference.Ref (uri2,spec)) ->
       refresh_uri uri,name,NReference.reference_of_spec (refresh_uri uri2) spec
     ) ga in
   let im =
    NUri.UriMap.fold
     (fun u l im -> NUri.UriMap.add (refresh_uri u) (List.map refresh_uri l) im
     ) im NUri.UriMap.empty
   in
    global_aliases := ga;
    rev_includes_map := im
  with
   Sys_error _ -> () in
 let get_deps u =
  let get_deps_one_step u =
    try NUri.UriMap.find u !rev_includes_map with Not_found -> [] in
  let rec aux res =
   function
      [] -> res
    | he::tl ->
       if List.mem he res then
        aux res tl
       else
        aux (he::res) (get_deps_one_step he @ tl)
  in
   aux [] [u] in
 let remove_deps u =
  rev_includes_map := NUri.UriMap.remove u !rev_includes_map;
  rev_includes_map :=
   NUri.UriMap.map
    (fun l -> List.filter (fun uri -> not (NUri.eq u uri)) l) !rev_includes_map;
  store_db ()
 in
  load_db,
  (fun ga -> global_aliases := ga; store_db ()),
  (fun () -> !global_aliases),
  (fun u l ->
    rev_includes_map := NUri.UriMap.add u (l @ get_deps u) !rev_includes_map;
    store_db ()),
  get_deps,
  remove_deps
;;

let init = load_db;;

class virtual status =
 object
  inherit NCic.status
  val timestamp = (time0 : timestamp)
  method timestamp = timestamp
  method set_timestamp v = {< timestamp = v >}
 end

let time_travel0 (sto,ali) =
 let diff_len = List.length !storage - List.length sto in
 let to_be_deleted,_ = HExtlib.split_nth diff_len !storage in
  if List.length to_be_deleted > 0 then
   List.iter NCicEnvironment.invalidate_item to_be_deleted;
  storage := sto; local_aliases := ali
;;

let time_travel status = time_travel0 status#timestamp;;

let replace status =
 let sto,ali = status#timestamp in
  storage := sto; local_aliases := ali
;;

type obj = string * Obj.t
(* includes are transitively closed; dependencies are only immediate *)
type dump =
 { objs: obj list ; includes: NUri.uri list; dependencies: string list }

class type g_dumpable_status =
 object
  method dump: dump
 end

class dumpable_status =
 object
  val db = { objs = []; includes = []; dependencies = [] }
  method dump = db
  method set_dump v = {< db = v >}
  method set_dumpable_status
   : 'status. #g_dumpable_status as 'status -> 'self
   = fun o -> {< db = o#dump >}
 end

let get_transitively_included status =
 status#dump.includes
;;

let dump_obj status obj =
 status#set_dump {status#dump with objs = obj::status#dump.objs }
;;

let remove_objects ~baseuri =
   let uri = NUri.string_of_uri baseuri in   
   let path = String.sub uri 4 (String.length uri - 4) in
   let path = Helm_registry.get "matita.basedir" ^ path in
   let map name = Sys.remove (Filename.concat path name) in
   if HExtlib.is_dir path && HExtlib.is_regular (path ^ ".ng") then begin
      HLog.warn ("removing contents of baseuri: " ^ uri);
      Array.iter map (Sys.readdir path)
   end

module type SerializerType =
 sig
  type dumpable_status

  type 'a register_type =
   'a ->
    refresh_uri_in_universe:(NCic.universe -> NCic.universe) ->
    refresh_uri_in_term:(NCic.status -> NCic.term -> NCic.term) ->
    refresh_uri_in_reference:(NReference.reference -> NReference.reference) ->
    alias_only:bool ->
     dumpable_status -> dumpable_status

  val register: < run: 'a.  string -> 'a register_type -> ('a -> obj) >
  val serialize: baseuri:NUri.uri -> dumpable_status -> unit
  val require:
   baseuri:NUri.uri -> fname:string -> alias_only:bool ->
    dumpable_status -> dumpable_status
  val dependencies_of: baseuri:NUri.uri -> string list
 end

module Serializer(D: sig type dumpable_s = private #dumpable_status end) =
 struct
  type dumpable_status = D.dumpable_s
  type 'a register_type =
   'a ->
    refresh_uri_in_universe:(NCic.universe -> NCic.universe) ->
    refresh_uri_in_term:(NCic.status -> NCic.term -> NCic.term) ->
    refresh_uri_in_reference:(NReference.reference -> NReference.reference) ->
    alias_only:bool ->
     dumpable_status -> dumpable_status

  let require1 = ref (fun ~alias_only:_ _ -> assert false) (* unknown data*)
  let already_registered = ref []

  let register =
   object
    method run : 'a.  string -> 'a register_type -> ('a -> obj)
    = fun tag require ->
     assert (not (List.mem tag !already_registered));
     already_registered := tag :: !already_registered;
     let old_require1 = !require1 in
     require1 :=
      (fun ~alias_only ((tag',data) as x) ->
        if tag=tag' then
         require (Obj.magic data) ~refresh_uri_in_universe ~refresh_uri_in_term
          ~refresh_uri_in_reference ~alias_only
        else
         old_require1 ~alias_only x);
     (fun x -> tag,Obj.repr x)
   end

  let serialize ~baseuri status =
   let ch = open_out (ng_path_of_baseuri baseuri) in
   Marshal.to_channel ch (magic,(status#dump.dependencies,status#dump.objs)) [];
   close_out ch;
(*
   remove_objects ~baseuri; (* FG: we remove the old objects before putting the new ones*)
*)
   List.iter
    (function 
     | `Obj (uri,obj) ->
         let ch = open_out (ng_path_of_baseuri uri) in
         Marshal.to_channel ch (magic,obj) [];
         close_out ch
     | `Constr _ -> ()
    ) !storage;
   set_global_aliases (!local_aliases @ get_global_aliases ());
   List.iter (fun u -> add_deps u [baseuri]) status#dump.includes;
   time_travel0 time0

  let require2 ~baseuri ~alias_only status =
   try
    let status =
     status#set_dump
      {status#dump with
        includes = baseuri::List.filter ((<>) baseuri) status#dump.includes} in
    let _dependencies,dump = require0 ~baseuri in
     List.fold_right (!require1 ~alias_only) dump status
   with
    Sys_error _ ->
     raise (IncludedFileNotCompiled(ng_path_of_baseuri baseuri,NUri.string_of_uri baseuri))

  let dependencies_of ~baseuri = fst (require0 ~baseuri)

  let record_include =
   let aux (baseuri,fname) ~refresh_uri_in_universe:_ ~refresh_uri_in_term:_
   ~refresh_uri_in_reference:_ ~alias_only status =
     let baseuri = refresh_uri baseuri in
     if not alias_only && List.mem baseuri (get_transitively_included status) then status
     else
      (HLog.warn ("include " ^ (if alias_only then "alias " else "") ^ fname);
      let status = require2 ~baseuri ~alias_only status in
      HLog.warn ("done: include " ^ (if alias_only then "alias " else "") ^ fname);
      status)
   in
    register#run "include" aux

  let require ~baseuri ~fname ~alias_only status =
   if not alias_only && List.mem baseuri (get_transitively_included status) then status
   else
    (let status =
     if not alias_only then
      status#set_dump
       {status#dump with dependencies = fname::status#dump.dependencies}
     else
      status in
    let status = require2 ~baseuri ~alias_only status in
      status#set_dump
       {status#dump with
         objs = record_include (baseuri,fname)::status#dump.objs })
end

let fetch_obj status uri =
 let obj = require0 ~baseuri:uri in
  refresh_uri_in_obj status obj
;;

let resolve name =
 try
  HExtlib.filter_map
   (fun (_,name',nref) -> if name'=name then Some nref else None)
   (!local_aliases @ get_global_aliases ())
 with
  Not_found -> raise (NCicEnvironment.ObjectNotFound (lazy name))
;;

let aliases_of uri =
  HExtlib.filter_map
   (fun (uri',_,nref) ->
     if NUri.eq uri' uri then Some nref else None) !local_aliases
;;

let add_obj status ((u,_,_,_,_) as orig_obj) =
 NCicEnvironment.check_and_add_obj status orig_obj;
 storage := (`Obj (u,orig_obj))::!storage;
  let _,height,_,_,obj = orig_obj in
  let references =
   match obj with
      NCic.Constant (_,name,None,_,_) ->
       [u,name,NReference.reference_of_spec u NReference.Decl]
    | NCic.Constant (_,name,Some _,_,_) ->
       [u,name,NReference.reference_of_spec u (NReference.Def height)]
    | NCic.Fixpoint (is_ind,fl,_) ->
       HExtlib.list_mapi
        (fun (_,name,recno,_,_) i ->
          if is_ind then
           u,name,NReference.reference_of_spec u(NReference.Fix(i,recno,height))
          else
           u,name,NReference.reference_of_spec u (NReference.CoFix i)) fl
    | NCic.Inductive (inductive,leftno,il,_) ->
       List.flatten
        (HExtlib.list_mapi
         (fun (_,iname,_,cl) i ->
           HExtlib.list_mapi
            (fun (_,cname,_) j->
              u,cname,
               NReference.reference_of_spec u (NReference.Con (i,j+1,leftno))
            ) cl @
           [u,iname,
             NReference.reference_of_spec u
              (NReference.Ind (inductive,i,leftno))]
         ) il)
  in
  local_aliases := references @ !local_aliases;
  status#set_timestamp (!storage,!local_aliases)
;;

let add_constraint status ~acyclic u1 u2 = 
  if
   List.exists
    (function `Constr (u1',u2') when u1=u1' && u2=u2' -> true | _ -> false)
    !storage
  then
   (*CSC: raise an exception here! *)
   (prerr_endline "CANNOT ADD A CONSTRAINT TWICE"; assert false);
  NCicEnvironment.add_lt_constraint ~acyclic u1 u2;
  storage := (`Constr (u1,u2)) :: !storage;
  status#set_timestamp (!storage,!local_aliases)
;;

let get_obj status u =
 try 
  List.assq u 
   (HExtlib.filter_map 
    (function `Obj (u,o) -> Some (u,o) | _ -> None )
    !storage)
 with Not_found ->
  try fetch_obj status u
  with Sys_error _ ->
   raise (NCicEnvironment.ObjectNotFound (lazy (NUri.string_of_uri u)))
;;

NCicEnvironment.set_get_obj get_obj
