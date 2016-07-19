open OcamlExtractionTable
open Coq

let print_ocaml_of_obj0 status ((_uri,_,_,_,_) as obj) =
 try
  let status,res,resl = Extraction.extract status obj in
  let status,_ =
   map_status status
    (fun status ml ->
      let status,cmds = Ocaml.pp_spec status ml in
      print_ppcmds ~in_ml:false status (cmds ++ fnl () ++ fnl ());
      status,()) resl in
  let status,_ =
   map_status status
    (fun status ml ->
      let status,cmds = Ocaml.pp_decl status ml in
      print_ppcmds ~in_ml:true status (cmds ++ fnl () ++ fnl ());
      status,()) res in
  status
 with
    HExtlib.Localized (_,exn)
  | exn ->
     prerr_endline (Printexc.to_string exn); assert false

let do_if_ocaml_set f status =
 if try ignore (Helm_registry.get "extract_ocaml"); true
    with Helm_registry.Key_not_found _ -> false
 then f status else status

let print_open status uris =
 do_if_ocaml_set
  (fun status ->
    let status,uris =
     map_status status
      (fun status uri ->
        let status,b = to_be_included status uri in
         status, if b then Some uri else None
      ) uris in
    let uris = HExtlib.filter_map (fun x -> x) uris in
    let fnames =
     List.map (fun uri -> Filename.basename (NUri.string_of_uri uri)) uris in
    let status,cmds = map_status status Ocaml.pp_open fnames in
    List.iter (print_ppcmds status ~in_ml:true) cmds;
    let status,cmds = map_status status Ocaml.pp_open fnames in
    List.iter (print_ppcmds status ~in_ml:false) cmds;
    status
  ) status

let print_ocaml_of_obj status cmds =
 do_if_ocaml_set (fun status -> print_ocaml_of_obj0 status cmds) status

let open_file status ~baseuri fname =
 do_if_ocaml_set
  (fun status -> OcamlExtractionTable.open_file status ~baseuri fname) status

let close_file status =
 do_if_ocaml_set OcamlExtractionTable.close_file status
