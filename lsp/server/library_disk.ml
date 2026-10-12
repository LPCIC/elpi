(* The files of the standard library (see Checker.library_files), for the
   native server: they are written on the disk (read-only), where the editor
   can open them. *)

(* the directory where the directories of the libraries are made *)
let base () =
  match Sys.getenv_opt "XDG_RUNTIME_DIR" with
  | Some d when not (String.equal d "") && Sys.file_exists d && Sys.is_directory d -> d
  | _ -> Filename.get_temp_dir_name ()

(* the start of the names of these directories *)
let prefix () = Printf.sprintf "elpi-lsp-%d-" (Unix.getuid ())

(* Where the files are written: a directory per version of the text (the
   libraries of instances with different builtins differ), in
   XDG_RUNTIME_DIR (private to the user) or else in the temporary directory,
   shared by the servers of the user. Since its name is known, it is used only
   if it is a directory (not a link) of the user that the others cannot
   access; otherwise a new directory with a random name is made. It is made
   the first time it is needed; if that fails, the next time it is tried
   again. The directories are cached by the digest of the text. *)
let dir_cache : (Digest.t, string) Hashtbl.t = Hashtbl.create 3

let make_dir digest =
  let base = base () in
  let private_dir d =
    match Unix.lstat d with
    | { Unix.st_kind = Unix.S_DIR; st_uid; st_perm; _ } -> st_uid = Unix.getuid () && st_perm land 0o077 = 0
    | _ -> false
    | exception Unix.Unix_error _ -> false in
  let make d = try Unix.mkdir d 0o700; true with Unix.Unix_error _ -> false in
  let dir = Filename.concat base (prefix () ^ Digest.to_hex digest) in
  ignore (make dir);
  if private_dir dir then dir
  else begin
    Checker.log "%s is not a private directory, the library is written elsewhere" dir;
    let rnd = Random.State.make_self_init () in
    let rec fresh n =
      let d = Filename.concat base (Printf.sprintf "%s%06x" (prefix ()) (Random.State.bits rnd land 0xffffff)) in
      if make d then d else if n > 0 then fresh (n - 1) else failwith "cannot make a directory for the library" in
    fresh 100
  end

let dir instance =
  let all = Hashtbl.fold (fun name text acc -> name ^ text ^ acc) (Checker.library_files instance) "" in
  let digest = Digest.string all in
  match Hashtbl.find_opt dir_cache digest with
  | Some d -> d
  | None -> let d = make_dir digest in Hashtbl.replace dir_cache digest d; d

(* the file of the library [name] (eg builtin_stdlib.elpi) of an instance, as
   its path on the disk and its text, if there is one *)
let file instance name =
  let name = Filename.basename name in
  match Checker.library_text instance name with
  | None -> None
  | Some text ->
      let path = Filename.concat (dir instance) name in
      (try
         if not (Sys.file_exists path) then begin
           (* written aside then renamed: a file that is there is complete *)
           let tmp = Printf.sprintf "%s.%d.tmp" path (Unix.getpid ()) in
           let oc = open_out_gen [ Open_wronly; Open_creat; Open_trunc; Open_excl; Open_binary ] 0o444 tmp in
           Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc text);
           Sys.rename tmp path
         end;
         Some (path, text)
       with Sys_error _ | Unix.Unix_error _ | Failure _ -> None)

(* a path as the client gives it back: through a URI, which normalizes it (on
   Windows the drive letter is lowercased, C:\ is c:\) *)
let normalize path = Lsp.Types.DocumentUri.(to_path (of_path path))

(* a file of the library opened by the editor: in one of the directories of
   the libraries (also of an earlier server, e.g. when the editor reopens it),
   whatever the instance that wrote it *)
let is_library_path path =
  let dir = Filename.dirname path in
  let name = Filename.basename dir in
  let prefix = prefix () in
  String.length name > String.length prefix
  && String.equal (String.sub name 0 (String.length prefix)) prefix
  && (try String.equal (normalize (Filename.dirname dir)) (normalize (base ())) with Failure _ -> false)
