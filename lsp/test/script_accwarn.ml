open Test_lsp_lib

(* a warning in an accumulated file is shown in that file, not in the
   document; when the file is open it shows its own diagnostics, and when the
   document is closed the warning goes away *)
let () = register ~name:"accwarn" "accwarn.elpi" (fun file ->
  let lib = "accwarn_lib.elpi" in
  open_file file;
  await_diagnostics [ lib ];
  open_file lib;
  close_file lib;
  await_diagnostics [ file; lib ];
  close_file file;
  await_diagnostics [ lib ])
