(* elpi -check-package PKG, built in the package elpi-json: under
   -p elpi-json the executable elpi (package elpi) is not part of the build.
   One line per item, as elpi prints them; exit code 1 if an item failed *)
let () =
  let pkg = Sys.argv.(1) in
  let failed = ref false in
  Elpi_dynload.check_package ~pkg |> List.iter (fun (item, result) ->
    match result with
    | Elpi_dynload.Checked what -> Printf.printf "%s  %s\n" item what
    | Elpi_dynload.Failed errors ->
        failed := true;
        Printf.printf "%s  %s\n" item (String.concat "\n  " errors));
  exit (if !failed then 1 else 0)
