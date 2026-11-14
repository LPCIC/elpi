(* prints the stub of the plugin of a package linked in this executable (its
   documentation), as elpi-json does: e.g. elpi-test-dyn.builtins.elpi *)
let () = Elpi.API.BuiltIn.document_fmt Format.std_formatter (Elpi.API.Plugin.builtins Sys.argv.(1))
