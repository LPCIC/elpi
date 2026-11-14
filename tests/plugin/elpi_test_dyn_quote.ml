(* a plugin that installs the default quotation: the plugin of findlib
   package elpi-test-dyn.quote, to be loaded before Setup.init (preload):
   {{ t }} is the Elpi term t *)
open Elpi.API

let () =
  Quotation.set_default_quotation (fun ~language:_ state loc text ->
    Quotation.elpi ~language:Quotation.elpi_language state loc text);
  ignore @@ Plugin.register ~name:"elpi-test-dyn.quote" []
