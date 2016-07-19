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

(* $Id: matitaInit.ml 12494 2013-02-04 17:38:31Z sacerdot $ *)

type thingsToInitialize = 
  ConfigurationFile | Db | Environment | Getter | CmdLine | Registry
  
exception FailedToInitialize of thingsToInitialize

let wants s l = 
  List.iter (
    fun item -> 
      if not (List.exists (fun x -> x = item) l) then
        raise (FailedToInitialize item)) 
  s

let already_configured s l =
  List.for_all (fun item -> List.exists (fun x -> x = item) l) s
  
let conffile = ref BuildTimeConf.matita_conf

let registry_defaults = [
  "matita.debug",                "false";
  "matita.debug_menu",           "false";
  "matita.external_editor",      "gvim -f -c 'go %p' %f";
  "matita.profile",              "true";
  "matita.system",               "false";
  "matita.verbose",              "false";
  "matita.paste_unicode_as_tex", "false";
  "matita.noinnertypes",         "false";
  "matita.do_heavy_checks",      "true";
  "matita.moo",                  "true";
  "matita.extract",              "false";
  "matita.execcomments",         "false";
]

let set_registry_values =
  List.iter 
    (fun key, value -> 
       if not (Helm_registry.has key) then Helm_registry.set ~key ~value)

let fill_registry init_status =
  if not (already_configured [ Registry ] init_status) then begin
    set_registry_values registry_defaults;
    Registry :: init_status
  end else
    init_status

let load_configuration init_status =
  if not (already_configured [ConfigurationFile] init_status) then
    begin
      Helm_registry.load_from !conffile;
      if not (Helm_registry.has "user.name") then begin
        let login = (Unix.getpwuid (Unix.getuid ())).Unix.pw_name in
        Helm_registry.set "user.name" login
      end;
      let home = Helm_registry.get_string "matita.basedir" in
      let user_conf_file = home ^ "/matita.conf.xml" in
      if HExtlib.is_regular user_conf_file then
        begin
          HLog.message ("Loading additional conf file from " ^ user_conf_file);
          try
            Helm_registry.load_from user_conf_file
          with exn -> 
            HLog.error
              ("While loading conf file: " ^ snd (MatitaExcPp.to_string exn))
        end;
      ConfigurationFile::init_status 
    end
  else
    init_status

let initialize_db init_status = 
  wants [ ConfigurationFile; CmdLine ] init_status;
  if not (already_configured [ Db ] init_status) then
    begin
      Db::init_status
    end
  else
    init_status

let initialize_environment init_status = 
  wants [CmdLine] init_status;
  if not (already_configured [Getter;Environment] init_status) then
    begin
      Http_getter.init ();
      if Helm_registry.get_bool "matita.system" then
        Http_getter_storage.activate_system_mode ();
      Getter::Environment::init_status
    end
  else
    init_status 
  
let status = ref []

let usages = Hashtbl.create 11 (** app name (e.g. "matitac") -> usage string *)
let _ =
  List.iter
    (fun (name, s) -> Hashtbl.replace usages name s)
    [ "matitac", 
        Printf.sprintf "Matita batch compiler v%s
Usage: matitac [ OPTION ... ] FILE
Options:"
          BuildTimeConf.version;
        "matitaprover",
        Printf.sprintf "Matita (TPTP) prover v%s
Usage: matitaprover [ -tptppath ] FILE.p
Options:"
          BuildTimeConf.version;
      "matita",
        Printf.sprintf "Matita interactive theorem prover v%s
Usage: matita [ OPTION ... ] [ FILE ]
Options:"
          BuildTimeConf.version;
      "matitadep",
        Printf.sprintf "Matita depency file generator v%s
Usage: matitadep [ OPTION ... ] 
Options:"
          BuildTimeConf.version;
      "matitaclean",
        Printf.sprintf "MatitaClean v%s
Usage: matitaclean all
       matitaclean ( FILE | URI )
Options:"
          BuildTimeConf.version;
    ]
let default_usage =
  Printf.sprintf 
    "Matita v%s\nUsage: matita [ ARG ]\nOptions:" BuildTimeConf.version

let usage () =
  let basename = Filename.basename Sys.argv.(0) in
  let usage_key =
    try Filename.chop_extension basename with Invalid_argument  _ -> basename
  in
  try Hashtbl.find usages usage_key with Not_found -> default_usage
;;

let extra_cmdline_specs = ref []
let add_cmdline_spec l = extra_cmdline_specs := l @ !extra_cmdline_specs

let parse_cmdline init_status =
  if not (already_configured [CmdLine] init_status) then begin
    wants [Registry] init_status;
    let includes = ref [] in
    let default_includes = [ 
      BuildTimeConf.new_stdlib_dir_devel;
    (* CSC: no installed standard library!
      BuildTimeConf.new_stdlib_dir_installed ; *)
    ] 
    in
    let absolutize s =
      if Pcre.pmatch ~pat:"^/" s then s else Sys.getcwd () ^"/"^s
    in
    let args = ref [] in
    let add_l l = fun s -> l := s :: !l in
    let print_version () =
            Printf.printf "%s\n" BuildTimeConf.version;exit 0 in
    let no_innertypes () =
      Helm_registry.set_bool "matita.noinnertypes" true in
    let set_baseuri s =
      match Str.split (Str.regexp "::") s with
      | [path; uri] -> Helm_registry.set "matita.baseuri"
          (HExtlib.normalize_path (absolutize path)^" "^uri)
      | _ -> raise (Failure "bad baseuri, use -b 'path::uri'")
    in
    let no_default_includes = ref false in
    let execcomments = ref false in
    let arg_spec =
      let std_arg_spec = [
        "-b", Arg.String set_baseuri, "<path::uri> forces the baseuri of path";
        "-I", Arg.String (add_l includes),
          ("<path> Adds path to the list of searched paths for the "
           ^ "include command");
        "-conffile", Arg.Set_string conffile,
          (Printf.sprintf ("<filename> Read configuration from filename"
             ^^ "\n    Default: %s")
            BuildTimeConf.matita_conf);
        "-extract_ocaml", 
          Arg.Unit (fun () -> Helm_registry.set_bool "extract_ocaml" true),
          "Extract ocaml code";
        "-force",
            Arg.Unit (fun () -> Helm_registry.set_bool "matita.force" true),
            ("Force actions that would not be executed per default");
        "-noprofile", 
          Arg.Unit (fun () -> Helm_registry.set_bool "matita.profile" false),
          "Turns off profiling printings";
        "-noinnertypes", Arg.Unit no_innertypes, 
          "Turns off inner types generation while publishing";
        "-profile-only",
          Arg.String (fun rex -> Helm_registry.set "matita.profile_only" rex),
          "Activates only profiler with label matching the provided regex";
        "-system", Arg.Unit (fun () ->
              Helm_registry.set_bool "matita.system" true),
            ("Act on the system library instead of the user one"
             ^ "\n    WARNING: not for the casual user");
        "-no-default-includes", Arg.Set no_default_includes,
          "Do not include the default searched paths for the include command"; 
        "-execcomments", Arg.Set execcomments,
          "Execute the content of (** ... *) comments";
	"-v", 
          Arg.Unit (fun () -> Helm_registry.set_bool "matita.verbose" true), 
          "Verbose mode";
        "--version", Arg.Unit print_version, "Prints version"
      ] in
      let debug_arg_spec =
        if BuildTimeConf.debug then
          [ "-debug",
            Arg.Unit (fun () -> Helm_registry.set_bool "matita.debug" true),
              ("Do not catch top-level exception "
              ^ "(useful for backtrace inspection)");
	    "-onepass",
	    Arg.Unit (fun () -> MultiPassDisambiguator.only_one_pass := true),
	    "Enable only one disambiguation pass";    
          ]
        else []
      in
      std_arg_spec @ debug_arg_spec @ !extra_cmdline_specs
    in
    let set_list ~key l =
      Helm_registry.set_list Helm_registry.of_string ~key ~value:l
    in
    Arg.parse arg_spec (add_l args) (usage ());
    Helm_registry.set_bool ~key:"matita.execcomments" ~value:!execcomments;
    let default_includes = if !no_default_includes then [] else default_includes in
    let includes = 
      List.map (fun x -> HExtlib.normalize_path (absolutize x)) 
       ((List.rev !includes) @ default_includes) 
    in
    set_list ~key:"matita.includes" includes;
    let args = List.rev (List.filter (fun x -> x <> "") !args) in
    set_list ~key:"matita.args" args;
    HExtlib.set_profiling_printings 
      (fun s -> 
        Helm_registry.get_bool "matita.profile" && 
        Pcre.pmatch 
          ~pat:(Helm_registry.get_opt_default 
                  Helm_registry.string ~default:".*" "matita.profile_only") 
          s);
    CmdLine :: init_status
  end else
    init_status

let die_usage () =
  print_endline (usage ());
  exit 1

let conf_components = 
  [ load_configuration; fill_registry; parse_cmdline]

let other_components =
  [ initialize_db; initialize_environment ]

let initialize_all () =
  status := 
    List.fold_left (fun s f -> f s) !status
    (conf_components @ other_components);
  NCicLibrary.init ()

let parse_cmdline_and_configuration_file () =
  status := List.fold_left (fun s f -> f s) !status conf_components

let initialize_environment () =
  status := initialize_environment !status
