type symbol = Glib.unichar
type tag = string

let virtual_to_symbol = Hashtbl.create 503;;
let tag_to_data = Hashtbl.create 503;;

let add_virtual names symbol tags =
  List.iter 
    (fun name -> 
       if Hashtbl.mem virtual_to_symbol name then
         HLog.error 
          (Printf.sprintf "name %s already used for virtual %s" name 
          (Glib.Utf8.from_unichar (Hashtbl.find virtual_to_symbol name)))
       else
         Hashtbl.add virtual_to_symbol name symbol) 
       names;     
  List.iter 
    (fun tag -> 
       try 
        let l = Hashtbl.find tag_to_data tag in
        let l = (names,symbol) :: l in
        Hashtbl.replace tag_to_data tag l
       with Not_found ->
        Hashtbl.add tag_to_data tag [names,symbol]) 
    tags;
;;

let get_all_virtuals () =
  let l = ref [] in
  Hashtbl.iter 
    (fun k v -> l := (k,v) :: !l;)
    tag_to_data;
  !l
;;

exception Not_a_virtual

let rec symbol_of_virtual str =
  if str = "" then raise Not_a_virtual
  else  
    try str, Hashtbl.find virtual_to_symbol str
    with Not_found -> 
     symbol_of_virtual (String.sub str 1 (String.length str - 1))
;;

let classes = Hashtbl.create 503;;

let add_eqclass l =
  List.iter (fun x -> 
    assert(not (Hashtbl.mem classes x));
    Hashtbl.add classes x l) l
;;

let similar_symbols symbol = 
  try Hashtbl.find classes symbol 
  with Not_found -> []
;;

let get_all_eqclass () =
  let rc = ref [] in
  Hashtbl.iter 
    (fun k v ->
      if not (List.mem v !rc) then
        rc := v :: !rc)
    classes;
  !rc
;;

