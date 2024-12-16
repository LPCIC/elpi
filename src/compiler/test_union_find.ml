open Elpi_compiler.Union_find

module M = Make (Elpi_util.Util.IntMap)

open M

let _ =
  (* From https://fr.wikipedia.org/wiki/Union-find#/media/Fichier:Dsu_disjoint_sets_final.svg *)
  let uf = ref empty in
  let update uf (_,act) = uf := act in
  let union uf a b = update uf (union !uf a b) in

  (* Partition avec 4 classes disjointes obtenue après
     Union(1, 2), Union(3, 4), Union(2, 5), Union(1, 6) et Union(2, 8). *)
  union uf 1 2;
  union uf 3 4;
  union uf 2 5;

  let uf1 = ref !uf in

  union uf 1 6;
  union uf 3 1;
  assert (roots !uf |> List.length = 1);
  (* The cloned table is not impacted by the modification in uf *)
  assert (roots !uf1 |> List.length = 2);
  union uf1 7 8;
  assert (roots !uf1 |> List.length = 3);
  assert (roots !uf |> List.length = 1)
