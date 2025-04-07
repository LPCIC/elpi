open Elpi_util.Union_find

module M = Make (Elpi_util.Util.Int)

open M

let _ =
  (* From https://fr.wikipedia.org/wiki/Union-find#/media/Fichier:Dsu_disjoint_sets_final.svg *)
  let uf = ref empty in
  let update uf (_,act) = uf := act in
  let union uf a b = update uf (union !uf a ~canon:b) in

  (* Partition avec 4 classes disjointes obtenue après
     Union(1, 2), Union(3, 4), Union(2, 5), Union(1, 6) et Union(2, 8). *)
  union uf 1 2;
  union uf 3 4;
  union uf 2 5;

  let uf1 = ref !uf in

  union uf 1 6;
  union uf 3 1;
  assert (roots !uf |> M.KeySet.cardinal = 1);
  (* The cloned table is not impacted by the modification in uf *)
  assert (roots !uf1 |> M.KeySet.cardinal = 2);
  union uf1 7 8;
  assert (roots !uf1 |> M.KeySet.cardinal = 3);
  assert (roots !uf |> M.KeySet.cardinal = 1)
