(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "formal_topology/basic_pairs_to_o-basic_pairs.ma".
include "formal_topology/apply_functor.ma".
(*
definition rOBP ≝ Apply (category2_of_category1 BP) OBP BP_to_OBP.

include "formal_topology/o-basic_pairs_to_o-basic_topologies.ma".

lemma category2_of_category1_respects_comp_r:
 ∀C:category1.∀o1,o2,o3:C.
  ∀f:arrows1 ? o1 o2.∀g:arrows1 ? o2 o3.
   (comp1 ???? f g) =_\ID (comp2 (category2_of_category1 C) o1 o2 o3 f g).
 intros; constructor 1; 
qed.

lemma category2_of_category1_respects_comp:
 ∀C:category1.∀o1,o2,o3:C.
  ∀f:arrows1 ? o1 o2.∀g:arrows1 ? o2 o3.
   (comp2 (category2_of_category1 C) o1 o2 o3 f g) =_\ID (comp1 ???? f g).
 intros; constructor 1; 
qed.

lemma POW_full': 
  ∀S,T:REL.∀f:arrows2 SET1 (POW S) (POW T).
   arrows1 REL S T.
 intros;
 constructor 1; constructor 1;
  [ intros (x y); apply (y ∈ c {(x)});
  | apply hide; intros; unfold FunClass_1_OF_Ocontinuous_relation;
    apply (e1‡††e); ]
qed.

(*
lemma POW_full_image: 
  ∀S,T:REL.∀f:arrows2 SET1 (POW S) (POW T).
   exT22 ? (λg:arrows1 REL S T.or_f ?? (map_arrows2 ?? POW S T g) = f).
 intros; letin g ≝ (? : carr1 (arrows1 REL S T)); [
 constructor 1; constructor 1;
  [ intros (x y); apply (y ∈ f {(x)});
  | apply hide; intros; unfold FunClass_1_OF_Ocontinuous_relation;
    apply (e1‡††e); ]]
exists [apply g]
intro; split; intro; simplify; intro; 
[ whd in f1; change in f1:(? ? (λ_:?.? ? ? ? ? % ?)) with (a1 ∈ f {(x)});
  cases f1; cases x; clear f1 x; change with (a1 ∈ f a);
  lapply (f_image_monotone ?? (map_arrows2 ?? POW S T g) (singleton ? w) a ? a1);
  [2: whd in Hletin;
      change in Hletin:(? ? (λ_:?.? ? ? ? ? % ?))
      with (a1 ∈ f {(x)}); cases Hletin; cases x;
           [ intros 2; change in f3 with (eq1 ? w a2); change with (a2 ∈ a);
             apply (. f3^-1‡#); assumption;
           | assumption; ]
           
           
           
  lapply (. (or_prop3 ?? (map_arrows2 ?? POW S T g) (singleton ? a1) a)^-1);
   [ whd in Hletin:(? ? ? ? ? ? %);
     change in Hletin:(? ? ? ? ? ? (? ? (? ? ? (λ_:?.? ? (λ_:?.? ? ? ? ? % ?)) ?)))
     with (y ∈ f {(x)});
     cases Hletin; cases x1; cases x2; 
  
   [ cases Hletin; change in x with (eq1 ? a1 w1); apply (. x‡#); assumption;
   | exists; [apply w] assumption ]


  clear g;
 cases f1; cases x; simplify in f2; change with (a1 ∈ (f a));
  lapply depth=0 (let x ≝ POW in or_prop3 (POW S) (POW T) (map_arrows2 ?? POW S T g));
  lapply (Hletin {(w)} {(a1)}).
  lapply (if ?? Hletin1); [2: clear Hletin Hletin1;
    exists; [apply a1] [whd; exists[apply w] split; [assumption;|change with (w = w); apply rule #]]
    change with (a1=a1); apply rule #;]
  clear Hletin Hletin1; cases Hletin2; whd in x2; 
qed.
*)
lemma curry: ∀A,B,C.(A × B ⇒_1 C) → A → (B ⇒_1 C).
 intros;
 constructor 1;
  [ apply (b c);
  | intros; apply (#‡e); ]
qed.

notation < "F x" left associative with precedence 65 for @{'map_arrows $F $x}.
interpretation "map arrows 2" 'map_arrows F x = (fun12 ? ? (map_arrows2 ? ? F ? ?) x).

definition preserve_sup : ∀S,T.∀ f:Ω^S ⇒_1 Ω^T. CProp[1].
intros (S T f); apply (∀X:Ω \sup S. (f X) =_1 ?);
constructor 1; constructor 1;
[ intro y; alias symbol "singl" = "singleton". alias symbol "and" = "and_morphism".
  apply (∃x:S. x ∈ X ∧ y ∈ f {(x)});
| intros (a b H); split; intro E; cases E; clear E; exists; [1,3:apply w]
  [ apply (. #‡(H^-1‡#)); | apply (. #‡(H‡#));] assumption]
qed.

alias symbol "singl" = "singleton".
lemma eq_cones_to_eq_rel: 
  ∀S,T. ∀f,g: arrows1 REL S T.
   (∀x. curry ??? (image ??) f {(x)} = curry ??? (image ??) g {(x)}) → f = g.
intros; intros 2 (a b); split; intro;
[ cases (f1 a); lapply depth=0 (s b); clear s s1;
  lapply (Hletin); clear Hletin;
   [ cases Hletin1; cases x; change in f4 with (a = w);
     change with (a ♮g b); apply (. f4‡#); assumption;
   | exists; [apply a] split; [ assumption | change with (a=a); apply rule #;]]
| cases (f1 a); lapply depth=0 (s1 b); clear s s1;
  lapply (Hletin); clear Hletin;
   [ cases Hletin1; cases x; change in f4 with (a = w);
     change with (a ♮f b); apply (. f4‡#); assumption;
   | exists; [apply a] split; [ assumption | change with (a=a); apply rule #;]]]
qed.

variant eq_cones_to_eq_rel': 
  ∀S,T. ∀f,g: arrows1 REL S T.
   (∀x:S. or_f ?? (map_arrows2 ?? POW S T f) {(x)} = or_f ?? (map_arrows2 ?? POW S T g) {(x)}) →
    f = g
≝ eq_cones_to_eq_rel.

(*
lemma rOR_full : 
  ∀s,t:rOBP.∀f:arrows2 OBTop (OR (ℱ_2 s)) (OR (ℱ_2 t)).
    exT22 ? (λg:arrows2 rOBP s t.
       map_arrows2 ?? OR ?? (ℳ_2 g) = f). 
intros 2 (s t); cases s (s_2 s_1 s_eq); clear s;
change in match (F2 ??? (mk_Fo ??????)) with s_2;
cases s_eq; clear s_eq s_2;
letin s1 ≝ (BP_to_OBP s_1); change in match (BP_to_OBP s_1) with s1;
cases t (t_2 t_1 t_eq); clear t;
change in match (F2 ??? (mk_Fo ??????)) with t_2;
cases t_eq; clear t_eq t_2;
letin t1 ≝ (BP_to_OBP t_1); change in match (BP_to_OBP t_1) with t1;
whd in ⊢ (%→?); whd in ⊢ (? (? ? ? ? %) (? ? ? ? %)→?);
intro; whd in s_1 t_1; 
letin R ≝ (? : (carr2 (arrows2 (category2_of_category1 BP) s_1 t_1))); 
[2:
  exists;
    [ constructor 1;
       [2: simplify; apply R;
       | simplify; apply (fun12 ?? (map_arrows2 ?? BP_to_OBP s_1 t_1)); apply R;
       | simplify; apply rule #; ]]
   simplify;
|1: constructor 1;   
    [2: apply (pi1exT22 ?? (POW_full (form s_1) (form t_1) f));
    |1: letin u ≝ (or_f_star ?? (map_arrows2 ?? POW (concr t_1) (form t_1) (⊩ \sub t_1)));
        letin r ≝ (u ∘ (or_f ?? f));
        letin xxx ≝ (or_f ?? (map_arrows2 ?? POW (concr s_1) (form s_1) (⊩ \sub s_1)));
        letin r' ≝ (r ∘ xxx); clearbody r';
        apply (POW_full' (concr s_1) (concr t_1) r');    
    | simplify in ⊢ (? ? ? (? ? ? ? ? % ?) ?);
      apply eq_cones_to_eq_rel'; intro;
      apply
       (cic:/matita/logic/equality/eq_elim_r''.con ?????
         (category2_of_category1_respects_comp_r : ?));
      apply rule (.= (#‡#));
      apply (.= (respects_comp2 ?? POW (concr s_1) (concr t_1) (form t_1) ? (⊩\sub t_1))‡#); 
      apply sym2;
      apply (.= (respects_comp2 ?? POW (concr s_1) (form s_1) (form t_1) (⊩\sub s_1) (pi1exT22 ?? (POW_full (form s_1) (form t_1) (Ocont_rel ?? f)))));
      apply (let H ≝(\snd (POW_full (form s_1) (form t_1) (Ocont_rel ?? f))) in .= #‡H);
      apply sym2;      
 ]

STOP;
 

(* Todo: rename BTop → OBTop *)

(* scrivo gli statement qua cosi' verra' un conflitto :-)

1. definire il funtore OR
2. dimostrare che ORel e' faithful

3. Definire la funzione
    Apply:
    ∀C1,C2: CAT2.  F: arrows3 CAT2 C1 C2 → CAT2
    ≝ 
     constructor 1;
      [ gli oggetti sono gli oggetti di C1 mappati da F
      | i morfismi i morfismi di C1 mappati da F
      | ....
      ]
   
   E : objs CATS === Σx.∃y. F y = x
  
   Quindi (Apply C1 C2 F) (che usando da ora in avanti una coercion
   scrivero' (F C1) ) e' l'immagine di C1 tramite F ed e'
   una sottocategoria di C2 (qualcosa da dimostare qui??? vedi sotto
   al punto 5)

4. Definire rOBP (le OBP rappresentabili) come (BP_to_OBP BP)
  [Si puo' fare lo stesso per le OA: rOA ≝ Rel_to_OA REL ]

5. Dimostrare che OR (il funtore faithful da OBP a OBTop) e' full
   quando applicato a rOBP.
   Nota: puo' darsi che faccia storie ad accettare lo statement.
   Infatti rOBP e' (BP_to_OBP BP) ed e' "una sottocategoria di OBP"
   e OR va da OBP a OBTop. Non so se tipa subito o se devi dare
   una "proiezione" da rOBP a OBP.

6. Definire rOBTop come (OBP_to_OBTop rOBP).

7. Per composizione si ha un funtore full and faithful da BP a rOBTop:
   basta prendere (OR ∘ BP_to_OBP).

8. Dimostrare (banale: quasi tutti i campi sono per conversione) che
   esiste un funtore da rOBTop a BTop. Dimostrare che tale funtore e'
   faithful e full (banale: tutta conversione).

9. Per composizione si ha un funtore full and faithful da BP a BTop.

10. Dimostrare che i seguenti funtori sono anche isomorphism-dense
    (http://planetmath.org/encyclopedia/DenseFunctor.html):

    BP_to_OBP
    OBP_to_OBTop quando applicato alle rOBP
    OBTop_to_BTop quando applicato alle rOBTop

    Concludere per composizione che anche il funtore da BP a BTop e'
    isomorphism-dense.

====== Da qui in avanti non e' "necessario" nulla:

== altre cose mancanti

11. Dimostrare che le r* e le * orrizzontali
    sono isomorfe dando il funtore da r* a * e dimostrando che componendo i
    due funtori ottengo l'identita'

12. La definizione di r* fa schifo: in pratica dici solo come ottieni
    qualcosa, ma non come lo caratterizzeresti. Ora un teorema carino
    e' che una a* (e.g. una aOBP) e' sempre una rOBP dove "a" sta per
    atomic. Dimostrarlo per tutte le r*.

== categorish/future works

13. definire astrattamente la FG-completion e usare quella per
    ottenere le BP da Rel e le OBP da OA.

14. indebolire le OA, generalizzare le costruzioni, etc. come detto
    con Giovanni

*)

*)
*)
