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

include "binding/names.ma".

(* permutations *)
definition finite_perm : ∀X:Nset.(X → X) → Prop ≝ 
 λX,f.injective X X f ∧ surjective X X f ∧ ∃l.∀x.x ∉ l → f x = x.

(* maps a permutation to a list of parameters *)
definition Pi_list : ∀X:Nset.(X → X) → list X → list X ≝ 
 λX,p,xl.map ?? (λx.p x) xl.

interpretation "permutation of X list" 'middot p x = (Pi_list p x).

definition swap : ∀N:Nset.N → N → N → N ≝
  λN,u,v,x.match (x == u) with
    [true ⇒ v
    |false ⇒ match (x == v) with
       [true ⇒ u
       |false ⇒ x]].
       
axiom swap_right : ∀N,x,y.swap N x y y = x.
(*
#N x y;nnormalize;nrewrite > (p_eqb3 ? y y …);//;
nlapply (refl ? (y ≟ x));ncases (y ≟ x) in ⊢ (???% → %);nnormalize;//;
#H1;napply p_eqb1;//;
nqed.
*)

axiom swap_left : ∀N,x,y.swap N x y x = y.
(*
#N x y;nnormalize;nrewrite > (p_eqb3 ? x x …);//;
nqed.
*)

axiom swap_other : ∀N,x,y,z.x ≠ z → y ≠ z → swap N x y z = z.
(*
#N x y z H1 H2;nnormalize;nrewrite > (p_eqb4 …);
##[nrewrite > (p_eqb4 …);//;@;ncases H2;/2/;
##|@;ncases H1;/2/
##]
nqed.
*)

axiom swap_inv : ∀N,x,y,z.swap N x y (swap N x y z) = z.
(*
#N x y z;nlapply (refl ? (x ≟ z));ncases (x ≟ z) in ⊢ (???% → ?);#H1
##[nrewrite > (p_eqb1 … H1);nrewrite > (swap_left …);//;
##|nlapply (refl ? (y ≟ z));ncases (y ≟ z) in ⊢ (???% → ?);#H2
   ##[nrewrite > (p_eqb1 … H2);nrewrite > (swap_right …);//;
   ##|nrewrite > (swap_other …) in ⊢ (??(????%)?);/2/;
      nrewrite > (swap_other …);/2/;
   ##]
##]
nqed.
*)

axiom swap_fp : ∀N,x1,x2.finite_perm ? (swap N x1 x2).
(*
#N x1 x2;@
##[@
   ##[nwhd;#xa xb;nnormalize;nlapply (refl ? (xa ≟ x1));
      ncases (xa ≟ x1) in ⊢ (???% → %);#H1
      ##[nrewrite > (p_eqb1 … H1);nlapply (refl ? (xb ≟ x1));
         ncases (xb ≟ x1) in ⊢ (???% → %);#H2
         ##[nrewrite > (p_eqb1 … H2);//
         ##|nlapply (refl ? (xb ≟ x2));
            ncases (xb ≟ x2) in ⊢ (???% → %);#H3
            ##[nnormalize;#H4;nrewrite > H4 in H3;
               #H3;nrewrite > H3 in H2;#H2;ndestruct (H2)
            ##|nnormalize;#H4;nrewrite > H4 in H3;
               nrewrite > (p_eqb3 …);//;#H5;ndestruct (H5)
            ##]
         ##]
      ##|nlapply (refl ? (xa ≟ x2));
         ncases (xa ≟ x2) in ⊢ (???% → %);#H2
         ##[nrewrite > (p_eqb1 … H2);nlapply (refl ? (xb ≟ x1));
            ncases (xb ≟ x1) in ⊢ (???% → %);#H3
            ##[nnormalize;#H4;nrewrite > H4 in H3;
               #H3;nrewrite > (p_eqb1 … H3);@
            ##|nnormalize;nlapply (refl ? (xb ≟ x2));
               ncases (xb ≟ x2) in ⊢ (???% → %);#H4
               ##[nrewrite > (p_eqb1 … H4);//
               ##|nnormalize;#H5;nrewrite > H5 in H3;
                  nrewrite > (p_eqb3 …);//;#H6;ndestruct (H6);
               ##]
            ##]
         ##|nnormalize;nlapply (refl ? (xb ≟ x1));
            ncases (xb ≟ x1) in ⊢ (???% → %);#H3
            ##[nnormalize;#H4;nrewrite > H4 in H2;nrewrite > (p_eqb3 …);//;
               #H5;ndestruct (H5)
            ##|nlapply (refl ? (xb ≟ x2));
               ncases (xb ≟ x2) in ⊢ (???% → %);#H4
               ##[nnormalize;#H5;nrewrite > H5 in H1;nrewrite > (p_eqb3 …);//;
                  #H6;ndestruct (H6)
               ##|nnormalize;//
               ##]
            ##]
         ##]
      ##]
   ##|nwhd;#z;nnormalize;nlapply (refl ? (z ≟ x1));
      ncases (z ≟ x1) in ⊢ (???% → %);#H1
      ##[nlapply (refl ? (z ≟ x2));
         ncases (z ≟ x2) in ⊢ (???% → %);#H2
         ##[@ z;nrewrite > H1;nrewrite > H2;napply p_eqb1;//
         ##|@ x2;nrewrite > (p_eqb4 …);
            ##[nrewrite > (p_eqb3 …);//;
               nnormalize;napply p_eqb1;//
            ##|nrewrite < (p_eqb1 … H1);@;#H3;nrewrite > H3 in H2;
               nrewrite > (p_eqb3 …);//;#H2;ndestruct (H2)
            ##]
         ##]
      ##|nlapply (refl ? (z ≟ x2));
         ncases (z ≟ x2) in ⊢ (???% → %);#H2
         ##[@ x1;nrewrite > (p_eqb3 …);//;
            napply p_eqb1;nnormalize;//
         ##|@ z;nrewrite > H1;nrewrite > H2;@;
         ##]
      ##]
   ##]
##|@ [x1;x2];#x0 H1;nrewrite > (swap_other …)
   ##[@
   ##|@;#H2;nrewrite > H2 in H1;*;#H3;napply H3;/2/;
   ##|@;#H2;nrewrite > H2 in H1;*;#H3;napply H3;//;
   ##]
##]
nqed.
*)

axiom inj_swap : ∀N,u,v.injective ?? (swap N u v).
(*
#N u v;ncases (swap_fp N u v);*;#H1 H2 H3;//;
nqed.
*)

axiom surj_swap : ∀N,u,v.surjective ?? (swap N u v).
(*
#N u v;ncases (swap_fp N u v);*;#H1 H2 H3;//;
nqed.
*)

axiom finite_swap : ∀N,u,v.∃l.∀x.x ∉ l → swap N u v x = x.
(*
#N u v;ncases (swap_fp N u v);*;#H1 H2 H3;//;
nqed.
*)

(* swaps two lists of parameters 
definition Pi_swap_list : ∀xl,xl':list X.X → X ≝ 
 λxl,xl',x.foldr2 ??? (λu,v,r.swap ? u v r) x xl xl'.

nlemma fp_swap_list : 
  ∀xl,xl'.finite_perm ? (Pi_swap_list xl xl').
#xl xl';@
##[@;
   ##[ngeneralize in match xl';nelim xl
      ##[nnormalize;//;
      ##|#x0 xl0;#IH xl'';nelim xl''
         ##[nnormalize;//
         ##|#x1 xl1 IH1 y0 y1;nchange in ⊢ (??%% → ?) with (swap ????);
            #H1;nlapply (inj_swap … H1);#H2;
            nlapply (IH … H2);//
         ##]
      ##]
   ##|ngeneralize in match xl';nelim xl
      ##[nnormalize;#_;#z;@z;@
      ##|#x' xl0 IH xl'';nelim xl''
         ##[nnormalize;#z;@z;@
         ##|#x1 xl1 IH1 z;
            nchange in ⊢ (??(λ_.???%)) with (swap ????);
            ncases (surj_swap X x' x1 z);#x2 H1;
            ncases (IH xl1 x2);#x3 H2;@ x3;
            nrewrite < H2;napply H1
         ##]
      ##]
   ##]
##|ngeneralize in match xl';nelim xl
   ##[#;@ [];#;@
   ##|#x0 xl0 IH xl'';ncases xl''
      ##[@ [];#;@
      ##|#x1 xl1;ncases (IH xl1);#xl2 H1;
         ncases (finite_swap X x0 x1);#xl3 H2;
         @ (xl2@xl3);#x2 H3;
         nchange in ⊢ (??%?) with (swap ????);
         nrewrite > (H1 …);
         ##[nrewrite > (H2 …);//;@;#H4;ncases H3;#H5;napply H5;
            napply in_list_to_in_list_append_r;//
         ##|@;#H4;ncases H3;#H5;napply H5;
            napply in_list_to_in_list_append_l;//
         ##]
      ##]
   ##]
##]
nqed.

(* the 'reverse' swap of lists of parameters 
   composing Pi_swap_list and Pi_swap_list_r yields the identity function
   (see the Pi_swap_list_inv lemma) *)
ndefinition Pi_swap_list_r : ∀xl,xl':list X. Pi ≝ 
 λxl,xl',x.foldl2 ??? (λr,u,v.swap ? u v r ) x xl xl'.

nlemma fp_swap_list_r : 
  ∀xl,xl'.finite_perm ? (Pi_swap_list_r xl xl').
#xl xl';@
##[@;
   ##[ngeneralize in match xl';nelim xl
      ##[nnormalize;//;
      ##|#x0 xl0;#IH xl'';nelim xl''
         ##[nnormalize;//
         ##|#x1 xl1 IH1 y0 y1;nwhd in ⊢ (??%% → ?);
            #H1;nlapply (IH … H1);#H2;
            napply (inj_swap … H2);
         ##]
      ##]
   ##|ngeneralize in match xl';nelim xl
      ##[nnormalize;#_;#z;@z;@
      ##|#x' xl0 IH xl'';nelim xl''
         ##[nnormalize;#z;@z;@
         ##|#x1 xl1 IH1 z;nwhd in ⊢ (??(λ_.???%));
            ncases (IH xl1 z);#x2 H1;
            ncases (surj_swap X x' x1 x2);#x3 H2;
            @ x3;nrewrite < H2;napply H1;
         ##]
      ##]
   ##]
##|ngeneralize in match xl';nelim xl
   ##[#;@ [];#;@
   ##|#x0 xl0 IH xl'';ncases xl''
      ##[@ [];#;@
      ##|#x1 xl1;
         ncases (IH xl1);#xl2 H1;
         ncases (finite_swap X x0 x1);#xl3 H2;
         @ (xl2@xl3);#x2 H3;nwhd in ⊢ (??%?);
         nrewrite > (H2 …);
         ##[nrewrite > (H1 …);//;@;#H4;ncases H3;#H5;napply H5;
            napply in_list_to_in_list_append_l;//
         ##|@;#H4;ncases H3;#H5;napply H5;
            napply in_list_to_in_list_append_r;//
         ##]
      ##]
   ##]
##]
nqed.

nlemma Pi_swap_list_inv :
 ∀xl1,xl2,x.
 Pi_swap_list xl1 xl2 (Pi_swap_list_r xl1 xl2 x) = x.
#xl;nelim xl
##[#;@
##|#x1 xl1 IH xl';ncases xl'
   ##[#;@
   ##|#x2 xl2;#x;
      nchange in ⊢ (??%?) with 
        (swap ??? (Pi_swap_list ?? 
                  (Pi_swap_list_r ?? (swap ????))));
      nrewrite > (IH xl2 ?);napply swap_inv;
   ##]
##]
nqed.

nlemma Pi_swap_list_fresh :
  ∀x,xl1,xl2.x ∉ xl1 → x ∉ xl2 → Pi_swap_list xl1 xl2 x = x.
#x xl1;nelim xl1
##[#;@
##|#x3 xl3 IH xl2' H1;ncases xl2'
   ##[#;@
   ##|#x4 xl4 H2;ncut (x ∉ xl3 ∧ x ∉ xl4);
      ##[@
         ##[@;#H3;ncases H1;#H4;napply H4;/2/;
         ##|@;#H3;ncases H2;#H4;napply H4;/2/
         ##]
      ##] *; #H1' H2';
      nchange in ⊢ (??%?) with (swap ????);
      nrewrite > (swap_other …)
      ##[napply IH;//;
      ##|nchange in ⊢ (?(???%)) with (Pi_swap_list ???);
         nrewrite > (IH …);//;@;#H3;ncases H2;#H4;napply H4;//;
      ##|nchange in ⊢ (?(???%)) with (Pi_swap_list ???);
         nrewrite > (IH …);//;@;#H3;ncases H1;#H4;napply H4;//
      ##]
   ##]
##]
nqed.
*)