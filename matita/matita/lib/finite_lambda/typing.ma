(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "finite_lambda/reduction.ma".


(****************************************************************)

inductive TJ (O: Type[0]) (D:O → FinSet): list (FType O) → T O D → FType O → Prop ≝
  | tval: ∀G,o,a. TJ O D G (Val O D o a) (atom O o)
  | trel: ∀G1,ty,G2,n. length ? G1 = n → TJ O D (G1@ty::G2) (Rel O D n) ty
  | tapp: ∀G,M,N,ty1,ty2. TJ O D G M (arrow O ty1 ty2) → TJ O D G N ty1 →
      TJ O D G (App O D M N) ty2
  | tlambda: ∀G,M,ty1,ty2. TJ O D (ty1::G) M ty2 → 
      TJ O D G (Lambda O D ty1 M) (arrow O ty1 ty2)
  | tvec: ∀G,v,ty1,ty2.
      (|v| = |enum (FinSet_of_FType O D ty1)|) →
      (∀M. mem ? M v → TJ O D G M ty2) →
      TJ O D G (Vec O D ty1 v) (arrow O ty1 ty2).

lemma wt_to_T: ∀O,D,G,ty,a.TJ O D G (to_T O D ty a) ty.
#O #D #G #ty elim ty
  [#o #a normalize @tval
  |#ty1 #ty2 #Hind1 #Hind2 normalize * #v #Hv @tvec
    [<Hv >length_map >length_map //
    |#M elim v 
      [normalize @False_ind |#a #v1 #Hind3 * [#eqM >eqM @Hind2 |@Hind3]]
    ]
  ]
qed.

lemma inv_rel: ∀O,D,G,n,ty.
  TJ O D G (Rel O D n) ty → ∃G1,G2.|G1|=n∧G=G1@ty::G2.
#O #D #G #n #ty #Hrel inversion Hrel
  [#G1 #o #a #_ #H destruct 
  |#G1 #ty1 #G2 #n1 #H1 #H2 #H3 #H4 destruct %{G1} %{G2} /2/ 
  |#G1 #M0 #N #ty1 #ty2 #_ #_ #_ #_ #_ #H destruct
  |#G1 #M0 #ty4 #ty5 #HM0 #_ #_ #H #H1 destruct 
  |#G1 #v #ty3 #ty4 #_ #_ #_ #_ #H destruct 
  ]
qed.
      
lemma inv_tlambda: ∀O,D,G,M,ty1,ty2,ty3.
  TJ O D G (Lambda O D ty1 M) (arrow O ty2 ty3) → 
  ty1 = ty2 ∧ TJ O D (ty2::G) M ty3.
#O #D #G #M #ty1 #ty2 #ty3 #Hlam inversion Hlam
  [#G1 #o #a #_ #H destruct 
  |#G1 #ty #G2 #n #_ #_ #H destruct
  |#G1 #M0 #N #ty1 #ty2 #_ #_ #_ #_ #_ #H destruct
  |#G1 #M0 #ty4 #ty5 #HM0 #_ #_ #H #H1 destruct % //
  |#G1 #v #ty3 #ty4 #_ #_ #_ #_ #H destruct 
  ]
qed.

lemma inv_tvec: ∀O,D,G,v,ty1,ty2,ty3.
   TJ O D G (Vec O D ty1 v) (arrow O ty2 ty3) →
  (|v| = |enum (FinSet_of_FType O D ty1)|) ∧
  (∀M. mem ? M v → TJ O D G M ty3).
#O #D #G #v #ty1 #ty2 #ty3 #Hvec inversion Hvec
  [#G #o #a #_ #H destruct 
  |#G1 #ty #G2 #n #_ #_ #H destruct
  |#G1 #M0 #N #ty1 #ty2 #_ #_ #_ #_ #_ #H destruct
  |#G1 #M0 #ty4 #ty5 #HM0 #_ #_ #H #H1 destruct 
  |#G1 #v1 #ty4 #ty5 #Hv #Hmem #_ #_ #H #H1 destruct % // @Hmem 
  ]
qed.

(* could be generalized *)
lemma weak_rel: ∀O,D,G1,G2,ty1,ty2,n. length ? G1 < n → 
   TJ O D (G1@G2) (Rel O D n) ty1 →
   TJ O D (G1@ty2::G2) (Rel O D (S n)) ty1.
#O #D #G1 #G2 #ty1 #ty2 #n #HG1 #Hrel lapply (inv_rel … Hrel)
* #G3 * #G4 * #H1 #H2 lapply (compare_append … H2)
* #G5 *
  [* #H3 @False_ind >H3 in HG1; >length_append >H1 #H4
   @(absurd … H4) @le_to_not_lt //
  |* #H3 #H4 >H4 >append_cons <associative_append @trel
   >length_append >length_append <H1 >H3 >length_append normalize 
   >plus_n_Sm >associative_plus @eq_f //
  ]
qed.

lemma strength_rel: ∀O,D,G1,G2,ty1,ty2,n. length ? G1 < n → 
   TJ O D (G1@ty2::G2) (Rel O D n) ty1 →
   TJ O D (G1@G2) (Rel O D (n-1)) ty1.
#O #D #G1 #G2 #ty1 #ty2 #n #HG1 #Hrel lapply (inv_rel … Hrel)
* #G3 * #G4 * #H1 #H2 lapply (compare_append … H2)
* #G5 *
  [* #H3 @False_ind >H3 in HG1; >length_append >H1 #H4
   @(absurd … H4) @le_to_not_lt //
  |lapply G5 -G5 * 
    [>append_nil normalize * #H3 #H4 destruct @False_ind @(absurd … HG1) 
     @le_to_not_lt //
    |#ty3 #G5 * #H3 normalize #H4 destruct (H4) <associative_append @trel
     <H1 >H3 >length_append >length_append normalize <plus_minus_associative //
    ]
  ]
qed.

lemma no_matter: ∀O,D,G,N,tyN. 
  TJ O D G N tyN →  ∀G1,G2,G3.G=G1@G2 → is_closed O D (|G1|) N →
    TJ O D (G1@G3) N tyN.    
#O #D #G #N #tyN #HN elim HN -HN -tyN -N -G 
  [#G #o #a #G1 #G2 #G3 #_ #_ @tval 
  |#G #ty #G2 #n #HG #G3 #G4 #G5 #H #HNC normalize 
   lapply (is_closed_rel … HNC) #Hlt lapply (compare_append … H) * #G6 *
    [* #H1 @False_ind @(absurd ? Hlt) @le_to_not_lt <HG >H1 >length_append // 
    |* cases G6
      [>append_nil normalize #H1 @False_ind 
       @(absurd ? Hlt) @le_to_not_lt <HG >H1 //
      |#ty1 #G7 #H1 normalize #H2 destruct >associative_append @trel //
      ]
    ]
  |#G #M #N #ty1 #ty2 #HM #HN #HindM #HindN #G1 #G2 #G3 
   #Heq #Hc lapply (is_closed_app … Hc) -Hc * #HMc #HNc  
   @(tapp … (HindM … Heq HMc) (HindN … Heq HNc))
  |#G #M #ty1 #ty2 #HM #HindM #G1 #G2 #G3 #Heq #Hc
   lapply (is_closed_lam … Hc) -Hc #HMc 
   @tlambda @(HindM (ty1::G1) G2) [>Heq // |@HMc]
  |#G #v #ty1 #ty2 #Hlen #Hv #Hind #G1 #G2 #G3 #H1 #Hc @tvec 
    [>length_map // 
    |#M #Hmem @Hind // lapply (is_closed_vec … Hc) #Hvc @Hvc //
    ]
  ]
qed.

lemma nth_spec: ∀A,a,d,l1,l2,n. |l1| = n → nth n A (l1@a::l2) d = a.
#A #a #d #l1 elim l1 normalize
  [#l2 #n #Hn <Hn  //
  |#b #tl #Hind #l2 #m #Hm <Hm normalize @Hind //
  ]
qed.
             
lemma wt_subst_gen: ∀O,D,G,M,tyM. 
  TJ O D G M tyM → 
   ∀G1,G2,N,tyN.G=(G1@tyN::G2) →
    TJ O D G2 N tyN → is_closed O D 0 N →
     TJ O D (G1@G2) (subst O D M (|G1|) N) tyM.
#O #D #G #M #tyM #HM elim HM -HM -tyM -M -G
  [#G #o #a #G1 #G2 #N #tyN #_ #HG #_ normalize @tval
  |#G #ty #G2 #n #Hlen #G21 #G22 #N #tyN #HG #HN #HNc
   normalize cases (true_or_false (leb (|G21|) n))
    [#H >H cases (le_to_or_lt_eq … (leb_true_to_le … H))
      [#ltn >(not_eq_to_eqb_false … (lt_to_not_eq … ltn)) normalize
       lapply (compare_append … HG) * #G3 *
        [* #HG1 #HG2 @(strength_rel … tyN … ltn) <HG @trel @Hlen
        |* #HG >HG in ltn; >length_append #ltn @False_ind 
         @(absurd … ltn) @le_to_not_lt >Hlen //
        ] 
      |#HG21 >(eq_to_eqb_true … HG21) 
       cut (ty = tyN) 
        [<(nth_spec ? ty ty ? G2 … Hlen) >HG @nth_spec @HG21] #Hty >Hty
       normalize <HG21 @(no_matter ????? HN []) //
      ]
    |#H >H normalize lapply (compare_append … HG) * #G3 *
      [* #H1 @False_ind @(absurd ? Hlen) @sym_not_eq @lt_to_not_eq >H1
       >length_append @(lt_to_le_to_lt n (|G21|)) // @not_le_to_lt
       @(leb_false_to_not_le … H) 
      |cases G3 
        [>append_nil * #H1 @False_ind @(absurd ? Hlen) <H1 @sym_not_eq
         @lt_to_not_eq @not_le_to_lt @(leb_false_to_not_le … H)
        |#ty2 #G4 * #H1 normalize #H2 destruct >associative_append @trel //
        ]
      ]    
    ]
  |#G #M #N #ty1 #ty2 #HM #HN #HindM #HindN #G1 #G2 #N0 #tyN0 #eqG
   #HN0 #Hc normalize @(tapp … ty1) 
    [@(HindM … eqG HN0 Hc) |@(HindN … eqG HN0 Hc)]
  |#G #M #ty1 #ty2 #HM #HindM #G1 #G2 #N0 #tyN0 #eqG
   #HN0 #Hc normalize @(tlambda … ty1) @(HindM (ty1::G1) … HN0) // >eqG //
  |#G #v #ty1 #ty2 #Hlen #Hv #Hind #G1 #G2 #N0 #tyN0 #eqG
   #HN0 #Hc normalize @(tvec … ty1) 
    [>length_map @Hlen
    |#M #Hmem lapply (mem_map ????? Hmem) * #a * -Hmem #Hmem #eqM <eqM
     @(Hind … Hmem … eqG HN0 Hc) 
    ]
  ]
qed.

lemma wt_subst: ∀O,D,M,N,G,ty1,ty2. 
  TJ O D (ty1::G) M ty2 → 
  TJ O D G N ty1 → is_closed O D 0 N →
  TJ O D G (subst O D M 0 N) ty2.
#O #D #M #N #G #ty1 #ty2 #HM #HN #Hc @(wt_subst_gen …(ty1::G) … [ ] … HN) //
qed.

lemma subject_reduction: ∀O,D,M,M1,G,ty. 
  TJ O D G M ty → red O D M M1 → TJ O D G M1 ty.
#O #D #M #M1 #G #ty #HM lapply M1 -M1 elim HM  -HM -ty -G -M
  [#G #o #a #M1 #Hval elim (red_val ????? Hval)
  |#G #ty #G1 #n #_ #M1 #Hrel elim (red_rel ???? Hrel) 
  |#G #M #N #ty1 #ty2 #HM #HN #HindM #HindN #M1 #Hred inversion Hred
    [#P #M0 #N0 #Hc #H1 destruct (H1) #HM1 @(wt_subst … HN) //
     @(proj2 … (inv_tlambda … HM))
    |#ty #v #a #M0 #Ha #H1 #H2 destruct @(proj2 … (inv_tvec … HM))
     @(assoc_to_mem … Ha)
    |#M2 #M3 #N0 #Hredl #_ #H1 destruct (H1) #eqM1 @(tapp … HN) @HindM @Hredl
    |#M2 #M3 #N0 #Hredr #_ #H1 destruct (H1) #eqM1 @(tapp … HM) @HindN @Hredr
    |#ty #N0 #N1 #_ #_ #H1 destruct (H1)
    |#ty #M0 #H1 destruct (H1)
    |#ty #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1)
    ]
  |#G #P #ty1 #ty2 #HP #Hind #M1 #Hred lapply(red_lambda ????? Hred) *
    [* #P1 * #HredP #HM1 >HM1 @tlambda @Hind //
    |#HM1 >HM1 @tvec // #N #HN lapply(mem_map ????? HN) 
     * #a * #mema #eqN <eqN -eqN @(wt_subst …HP) // @wt_to_T
    ]
  |#G #v #ty1 #ty2 #Hlen #Hv #Hind #M1 #Hred lapply(red_vec ????? Hred)
   * #N * #N1 * #v1 * #v2 * * #H1 #H2 #H3 >H3 @tvec 
    [<Hlen >H2 >length_append >length_append @eq_f //
    |#M2 #Hmem cases (mem_append ???? Hmem) -Hmem #Hmem
      [@Hv >H2 @mem_append_l1 //
      |cases Hmem 
        [#HM2 >HM2 -HM2 @(Hind N … H1) >H2 @mem_append_l2 %1 //
        |-Hmem #Hmem @Hv >H2 @mem_append_l2 %2 //
        ]
      ]
    ]
  ]
qed.
    
