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

   
axiom canonical_to_T: ∀O,D.∀M:T O D.∀ty.(* type_of M ty → *)
  ∃a:FinSet_of_FType O D ty. star ? (red O D) M (to_T O D ty a).
   
axiom normal_to_T: ∀O,D,M,ty,a. red O D (to_T O D ty a) M → False.

axiom red_closed: ∀O,D,M,M1. 
  is_closed O D 0 M → red O D M M1 → is_closed O D 0 M1.

lemma critical: ∀O,D,ty,M,N. 
  ∃M3:T O D
  .star (T O D) (red O D) (subst O D M 0 N) M3
   ∧star (T O D) (red O D)
    (App O D
     (Vec O D ty
      (map (FinSet_of_FType O D ty) (T O D)
       (λa0:FinSet_of_FType O D ty.subst O D M 0 (to_T O D ty a0))
       (enum (FinSet_of_FType O D ty)))) N) M3.
#O #D #ty #M #N
lapply (canonical_to_T O D N ty) * #a #Ha
%{(subst O D M 0 (to_T O D ty a))} (* CR-term *)
%[@red_star_subst @Ha
 |@trans_star [|@(star_red_appr … Ha)] @R_to_star @riota
  lapply (enum_complete (FinSet_of_FType O D ty) a)
  elim (enum (FinSet_of_FType O D ty))
   [normalize #H1 destruct (H1)
   |#hd #tl #Hind #H cases (orb_true_l … H) -H #Hcase
     [normalize >Hcase >(\P Hcase) //
     |normalize cases (true_or_false (a==hd)) #Hcase1
       [normalize >Hcase1 >(\P Hcase1) // |>Hcase1 @Hind @Hcase]
     ]
   ]
 ]
qed.

lemma critical2: ∀O,D,ty,a,M,M1,M2,v.
  red O D (Vec O D ty v) M →
  red O D (App O D (Vec O D ty v) (to_T O D ty a)) M1 →
  assoc (FinSet_of_FType O D ty) (T O D) a (enum (FinSet_of_FType O D ty)) v
    =Some (T O D) M2 →
  ∃M3:T O D
  .star (T O D) (red O D) M2 M3
   ∧star (T O D) (red O D) (App O D M (to_T O D ty a)) M3.
#O #D #ty #a #M #M1 #M2 #v #redM #redM1 #Ha lapply (red_vec … redM) -redM
* #N * #N1 * #v1 * #v2 * * #Hred1 #Hv #HM0 >HM0 -HM0 >Hv in Ha; #Ha
cases (same_assoc … a (enum (FinSet_of_FType O D ty)) v1 v2 N N1)
  [* >Ha -Ha #H1 destruct (H1) #Ha
   %{N1} (* CR-term *) % [@R_to_star //|@R_to_star @(riota … Ha)]
  |#Ha1 %{M2} (* CR-term *) % [// | @R_to_star @riota <Ha1 @Ha]
  ]
qed.


lemma critical3: ∀O,D,ty,M1,M2. red O D M1 M2 → 
  ∃M3:T O D.star (T O D) (red O D) (Lambda O D ty M2) M3
   ∧star (T O D) (red O D)
    (Vec O D ty
     (map (FinSet_of_FType O D ty) (T O D)
      (λa:FinSet_of_FType O D ty.subst O D M1 0 (to_T O D ty a))
      (enum (FinSet_of_FType O D ty)))) M3.
#O #D #ty #M1 #M2 #Hred
 %{(Vec O D ty
    (map (FinSet_of_FType O D ty) (T O D)
    (λa:FinSet_of_FType O D ty.subst O D M2 0 (to_T O D ty a))
    (enum (FinSet_of_FType O D ty))))} (* CR-term *) %
  [@R_to_star @rmem
  |@star_red_vec2 [>length_map >length_map //] #n #M0
   cases (true_or_false (leb (|enum (FinSet_of_FType O D ty)|) n)) #Hcase
    [>nth_to_default [2:>length_map @(leb_true_to_le … Hcase)]
     >nth_to_default [2:>length_map @(leb_true_to_le … Hcase)] //
    |cut (n < |enum (FinSet_of_FType O D ty)|) 
      [@not_le_to_lt @leb_false_to_not_le @Hcase] #Hlt
     cut (∃a:FinSet_of_FType O D ty.True)
      [lapply Hlt lapply (enum_complete (FinSet_of_FType O D ty))
       cases (enum (FinSet_of_FType O D ty)) 
        [#_ normalize #H @False_ind @(absurd … H) @lt_to_not_le //
        |#a #l #_ #_ %{a} //
        ]
      ] * #a #_
     >(nth_map ?????? a Hlt) >(nth_map ?????? a Hlt) #_
     @red_star_subst2 // 
    ]
  ]
qed.

(* we need to proceed by structural induction on the term and then
by inversion on the two redexes. The problem are the moves in a 
same subterm, since we need an induction hypothesis, there *)

lemma local_confluence: ∀O,D,M,M1,M2. red O D M M1 → red O D M M2 → 
∃M3. star ? (red O D) M1 M3 ∧ star ? (red O D) M2 M3. 
#O #D #M @(T_elim … M)
  [#o #a #M1 #M2 #H elim(red_val ????? H)
  |#n #M1 #M2 #H elim(red_rel ???? H)
  |(* app : this is the interesting case *)
   #P #Q #HindP #HindQ
   #M1 #M2 #H1 inversion H1 -H1
    [(* right redex is beta *)
     #ty #Q #N #Hc #HM >HM -HM #HM1 >HM1 - HM1 #Hl inversion Hl
      [#ty1 #Q1 #N1 #Hc1 #H1 destruct (H1) #H_ 
       %{(subst O D Q1 0 N1)} (* CR-term *) /2/
      |#ty #v #a #M0 #_ #H1 destruct (H1) (* vacuous *)
      |#M0 #M10 #N0 #redM0 #_ #H1 destruct (H1) #_ cases (red_lambda … redM0)
        [* #Q1 * #redQ #HM10 >HM10 
         %{(subst O D Q1 0 N0)} (* CR-term *) %
          [@red_star_subst2 //|@R_to_star @rbeta @Hc]
        |#HM1 >HM1 @critical
        ]
      |#M0 #N0 #N1 #redN0N1 #_ #H1 destruct (H1) #HM2
       %{(subst O D Q 0 N1)} (* CR-term *) 
       %[@red_star_subst @R_to_star //|@R_to_star @rbeta @(red_closed … Hc) //]
      |#ty1 #N0 #N1 #_ #_ #H1 destruct (H1) (* vacuous *)
      |#ty1 #M0 #H1 destruct (H1) (* vacuous *)
      |#ty1 #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1) (* vacuous *)
      ] 
    |(* right redex is iota *)#ty #v #a #M3 #Ha #_ #_ #Hl inversion Hl
      [#P1 #M1 #N1 #_ #H1 destruct (H1) (* vacuous *)
      |#ty1 #v1 #a1 #M4 #Ha1 #H1 destruct (H1) -H1 #HM4 >(inj_to_T … e0) in Ha;
       >Ha1 #H1 destruct (H1) %{M3} (* CR-term *) /2/
      |#M0 #M10 #N0 #redM0 #_ #H1 destruct (H1) #HM2 @(critical2 … redM0 Hl Ha)
      |#M0 #N0 #N1 #redN0N1 #_ #H1 destruct (H1) elim (normal_to_T … redN0N1)
      |#ty1 #N0 #N1 #_ #_ #H1 destruct (H1) (* vacuous *)
      |#ty1 #M0 #H1 destruct (H1) (* vacuous *)
      |#ty1 #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1) (* vacuous *)
      ]
    |(* right redex is appl *)#M3 #M4 #N #redM3M4 #_ #H1 destruct (H1) #_ 
      #Hl inversion Hl
      [#ty1 #M1 #N1 #Hc #H1 destruct (H1) #HM2 lapply (red_lambda … redM3M4) *
        [* #M3 * #H1 #H2 >H2 %{(subst O D M3 0 N1)} %
          [@R_to_star @rbeta @Hc|@red_star_subst2 // ]
        |#H >H -H lapply (critical O D ty1 M1 N1) * #M3 * #H1 #H2 
         %{M3} /2/
        ]
      |#ty1 #v1 #a1 #M4 #Ha1 #H1 #H2 destruct 
       lapply (critical2 … redM3M4 Hl Ha1) * #M3 * #H1 #H2 %{M3} /2/
      |#M0 #M10 #N0 #redM0 #_ #H1 destruct (H1) #HM2 
       lapply (HindP … redM0 redM3M4) * #M3 * #H1 #H2 
       %{(App O D M3 N0)} (* CR-term *) % [@star_red_appl //|@star_red_appl //]
      |#M0 #N0 #N1 #redN0N1 #_ #H1 destruct (H1) #_
       %{(App O D M4 N1)} % @R_to_star [@rappr //|@rappl //]
      |#ty1 #N0 #N1 #_ #_ #H1 destruct (H1) (* vacuous *)
      |#ty1 #M0 #H1 destruct (H1) (* vacuous *)
      |#ty1 #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1) (* vacuous *)
      ]
    |(* right redex is appr *)#M3 #N #N1 #redN #_ #H1 destruct (H1) #_ 
      #Hl inversion Hl
      [#ty1 #M0 #N0 #Hc #H1 destruct (H1) #HM2 
       %{(subst O D M0 0 N1)} (* CR-term *) % 
        [@R_to_star @rbeta @(red_closed … Hc) //|@red_star_subst @R_to_star // ]
      |#ty1 #v1 #a1 #M4 #Ha1 #H1 #H2 destruct (H1) elim (normal_to_T … redN)
      |#M0 #M10 #N0 #redM0 #_ #H1 destruct (H1) #HM2 
       %{(App O D M10 N1)} (* CR-term *) % @R_to_star [@rappl //|@rappr //]
      |#M0 #N0 #N10 #redN0 #_ #H1 destruct (H1) #_
       lapply (HindQ … redN0 redN) * #M3 * #H1 #H2 
       %{(App O D M0 M3)} (* CR-term *) % [@star_red_appr //|@star_red_appr //]
      |#ty1 #N0 #N1 #_ #_ #H1 destruct (H1) (* vacuous *)
      |#ty1 #M0 #H1 destruct (H1) (* vacuous *)
      |#ty1 #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1) (* vacuous *)
      ]
    |(* right redex is rlam *) #ty #N0 #N1 #_ #_ #H1 destruct (H1) (* vacuous *)
    |(* right redex is rmem *) #ty #M0 #H1 destruct (H1) (* vacuous *)
    |(* right redex is vec *) #ty #N #N1 #v #v1 #_ #_ 
     #H1 destruct (H1) (* vacuous *)
    ]
  |#ty #M1 #Hind #M2 #M3 #H1 #H2 (* this case is not trivial any more *)
   lapply (red_lambda … H1) *
    [* #M4 * #H3 #H4 >H4 lapply (red_lambda … H2) *
      [* #M5 * #H5 #H6 >H6 lapply(Hind … H3 H5) * #M6 * #H7 #H8 
       %{(Lambda O D ty M6)} (* CR-term *) % @star_red_lambda //
      |#H5 >H5 @critical3 // 
      ]
    |#HM2 >HM2 lapply (red_lambda … H2) *
      [* #M4 * #Hred #HM3 >HM3 lapply (critical3 … ty ?? Hred) * #M5
       * #H3 #H4 %{M5} (* CR-term *) % //
      |#HM3 >HM3 %{M3} (* CR-term *) % // 
      ]
    ]
  |#ty #v1 #Hind #M1 #M2 #H1 #H2
   lapply (red_vec … H1) * #N11 * #N12 * #v11 * #v12 * * #redN11 #Hv1 #HM1
   lapply (red_vec … H2) * #N21* #N22 * #v21 * #v22 * * #redN21 #Hv2 #HM2
   >Hv1 in Hv2; #Hvv lapply (compare_append … Hvv) -Hvv * 
   (* we must proceed by cases on the list *) * normalize
    [(* N11 = N21 *) *
      [>append_nil * #Hl1 #Hl2 destruct lapply(Hind N11 … redN11 redN21)
        [@mem_append_l2 %1 //]
       * #M3 * #HM31 #HM32
       %{(Vec O D ty (v21@M3::v12))} (* CR-term *) 
       % [@star_red_vec //|@star_red_vec //]
      |>append_nil * #Hl1 #Hl2 destruct lapply(Hind N21 … redN21 redN11)
        [@mem_append_l2 %1 //]
       * #M3 * #HM31 #HM32
       %{(Vec O D ty (v11@M3::v22))} (* CR-term *) 
       % [@star_red_vec //|@star_red_vec //]
      ]
    |(* N11 ≠  N21 *) -Hind #P #l *
      [* #Hv11 #Hv22 destruct
       %{((Vec O D ty ((v21@N22::l)@N12::v12)))} (* CR-term *) % @R_to_star 
        [>associative_append >associative_append normalize @rvec //
        |>append_cons <associative_append <append_cons in ⊢ (???%?); @rvec //
        ]
      |* #Hv11 #Hv22 destruct
       %{((Vec O D ty ((v11@N12::l)@N22::v22)))} (* CR-term *) % @R_to_star 
        [>append_cons <associative_append <append_cons in ⊢ (???%?); @rvec //
        |>associative_append >associative_append normalize @rvec //
        ]
      ]
    ]
  ]
qed.    
      



