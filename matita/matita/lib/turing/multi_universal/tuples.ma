(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)


(****************************** table of tuples *******************************)
include "turing/multi_universal/normalTM.ma".

(* a well formed table is a list of tuples *) 
 
definition table_TM ≝ λn,l,h.flatten ? (tuples_list n h l).

lemma table_TM_cons: ∀n,h,t,o. 
  table_TM n (t::o) h = (tuple_encoding n h t)@(table_TM n o h).
// qed.

lemma initial_bar: ∀n,h,l. l ≠ [ ] →
  table_TM n l h = bar :: tail ? (table_TM n l h).
#n #h * 
  [* #H @False_ind @H // 
  |#a #tl #_ >table_TM_cons lapply (is_tuple n h a) 
   * #qin * #cin * #qout * #cout * #mv * #_ #Htup >Htup %
  ]
qed. 

(************************** matching in a table *******************************)
lemma list_to_table: ∀n,l,h,t. mem ? t l →
  ∃ll,lr.table_TM n l h = ll@(tuple_encoding n h t)@lr.
#n #l #h #t elim l 
  [@False_ind
  |#hd #tl #Hind *
    [#Htup %{[]} %{(table_TM n tl h)} >Htup %
    |#H cases (Hind H) #ll * #lr #H1
     %{((tuple_encoding n h hd)@ll)} %{lr} 
     >associative_append <H1 %
    ]
  ]
qed.

lemma list_to_table1: ∀n,l,h,tup. mem ? tup (tuples_list n h l) →
  ∃ll,lr.table_TM n l h = ll@tup@lr.
#n #l #h #tup elim l 
  [@False_ind
  |#hd #tl #Hind *
    [#Htup %{[]} %{(table_TM n tl h)} >Htup %
    |#H cases (Hind H) #ll * #lr #H1
     %{((tuple_encoding n h hd)@ll)} %{lr} 
     >associative_append <H1 %
    ]
  ]
qed.

definition is_config : nat → list unialpha → Prop ≝  
 λn,t.∃qin,cin.
 only_bits qin ∧ cin ≠ bar ∧ |qin| = S n ∧ t = bar::qin@[cin].

lemma table_to_list: ∀n,l,h,c. is_config n c → 
  ∀ll,lr.table_TM n l h = ll@c@lr → 
    ∃out,lr0,t. lr = out@lr0 ∧ tuple_encoding n h t = (c@out) ∧ mem ? t l.
#n #l #h #c * #qin * #cin * * * #H1 #H2 #H3 #H4  
#ll #lr lapply ll -ll elim l
  [>H4 #ll cases ll normalize [|#hd #tl ] #Habs destruct
  |#t1 #othert #Hind #ll >table_TM_cons #Htuple
   cut (S n < |ll@c@lr|)
     [<Htuple >length_append >(length_of_tuple  … (is_tuple … ))
      /2 by transitive_lt, le_n/] #Hsplit lapply Htuple -Htuple
   cases (is_tuple … n h t1) #q1 * #c1 * #q2 * #c2 * #m 
   * * * * * * * #Hq1 #Hq2 #Hc1 #Hc2 #Hm #Hlen1 #Hlen2 
   whd in ⊢ (???%→?); #Ht1 
   (* if ll is empty we match the first tuple t1, otherwise
      we match inside othert *)
   cases ll
    [>H4 >Ht1 normalize in ⊢ (???%→?); 
     >associative_append whd in ⊢ (??%?→?); #Heq destruct (Heq) -Heq
     >associative_append in e0; #e0
     lapply (append_l1_injective  … e0) [>H3 @Hlen1] #Heq1
     lapply (append_l2_injective  … e0) [>H3 @Hlen1]
     normalize in ⊢ (???%→?); whd in ⊢ (??%?→?); #Htemp 
     lapply (cons_injective_l ????? Htemp) #Hc1
     lapply (cons_injective_r ????? Htemp) -Htemp #Heq2
     %{(q2@[c2;m])} %{(table_TM n othert h)} %{t1} % 
      [ %[ // |>Ht1 >Heq1 >Hc1 @eq_f >associative_append % ]
      |%1 %
      ]
    |(* ll not nil *)
     #b #tl >Ht1 normalize in ⊢ (???%→?); 
     whd in ⊢ (??%?→?); #Heq destruct (Heq) 
     cases (compare_append … e0) #l *
      [* cases l 
        [#_ #Htab cases (Hind [ ] (sym_eq … Htab)) 
         #out * #lr0  * #t * * #Hlr #Ht #Hmemt
         %{out} %{lr0} %{t} % [% //| %2 //]
        |(* this case is absurd *) 
         #al #tll #Heq1 >H4 #Heq2 @False_ind 
         lapply (cons_injective_l ? bar … Heq2) #Hbar <Hbar in Heq1; #Heq1
         @(absurd (mem ? bar (q1@(c1::q2@[c2; m]))))
          [>Heq1 @mem_append_l2 %1 //
          |% #Hmembar cases (mem_append ???? Hmembar) -Hmembar
            [#Hmembar lapply(Hq1 bar Hmembar) normalize #Habs destruct (Habs)
            |* [#Habs @absurd //]
             #Hmembar cases (mem_append ???? Hmembar) -Hmembar
              [#Hmembar lapply(Hq2 bar Hmembar) normalize #Habs destruct (Habs)
              |* [#Habs @absurd //] #Hmembar @(absurd ?? Hm) @sym_eq @mem_single //
              ]
            ]
          ]
        ]
      |* #Htl #Htab cases (Hind … Htab) #out * #lr0 * #t * * #Hlr #Ht #Hmemt
       %{out} %{lr0} %{t} % [% // | %2 //]
      ] 
    ]
  ]
qed.

(*
lemma tuple_to_config: ∀n,h,t,out,c. is_config n c →
  tuple_encoding n h t = c@out → 
    ∃outq,outa,m. out = outq@[outa;m] ∧ is_config n (bar::outq@[outa]).
#n #h * * #q0 #a0 * * #q1 #a1 #m #out #c * #q * #a * * * #Hq #Ha #Hlen #Hc 
whd in ⊢ (??%?→?); #Heq 
%{(bits_of_state n h q1)} %{(low_char a1)} %{(low_mv m)} %
  [% [ %[ // | cases a1 [|#b] normalize % #H destruct (H)]
     |whd in ⊢ (??%?); @eq_f //]
  |@eq_f cut (∀A.∀a:A.∀l1,l2. a::l1@l2 = (a::l1)@l2) [//] #Hcut
   >append_cons in Heq; >Hcut <associative_append
   >(append_cons ? (low_char a1)) <associative_append #Heq 
   lapply (append_l1_injective_r ?? (c@out) ??? Heq) [%] -Heq 
   >associative_append #Heq @sym_eq @(append_l2_injective ?????? Heq)
   >Hc whd in ⊢ (??%%); @eq_f >length_append >length_append
   @eq_f2 // >length_map >Hlen whd in ⊢ (??%?); @eq_f //
  ]
qed.
*)

lemma tuple_to_config: ∀n,h,t,out,m,c. is_config n c →
  tuple_encoding n h t = c@out@[m] → is_config n (bar::out).
#n #h * * #q0 #a0 * * #q1 #a1 #m #out #lowm #c * #q * #a * * * #Hq #Ha #Hlen #Hc 
whd in ⊢ (??%?→?); #Heq %{(bits_of_state n h q1)} %{(low_char a1)} %
  [% [ %[ // | cases a1 [|#b] normalize % #H destruct (H)]
     |whd in ⊢ (??%?); @eq_f //]
  |@eq_f cut (∀A.∀a:A.∀l1,l2. a::l1@l2 = (a::l1)@l2) [//] #Hcut
   >append_cons in Heq; >Hcut <associative_append
   >(append_cons ? (low_char a1)) <associative_append #Heq 
   lapply (append_l1_injective_r ?? (c@out) ??? Heq) [%] -Heq 
   >associative_append #Heq @sym_eq @(append_l2_injective ?????? Heq)
   >Hc whd in ⊢ (??%%); @eq_f >length_append >length_append
   @eq_f2 // >length_map >Hlen whd in ⊢ (??%?); @eq_f //
  ]
qed.

(* da spostare *)
lemma injective_nat_of: ∀n. injective … (nat_of n).
#n * #a0 #Ha0 * #b0 #Hb0 normalize #Heq
generalize in match Ha0; generalize in match Hb0; >Heq //
qed.

lemma not_of_lt: ∀n,m. nat_of n m < n.
#n * #a #lta //
qed.

(* da spostare *)
lemma injective_map: ∀A,B,f. injective A B f → injective … (map … f).
#A #B #f #injf #l1 elim l1 
  [* // #a2 #l2 normalize #H destruct
  |#a1 -l1 #l1 #Hind * 
    [normalize #H destruct
    |#a2 #l2 normalize #Hmap
     >(injf … (cons_injective_l ????? Hmap)) 
     >(Hind … (cons_injective_r ????? Hmap)) % 
    ]
  ]
qed.

lemma deterministic: ∀M:normalTM.∀l,t1,t2,c,out1,out2. 
  l = graph_enum ?? (ntrans M) → 
  mem ? t1 l → mem ? t2 l →
  is_config (no_states M) c → 
  tuple_encoding ? (nhalt M) t1 = (c@out1) → 
  tuple_encoding ? (nhalt M) t2 = (c@out2) →
  out1 = out2.
#M #l * * #q1 #a1 * * #q11 #a11 #m1 
* * #q2 #a2 * * #q21 #a21 #m2 #c #out1 #out2 #Hl #memt1 #memt2 * 
#state * #char * * * #_ #_ #Hlen #Heqc #tuplet1 #tuplet2 
lapply (mem_to_memb … memt1) >Hl #membt1
lapply (graph_enum_correct ?? (ntrans M) ?? membt1) #Ht1
lapply (mem_to_memb … memt2) >Hl #membt2
lapply (graph_enum_correct ?? (ntrans M) ?? membt2) #Ht2
cut (bar::bits_of_state (no_states M) (nhalt M) q1@[low_char a1]=c)
  [whd in tuplet1:(??%?); >(append_cons ? (low_char a1)) in tuplet1; #tuplet1
   @(append_l1_injective ? (bar::bits_of_state ?? q1@[low_char a1]) ???? tuplet1)
   >Heqc whd in ⊢ (??%%); @eq_f >length_append >length_append
   @eq_f2 // >length_map whd in ⊢ (??%?); >Hlen @eq_f
   >bitlist_length %] #Hcfg1
cut (bar::bits_of_state (no_states M) (nhalt M) q2@[low_char a2]=c)
  [whd in tuplet2:(??%?); >(append_cons ? (low_char a2)) in tuplet2; #tuplet2
   @(append_l1_injective ? (bar::bits_of_state ?? q2@[low_char a2]) ???? tuplet2)
   >Heqc whd in ⊢ (??%%); @eq_f >length_append >length_append
   @eq_f2 // >length_map whd in ⊢ (??%?); >Hlen @eq_f
   >bitlist_length %] #Hcfg2
cut (a1 = a2)  
  [@injective_low_char
   <Hcfg2 in Hcfg1; #H lapply (cons_injective_r ????? H) -H #H
   lapply (append_l2_injective_r … H) [%] -H #H @(cons_injective_l ????? H)]
#Heqa
cut (to_bitlist (no_states M) (nat_of … q1) = 
     to_bitlist (no_states M)  (nat_of … q2))  
  [<Hcfg2 in Hcfg1; #H lapply (cons_injective_r ????? H) -H #H
   lapply (append_l1_injective_r … H) // -H whd in ⊢ (??%%→?); #H 
   lapply (cons_injective_r ????? H) -H #H 
   @(injective_map ?? (λx.bit x) ??? H) 
   (* injective  bit *) * * #H1 destruct (H1) %]
#Hbits
cut (q1 = q2)
  [@injective_nat_of  
   <(bitlist_inv1 (no_states M) (nat_of … q1)) //
   <(bitlist_inv1 (no_states M) (nat_of … q2)) //]
#Heqq
cut (〈q11,a11,m1〉=〈q21,a21,m2〉)
  [<Ht1 <Ht2 @eq_f @eq_f2 //]
#Heqout <Heqout in tuplet2; <Heqq <Heqa >tuplet1
@append_l2_injective %
qed.
