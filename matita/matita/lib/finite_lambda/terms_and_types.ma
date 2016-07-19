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

include "basics/finset.ma".
include "basics/star.ma".


inductive FType (O:Type[0]): Type[0] ≝
  | atom : O → FType O 
  | arrow : FType O → FType O → FType O. 

inductive T (O:Type[0]) (D:O → FinSet): Type[0] ≝
  | Val: ∀o:O.carr (D o) → T O D        (* a value in a finset *)
  | Rel: nat → T O D                    (* DB index, base is 0 *)
  | App: T O D → T O D → T O D          (* function, argument *)
  | Lambda: FType O → T O D → T O D     (* type, body *)
  | Vec: FType O → list (T O D) → T O D (* type, body *)
.

let rec FinSet_of_FType O (D:O→FinSet) (ty:FType O) on ty : FinSet ≝
  match ty with
  [atom o ⇒ D o
  |arrow ty1 ty2 ⇒ FinFun (FinSet_of_FType O D ty1) (FinSet_of_FType O D ty2)
  ].

(* size *)

let rec size O D (M:T O D) on M ≝
match M with
  [Val o a ⇒ 1
  |Rel n ⇒ 1
  |App P Q ⇒ size O D P + size O D Q + 1
  |Lambda Ty P ⇒ size O D P + 1
  |Vec Ty v ⇒ foldr ?? (λx,a. size O D x + a) 0 v +1
  ]
.

(* axiom pos_size: ∀M. 1 ≤ size M. *)

theorem Telim_size: ∀O,D.∀P: T O D → Prop. 
 (∀M. (∀N. size O D N < size O D M → P N) → P M) → ∀M. P M.
#O #D #P #H #M (cut (∀p,N. size O D N = p → P N))
  [2: /2/]
#p @(nat_elim1 p) #m #H1 #N #sizeN @H #N0 #Hlt @(H1 (size O D N0)) //
qed.

lemma T_elim: 
  ∀O: Type[0].∀D:O→FinSet.∀P:T O D→Prop.
  (∀o:O.∀x:D o.P (Val O D o x)) →
  (∀n:ℕ.P(Rel O D n)) →
  (∀m,n:T O D.P m→P n→P (App O D m n)) →
  (∀Ty:FType O.∀m:T O D.P m→P(Lambda O D Ty m)) →
  (∀Ty:FType O.∀v:list (T O D).
     (∀x:T O D. mem ? x v → P x) → P(Vec O D Ty v)) →
  ∀x:T O D.P x.
#O #D #P #Hval #Hrel #Happ #Hlam #Hvec @Telim_size #x cases x //
  [ (* app *) #m #n #Hind @Happ @Hind // /2 by le_minus_to_plus/
  | (* lam *) #ty #m #Hind @Hlam @Hind normalize // 
  | (* vec *) #ty #v #Hind @Hvec #x lapply Hind elim v
    [#Hind normalize *
    |#hd #tl #Hind1 #Hind2 * 
      [#Hx >Hx @Hind2 normalize //
      |@Hind1 #N #H @Hind2 @(lt_to_le_to_lt … H) normalize //
      ]
    ]
  ]
qed.

(* since we only consider beta reduction with closed arguments we could avoid
lifting. We define it for the sake of generality *)
        
(* arguments: k is the nesting depth (starts from 0), p is the lift 
let rec lift O D t k p on t ≝ 
  match t with 
    [ Val o a ⇒ Val O D o a
    | Rel n ⇒ if (leb k n) then Rel O D (n+p) else Rel O D n
    | App m n ⇒ App O D (lift O D m k p) (lift O D n k p)
    | Lambda Ty n ⇒ Lambda O D Ty (lift O D n (S k) p)
    | Vec Ty v ⇒ Vec O D Ty (map ?? (λx. lift O D x k p) v) 
    ].

notation "↑ ^ n ( M )" non associative with precedence 40 for @{'Lift 0 $n $M}.
notation "↑ _ k ^ n ( M )" non associative with precedence 40 for @{'Lift $n $k $M}.

interpretation "Lift" 'Lift n k M = (lift ?? M k n). 

let rec subst O D t k s on t ≝ 
  match t with 
    [ Val o a ⇒ Val O D o a 
    | Rel n ⇒ if (leb k n) then
        (if (eqb k n) then lift O D s 0 n else Rel O D (n-1)) 
        else(Rel O D n)
    | App m n ⇒ App O D (subst O D m k s) (subst O D n k s)
    | Lambda T n ⇒ Lambda O D T (subst O D n (S k) s)
    | Vec T v ⇒ Vec O D T (map ?? (λx. subst O D x k s) v) 
    ].
*)

(* simplified version of subst, assuming the argument s is closed *)

let rec subst O D t k s on t ≝ 
  match t with 
    [ Val o a ⇒ Val O D o a 
    | Rel n ⇒ if (leb k n) then
        (if (eqb k n) then (* lift O D s 0 n*) s else Rel O D (n-1)) 
        else(Rel O D n)
    | App m n ⇒ App O D (subst O D m k s) (subst O D n k s)
    | Lambda T n ⇒ Lambda O D T (subst O D n (S k) s)
    | Vec T v ⇒ Vec O D T (map ?? (λx. subst O D x k s) v) 
    ].
(* notation "hvbox(M break [ k ≝ N ])" 
   non associative with precedence 90
   for @{'Subst1 $M $k $N}. *)
 
interpretation "Subst" 'Subst1 M k N = (subst M k N). 

(*
lemma subst_rel1: ∀O,D,A.∀k,i. i < k → 
  (Rel O D i) [k ≝ A] = Rel O D i.
#A #k #i normalize #ltik >(lt_to_leb_false … ltik) //
qed.

lemma subst_rel2: ∀O,D, A.∀k. 
  (Rel k) [k ≝ A] = lift A 0 k.
#A #k normalize >(le_to_leb_true k k) // >(eq_to_eqb_true … (refl …)) //
qed.

lemma subst_rel3: ∀A.∀k,i. k < i → 
  (Rel i) [k ≝ A] = Rel (i-1).
#A #k #i normalize #ltik >(le_to_leb_true k i) /2/ 
>(not_eq_to_eqb_false k i) // @lt_to_not_eq //
qed. *)


(* closed terms ????
let rec closed_k O D (t: T O D) k on t ≝ 
  match t with 
    [ Val o a ⇒ True
    | Rel n ⇒ n < k 
    | App m n ⇒ (closed_k O D m k) ∧ (closed_k O D n k)
    | Lambda T n ⇒ closed_k O D n (k+1)
    | Vec T v ⇒ closed_list O D v k
    ]
    
and closed_list O D (l: list (T O D)) k on l ≝
  match l with
    [ nil ⇒ True
    | cons hd tl ⇒ closed_k O D hd k ∧ closed_list O D tl k
    ]
. *)

inductive is_closed (O:Type[0]) (D:O→FinSet): nat → T O D → Prop ≝
| cval : ∀k,o,a.is_closed O D k (Val O D o a)
| crel : ∀k,n. n < k → is_closed O D k (Rel O D n)
| capp : ∀k,m,n. is_closed O D k m → is_closed O D k n → 
           is_closed O D k (App O D m n)
| clam : ∀T,k,m. is_closed O D (S k) m → is_closed O D k (Lambda O D T m)
| cvec:  ∀T,k,v. (∀m. mem ? m v → is_closed O D k m) → 
           is_closed O D k (Vec O D T v).
      
lemma is_closed_rel: ∀O,D,n,k.
  is_closed O D k (Rel O D n) → n < k.
#O #D #n #k #H inversion H 
  [#k0 #o #a #eqk #H destruct
  |#k0 #n0 #ltn0 #eqk #H destruct //
  |#k0 #M #N #_ #_ #_ #_ #_ #H destruct
  |#T #k0 #M #_ #_ #_ #H destruct
  |#T #k0 #v #_ #_ #_ #H destruct
  ]
qed.
  
lemma is_closed_app: ∀O,D,k,M, N.
  is_closed O D k (App O D M N) → is_closed O D k M ∧ is_closed O D k N.
#O #D #k #M #N #H inversion H 
  [#k0 #o #a #eqk #H destruct
  |#k0 #n0 #ltn0 #eqk #H destruct 
  |#k0 #M1 #N1 #HM #HN #_ #_ #_ #H1 destruct % //
  |#T #k0 #M #_ #_ #_ #H destruct
  |#T #k0 #v #_ #_ #_ #H destruct
  ]
qed.
  
lemma is_closed_lam: ∀O,D,k,ty,M.
  is_closed O D k (Lambda O D ty M) → is_closed O D (S k) M.
#O #D #k #ty #M #H inversion H 
  [#k0 #o #a #eqk #H destruct
  |#k0 #n0 #ltn0 #eqk #H destruct 
  |#k0 #M1 #N1 #HM #HN #_ #_ #_ #H1 destruct 
  |#T #k0 #M1 #HM1 #_ #_ #H1 destruct //
  |#T #k0 #v #_ #_ #_ #H destruct
  ]
qed.

lemma is_closed_vec: ∀O,D,k,ty,v.
  is_closed O D k (Vec O D ty v) → ∀m. mem ? m v → is_closed O D k m.
#O #D #k #ty #M #H inversion H 
  [#k0 #o #a #eqk #H destruct
  |#k0 #n0 #ltn0 #eqk #H destruct 
  |#k0 #M1 #N1 #HM #HN #_ #_ #_ #H1 destruct 
  |#T #k0 #M1 #HM1 #_ #_ #H1 destruct
  |#T #k0 #v #Hv #_ #_ #H1 destruct @Hv
  ]
qed.

lemma is_closed_S: ∀O,D,M,m.
  is_closed O D m M → is_closed O D (S m) M.
#O #D #M #m #H elim H //
  [#k #n0 #Hlt @crel @le_S //
  |#k #P #Q #HP #HC #H1 #H2 @capp //
  |#ty #k #P #HP #H1 @clam //
  |#ty #k #v #Hind #Hv @cvec @Hv
  ]
qed.

lemma is_closed_mono: ∀O,D,M,m,n. m ≤ n →
  is_closed O D m M → is_closed O D n M.
#O #D #M #m #n #lemn elim lemn // #i #j #H #H1 @is_closed_S @H @H1
qed.
  
  
(*** properties of lift and subst ***)

(*
lemma lift_0: ∀O,D.∀t:T O D.∀k. lift O D t k 0 = t.
#O #D #t @(T_elim … t) normalize // 
  [#n #k cases (leb k n) normalize // 
  |#o #v #Hind #k @eq_f lapply Hind -Hind elim v // 
   #hd #tl #Hind #Hind1 normalize @eq_f2 
    [@Hind1 %1 //|@Hind #x #Hx @Hind1 %2 //]
  ]
qed.

lemma lift_closed: ∀O,D.∀t:T O D.∀k,p. 
  is_closed O D k t → lift O D t k p = t.
#O #D #t @(T_elim … t) normalize // 
  [#n #k #p #H >(not_le_to_leb_false … (lt_to_not_le … (is_closed_rel … H))) //
  |#M #N #HindM #HindN #k #p #H lapply (is_closed_app … H) * #HcM #HcN
   >(HindM … HcM) >(HindN … HcN) //
  |#ty #M #HindM #k #p #H lapply (is_closed_lam … H) -H #H >(HindM … H) //
  |#ty #v #HindM #k #p #H lapply (is_closed_vec … H) -H #H @eq_f 
   cut (∀m. mem ? m v → lift O D m k p = m)
    [#m #Hmem @HindM [@Hmem | @H @Hmem]] -HindM
   elim v // #a #tl #Hind #H1 normalize @eq_f2
    [@H1 %1 //|@Hind #m #Hmem @H1 %2 @Hmem]
  ]
qed.  

*)

lemma subst_closed: ∀O,D,M,N,k,i. k ≤ i → 
  is_closed O D k M → subst O D M i N = M.
#O #D #M @(T_elim … M)
  [#o #a normalize //
  |#n #N #k #j #Hlt #Hc lapply (is_closed_rel … Hc) #Hnk normalize 
   >not_le_to_leb_false [2:@lt_to_not_le @(lt_to_le_to_lt … Hnk Hlt)] //
  |#P #Q #HindP #HindQ #N #k #i #ltki #Hc lapply (is_closed_app … Hc) * 
   #HcP #HcQ normalize >(HindP … ltki HcP) >(HindQ … ltki HcQ) //
  |#ty #P #HindP #N #k #i #ltki #Hc lapply (is_closed_lam … Hc)  
   #HcP normalize >(HindP … HcP) // @le_S_S @ltki
  |#ty #v #Hindv #N #k #i #ltki #Hc lapply (is_closed_vec … Hc)  
   #Hcv normalize @eq_f 
   cut (∀m:T O D.mem (T O D) m v→ subst O D m i N=m)
    [#m #Hmem @(Hindv … Hmem N … ltki) @Hcv @Hmem] 
   elim v // #a #tl #Hind #H normalize @eq_f2
    [@H %1 //| @Hind #Hmem #Htl @H %2 @Htl]
  ]
qed.

lemma subst_lemma:  ∀O,D,A,B,C,k,i. is_closed O D k B → is_closed O D i C →
  subst O D (subst O D A i B) (k+i) C =
  subst O D (subst O D A (k+S i) C) i B.
#O #D #A #B #C #k @(T_elim … A) normalize 
  [//
  |#n #i #HBc #HCc @(leb_elim i n) #Hle 
    [@(eqb_elim i n) #eqni
      [<eqni >(lt_to_leb_false (k+(S i)) i) // normalize 
       >(subst_closed … HBc) // >le_to_leb_true // >eq_to_eqb_true // 
      |(cut (i < n)) 
        [cases (le_to_or_lt_eq … Hle) // #eqin @False_ind /2/] #ltin 
       (cut (0 < n)) [@(le_to_lt_to_lt … ltin) //] #posn
       normalize @(leb_elim (k+i) (n-1)) #nk
        [@(eqb_elim (k+i) (n-1)) #H normalize
          [cut (k+(S i) = n); [/2 by S_pred/] #H1
           >(le_to_leb_true (k+(S i)) n) /2/
           >(eq_to_eqb_true … H1) normalize >(subst_closed … HCc) //
          |(cut (k+i < n-1)) [@not_eq_to_le_to_lt; //] #Hlt 
           >(le_to_leb_true (k+(S i)) n) normalize
            [>(not_eq_to_eqb_false (k+(S i)) n) normalize
              [>le_to_leb_true [2:@lt_to_le @(le_to_lt_to_lt … Hlt) //]
               >not_eq_to_eqb_false // @lt_to_not_eq @(le_to_lt_to_lt … Hlt) //
              |@(not_to_not … H) #Hn /2 by plus_minus/ 
              ]  
            |<plus_n_Sm @(lt_to_le_to_lt … Hlt) //
            ]
          ]
        |>(not_le_to_leb_false (k+(S i)) n) normalize
          [>(le_to_leb_true … Hle) >(not_eq_to_eqb_false … eqni) // 
          |@(not_to_not … nk) #H @le_plus_to_minus_r //
          ]
        ] 
      ]
    |(cut (n < k+i)) [@(lt_to_le_to_lt ? i) /2 by not_le_to_lt/] #ltn 
     >not_le_to_leb_false [2: @lt_to_not_le @(transitive_lt …ltn) //] normalize 
     >not_le_to_leb_false [2: @lt_to_not_le //] normalize
     >(not_le_to_leb_false … Hle) // 
    ] 
  |#M #N #HindM #HindN #i #HBC #HCc @eq_f2 [@HindM // |@HindN //]
  |#ty #M #HindM #i #HBC #HCc @eq_f >plus_n_Sm >plus_n_Sm @HindM // 
   @is_closed_S //
  |#ty #v #Hindv #i #HBC #HCc @eq_f 
   cut (∀m.mem ? m v → subst O D (subst O D m i B) (k+i) C = 
          subst O D (subst O D m (k+S i) C) i B)
    [#m #Hmem @Hindv //] -Hindv elim v normalize [//]
   #a #tl #Hind #H @eq_f2 [@H %1 // | @Hind #m #Hmem @H %2 //]
  ]
qed.


