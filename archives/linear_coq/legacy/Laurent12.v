(*** Cut admissibility property for an entailment relation (sub) coming ***)
(*** from a subtyping relation of BCD intersection types                ***)
(*** followed by some related results used in the paper                 ***)
(***    Intersection types with subtyping by means of cut elimination   ***)

(*** Olivier Laurent  19/02/12 - Coq V8.3pl3 ***)

Require Import Omega.



Inductive formula : Set :=
  var   : nat -> formula
| omega : formula
| inter : formula -> formula -> formula
| arrow : formula -> formula -> formula
.

Inductive sub : formula -> formula -> Prop :=
  identity    : forall a, sub a a
| omega_right : forall a, sub a omega
| inter_left1 : forall a b c, sub a b -> sub (inter a c) b
| inter_left2 : forall a b c, sub a b -> sub (inter c a) b
| inter_right : forall a b c, sub a b -> sub a c -> sub a (inter b c)
| arrow_left  : forall a b c, sub c a -> sub (arrow a b) (arrow c b)
| arrow_right : forall a b c d,
    sub c (arrow a d) -> sub d b -> sub c (arrow a b)
| arrow_inter : forall a c d e,
    sub c (arrow a d) -> sub c (arrow a e) -> sub c (arrow a (inter d e))
| arrow_omega : forall a b, sub b (arrow a omega)
| var_left    : forall a x, sub (var x) (arrow a (var x))
| var_right   : forall a x, sub a (arrow omega (var x)) -> sub a (var x)
.




(** Cut/transitivity admissibility **)

Inductive sub_lg : formula -> formula -> nat -> Prop :=
  identity_lg    : forall a, sub_lg a a 1
| omega_right_lg : forall a, sub_lg a omega 1
| inter_left1_lg : forall a b c n,
    sub_lg a b n -> sub_lg (inter a c) b (S n)
| inter_left2_lg : forall a b c n,
    sub_lg a b n -> sub_lg (inter c a) b (S n)
| inter_right_lg : forall a b c n m,
    sub_lg a b n -> sub_lg a c m -> sub_lg a (inter b c) (S (n+m))
| arrow_left_lg  : forall a b c n,
    sub_lg c a n -> sub_lg (arrow a b) (arrow c b) (S n)
| arrow_right_lg : forall a b c d n m,
    sub_lg c (arrow a d) n -> sub_lg d b m -> sub_lg c (arrow a b) (S (n+m))
| arrow_inter_lg : forall a c d e n m,
    sub_lg c (arrow a d) n -> sub_lg c (arrow a e) m ->
       sub_lg c (arrow a (inter d e)) (S (n+m))
| arrow_omega_lg : forall a b, sub_lg b (arrow a omega) 1
| var_left_lg    : forall a x, sub_lg (var x) (arrow a (var x)) 2
| var_right_lg   : forall a x n,
    sub_lg a (arrow omega (var x)) n -> sub_lg a (var x) (S n)
.


Lemma exists_length :
  forall a b, sub a b -> exists n, sub_lg a b n
.

Proof.
intros a b H.
induction H ;
  try destruct IHsub ;
  try destruct IHsub1 ;
  try destruct IHsub2 ;
  eexists ;
  try (constructor ; assumption ; fail) ;
  try (econstructor ; eassumption ; fail).
(* apply inter_left2_lg ; eassumption.
apply arrow_inter_lg ; eassumption. *)
Qed.


Lemma forget_length :
  forall a b n, sub_lg a b n -> sub a b
.

Proof.
intros a b n H.
induction H ; 
  try (constructor ; assumption ; fail) ;
  try (econstructor ; eassumption ; fail).
(* apply inter_left2 ; assumption. *)
Qed.


Theorem sub_trans_lg :
  forall k n m a b c, n+m <= k -> sub_lg a b n -> sub_lg b c m -> sub a c
.

Proof.
intro k.
induction k ; intros n m a b c Cmp Hl Hr.

(* derivation of 0 length: impossible *)
replace n with 0 in Hl ; inversion Hl ; omega.

(* true non-0 case *)
inversion Hr ; subst.

(* */identity *)
eapply forget_length ; eassumption.

(* */omega *)
apply omega_right.

(* */inter_left1 *)
inversion Hl ; subst.
(* identity/inter_left1 *)
eapply forget_length ; eassumption.
(* inter_left1/inter_left1 *)
apply inter_left1.
eapply (IHk n1 (S n0)) ; try omega ; eassumption.
(* inter_left2/inter_left1 *)
apply inter_left2.
eapply (IHk n1 (S n0)) ; try omega ; eassumption.
(* inter_right/inter_left1 *)
eapply (IHk n1 n0) ; try omega ; eassumption.

(* */inter_left2 *)
inversion Hl ; subst.
(* identity/inter_left2 *)
eapply forget_length ; eassumption.
(* inter_left1/inter_left2 *)
apply inter_left1.
eapply (IHk n1 (S n0)) ; try omega ; eassumption.
(* inter_left2/inter_left2 *)
apply inter_left2.
eapply (IHk n1 (S n0)) ; try omega ; eassumption.
(* inter_right/inter_left2 *)
eapply (IHk m n0) ; try omega ; eassumption.

(* */inter_right *)
apply inter_right.
eapply (IHk n n0) ; try omega ; eassumption.
eapply (IHk n m0) ; try omega ; eassumption.

(* */arrow_left *)
inversion Hl ; subst.
(* identity/arrow_left *)
eapply forget_length ; eassumption.
(* inter_left1/arrow_left *)
apply inter_left1.
eapply (IHk n1 (S n0)) ; try omega ; eassumption.
(* inter_left2/arrow_left *)
apply inter_left2.
eapply (IHk n1 (S n0)) ; try omega ; eassumption.
(* arrow_left/arrow_left *)
apply arrow_left.
eapply (IHk n0 n1) ; try omega ; eassumption.
(* arrow_right/arrow_left *)
eapply arrow_right.
eapply (IHk n1 (S n0)) ; try omega ; try eassumption.
apply arrow_left_lg ; assumption.
eapply forget_length ; eassumption.
(* arrow_inter/arrow_left *)
eapply arrow_inter.
eapply (IHk n1 (S n0)) ; try omega ; try eassumption.
eapply arrow_left_lg ; eassumption.
eapply (IHk m (S n0)) ; try omega ; try eassumption.
eapply arrow_left_lg ; eassumption.
(* arrow_omega/arrow_left *)
apply arrow_omega.
(* var_left/arrow_left *)
apply var_left.

(* */arrow_right *)
eapply arrow_right.
eapply (IHk n n0) ; try omega ; eassumption.
eapply forget_length ; eassumption.

(* */arrow_inter *)
eapply arrow_inter.
eapply (IHk n n0) ; try omega ; eassumption.
eapply (IHk n m0) ; try omega ; eassumption.

(* */arrow_omega *)
apply arrow_omega.

(* */var_left *)
inversion Hl ; subst.
(* identity/var_left *)
eapply forget_length ; eassumption.
(* inter_left1/var_left *)
apply inter_left1.
eapply (IHk n0 2) ; try omega ; eassumption.
(* inter_left2/var_left *)
apply inter_left2.
eapply (IHk n0 2) ; try omega ; eassumption.
(* var_right/var_left *)
eapply (IHk n0 2) ; try omega ; try eassumption.
apply arrow_left_lg ; try eassumption.
apply omega_right_lg.

(* */var_right *)
apply var_right.
eapply (IHk n n0) ; try omega ; eassumption.
Qed.


Theorem sub_trans : (* Lemma 4.1 *)
  forall a b c, sub a b -> sub b c -> sub a c
.

Proof.
intros a b c Hl Hr.
assert (exists n, sub_lg a b n) as Hen.
apply exists_length ; assumption.
inversion Hen as [n Hn].
assert (exists m, sub_lg b c m) as Hem.
apply exists_length ; assumption.
inversion Hem as [m Hm].
eapply (sub_trans_lg (n+m)) ; try eassumption ; apply le_refl.
Qed.




(** Arrow lemma **)

Require Import Coq.Program.Equality.

(* ia formulas are intersections (possibly empty) of arrows *)
Inductive ia_formula : formula -> Prop :=
  ia_omega : ia_formula omega
| ia_arrow : forall a b, ia_formula (arrow a b)
| ia_inter :  forall a b, ia_formula a -> ia_formula b -> ia_formula (inter a b)
.

(* left_right_ia a b c if (arrow a b) appears in the intersection c *)
Inductive left_right_ia : formula -> formula -> formula -> Prop :=
  lria_arrow : forall a b c : formula, left_right_ia a b (arrow a b)
| lria_inter1 : forall a b c d,
    left_right_ia a b c -> ia_formula d -> left_right_ia a b (inter c d)
| lria_inter2 : forall a b c d,
    left_right_ia a b d -> ia_formula c -> left_right_ia a b (inter c d)
.

(* left_right_iia a b c if all the arrows built from
   an element in a and an element in b are in the intersection c
   with a and b non empty *)
Inductive left_right_iia : formula -> formula -> formula -> Prop :=
  lriia_inter : forall a b c d e,
    left_right_iia a c e -> left_right_iia b d e ->
      left_right_iia (inter a b) (inter c d) e
| lriia_lria : forall a b c, left_right_ia a b c -> left_right_iia a b c
.

(* as for left_right_iia a b c but with a and b possibly empty *)
Inductive left_right_iia_e : formula -> formula -> formula -> Prop :=
  lriia_omega_e : forall c, left_right_iia_e omega omega c
| lriia_lriia_e : forall a b c, left_right_iia a b c -> left_right_iia_e a b c
.


Lemma rmon1_lriia :
   forall d e a, left_right_iia d e a ->
     forall c, ia_formula c -> left_right_iia d e (inter a c)
.

Proof.
intros d e a H.
induction H ; intros ; constructor ;
  try (constructor ; assumption ; fail).
apply IHleft_right_iia1 ; assumption.
apply IHleft_right_iia2 ; assumption.
Qed.

Lemma rmon1_lriia_e :
   forall d e a, left_right_iia_e d e a ->
     forall c, ia_formula c -> left_right_iia_e d e (inter a c)
.

Proof.
intros d e a H.
induction H ; intros ; constructor.
apply rmon1_lriia ; assumption.
Qed.

Lemma rmon2_lriia :
  forall d e a, left_right_iia d e a -> 
    forall c, ia_formula c -> left_right_iia d e (inter c a)
.

Proof.
intros d e a H.
induction H ; intros ; constructor.
apply IHleft_right_iia1 ; assumption.
apply IHleft_right_iia2 ; assumption.
apply lria_inter2 ; assumption.
Qed.

Lemma rmon2_lriia_e :
   forall d e a, left_right_iia_e d e a ->
     forall c, ia_formula c -> left_right_iia_e d e (inter c a)
.

Proof.
intros d e a H.
induction H ; intros ; constructor.
apply rmon2_lriia ; assumption.
Qed.


Lemma arrow_sub : (* Lemma 4.2 *)
  forall a b c, sub a (arrow b c) -> ia_formula a -> 
    exists d, exists e, left_right_iia_e d e a /\ sub b d /\ sub e c
.

Proof.
intros a b c H.
dependent induction H ; intro ia ; try (inversion ia ; fail).

(* identity *)
eexists ; eexists ; split.
apply lriia_lriia_e ; apply lriia_lria ; apply lria_arrow ; assumption.
split ; apply identity.

(* inter_left1 *)
inversion ia ; subst.
destruct (IHsub b c) as (? & ? & ? & ? & ?) ;
  try assumption ; try reflexivity.
eexists ; eexists ; split.
apply rmon1_lriia_e ; try eassumption.
split ; assumption.

(* inter_left2 *)
inversion ia ; subst.
destruct (IHsub b c) as (? & ? & ? & ? & ?) ;
  try assumption ; try reflexivity.
eexists ; eexists ; split.
apply rmon2_lriia_e ; try eassumption.
split ; assumption.

(* arrow_left *)
eexists ; eexists ; split.
apply lriia_lriia_e ; apply lriia_lria ; apply lria_arrow ; assumption.
split ; try assumption.
apply identity.

(* arrow_right *)
destruct (IHsub1 b d) as (d' & e' & Hia & ? & ?) ;
  try assumption ; try reflexivity.
eexists ; eexists ; split ; try eassumption.
split ; try assumption.
eapply sub_trans ; eassumption.

(* arrow_inter *)
destruct (IHsub1 b d) as (d' & e' & Hia1 & ? & ?) ; try assumption ;
destruct (IHsub2 b e) as (d'' & e'' & Hia2 & ? & ?) ; try assumption ;
  try reflexivity.
inversion Hia1 ; subst ; inversion Hia2 ; subst.
eexists ; eexists ; split ; try eassumption ; split ; try assumption.
apply inter_right ; assumption.
exists d'' ; exists e'' ; split ; try assumption ; split ; try assumption.
apply inter_right ; try assumption.
eapply sub_trans.
apply omega_right.
assumption.
exists d' ; exists e' ; split ; try assumption ; split ; try assumption.
apply inter_right ; try assumption.
eapply sub_trans.
apply omega_right.
assumption.
exists (inter d' d'') ; exists (inter e' e'') ; split.
apply lriia_lriia_e ; apply lriia_inter ; assumption.
split ; eapply inter_right ; try assumption.
apply inter_left1 ; assumption.
apply inter_left2 ; assumption.

(* arrow_omega *)
eexists ; eexists ; split.
apply lriia_omega_e.
split ; apply omega_right.
Qed.




(** Intersection arrow lemma **)

(* ias formulas are non-empty intersections of arrows *)
Inductive ias_formula : formula -> Prop :=
  ias_arrow : forall a b, ias_formula (arrow a b)
| ias_inter :  forall a b, ias_formula a -> ias_formula b -> ias_formula (inter a b)
.


Lemma intersection_arrow : (* Lemma 4.3 *)
  forall a, exists b, ias_formula b /\ sub a b /\ sub b a
.

Proof.
intro a.
induction a.
(* var *)
eexists (arrow omega (var n)).
split ; try split ; constructor.
apply identity.
(* omega *)
exists (arrow omega omega).
split ; try split ; constructor.
(* inter *)
destruct IHa1 as (b1 & ? & ? & ?).
destruct IHa2 as (b2 & ? & ? & ?).
exists (inter b1 b2).
split.
constructor ; assumption.
split ; apply inter_right ;
  try (apply inter_left1 ; assumption) ;
  try (apply inter_left2 ; assumption).
(* arrow *)
exists (arrow a1 a2).
split ; try split ; constructor.
Qed.



(** Correspondence with the BCD subtyping relation **)

Inductive sub_bcd : formula -> formula -> Prop :=
  identity_bcd    : forall a, sub_bcd a a
| trans_bcd       : forall a b c, sub_bcd a b -> sub_bcd b c -> sub_bcd a c
| omega_right_bcd : forall a, sub_bcd a omega
| inter_left1_bcd : forall a b, sub_bcd (inter a b) a
| inter_left2_bcd : forall a b, sub_bcd (inter a b) b
| inter_right_bcd : forall a, sub_bcd a (inter a a)
| inter_bcd       : forall a b c d,
    sub_bcd a c -> sub_bcd b d -> sub_bcd (inter a b) (inter c d)
| arrow_bcd       : forall a b c d,
    sub_bcd c a -> sub_bcd b d -> sub_bcd (arrow a b) (arrow c d)
| arrow_inter_bcd : forall a b c,
    sub_bcd (inter (arrow a b) (arrow a c)) (arrow a (inter b c))
| arrow_omega_bcd : sub_bcd omega (arrow omega omega)
| var_left_bcd    : forall x, sub_bcd (var x) (arrow omega (var x))
| var_right_bcd   : forall x, sub_bcd (arrow omega (var x)) (var x)
.


Lemma sub_sub_bcd : (* Lemmas 3.1, 3.2 and 4.4 *)
  forall a b, sub a b -> sub_bcd a b
.

Proof.
intros a b H.
induction H.
(* identity *)
apply identity_bcd.
(* omega_right *)
apply omega_right_bcd.
(* inter_left1 *)
eapply trans_bcd.
apply inter_left1_bcd.
assumption.
(* inter_left2 *)
eapply trans_bcd.
apply inter_left2_bcd.
assumption.
(* inter_right *)
eapply trans_bcd.
apply inter_right_bcd.
apply inter_bcd ; assumption.
(* arrow_left *)
apply arrow_bcd.
assumption.
apply identity_bcd.
(* arrow_right *)
eapply trans_bcd.
eassumption.
apply arrow_bcd.
apply identity_bcd.
assumption.
(* arrow_inter *)
eapply trans_bcd.
apply inter_right_bcd.
eapply trans_bcd.
apply inter_bcd.
apply IHsub1.
apply IHsub2.
apply arrow_inter_bcd.
(* arrow_omega *)
eapply trans_bcd.
apply omega_right_bcd.
eapply trans_bcd.
apply arrow_omega_bcd.
apply arrow_bcd.
apply omega_right_bcd.
apply identity_bcd.
(* var_left *)
eapply trans_bcd.
apply var_left_bcd.
apply arrow_bcd.
apply omega_right_bcd.
apply identity_bcd.
(* var_right *)
eapply trans_bcd.
eassumption.
apply var_right_bcd.
Qed.


Lemma sub_bcd_sub : (* Lemmas 3.1, 3.2 and 4.4 *)
  forall a b, sub_bcd a b -> sub a b
.

Proof.
intros a b H.
induction H ;
  try (constructor ; apply identity ; fail).
(* trans_bcd *)
eapply sub_trans ; eassumption.
(* inter_left2_bcd *)
(* apply inter_left2 ; apply identity. *)
(* inter_bcd *)
apply inter_right.
apply inter_left1 ; assumption.
apply inter_left2 ; assumption.
(* arrow_bcd *)
eapply arrow_right.
apply arrow_left.
assumption.
assumption.
(* arrow_inter_bcd *)
apply arrow_inter.
apply inter_left1.
apply identity.
apply inter_left2.
apply identity.
Qed.




(** Identity admissibility **)

Inductive sub_noid : formula -> formula -> Prop :=
  identity_noid    : forall x, sub_noid (var x) (var x)
| omega_right_noid : forall a, sub_noid a omega
| inter_left1_noid : forall a b c, sub_noid a b -> sub_noid (inter a c) b
| inter_left2_noid : forall a b c, sub_noid a b -> sub_noid (inter c a) b
| inter_right_noid : forall a b c,
    sub_noid a b -> sub_noid a c -> sub_noid a (inter b c)
| arrow_left_noid  : forall a b c,
    sub_noid c a -> sub_noid (arrow a b) (arrow c b)
| arrow_right_noid : forall a b c d,
    sub_noid c (arrow a d) -> sub_noid d b -> sub_noid c (arrow a b)
| arrow_inter_noid : forall a c d e,
    sub_noid c (arrow a d) -> sub_noid c (arrow a e) ->
      sub_noid c (arrow a (inter d e))
| arrow_omega_noid : forall a b, sub_noid b (arrow a omega)
| var_left_noid    : forall a x, sub_noid (var x) (arrow a (var x))
| var_right_noid   : forall a x,
     sub_noid a (arrow omega (var x)) -> sub_noid a (var x)
.


Lemma sub_sub_noid :
  forall a b, sub a b -> sub_noid a b
.

Proof.
intros a b H.
induction H ; 
  try (constructor ; assumption ; fail) ;
  try (econstructor ; eassumption ; fail).
induction a.
(* var *)
apply identity_noid.
(* omega *)
apply omega_right_noid.
(* inter *)
apply inter_right_noid.
apply inter_left1_noid ; assumption.
apply inter_left2_noid ; assumption.
(* arrow *)
eapply arrow_right_noid.
apply arrow_left_noid ; assumption.
assumption.
(* non infered constructor for inter_left2 *)
(* apply inter_left2_noid ; assumption. *)
Qed.


Lemma sub_noid_sub :
  forall a b, sub_noid a b -> sub a b
.

Proof.
intros a b H.
induction H ; 
  try (constructor ; eassumption ; fail) ;
  try (econstructor ; eassumption ; fail).
(* apply inter_left2 ; assumption. *)
Qed.




(* Thanks to Hugo Herbelin and Marc Lasson for their help with Coq *)