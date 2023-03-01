Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Rules.

Ltac destruct_hypos :=
  repeat
    match goal with
    | [H : _ /\ _ |- _ ] => destruct H
    | [H : exists _, _ |- _ ] => destruct H              
    end.


Lemma decide_typ : forall x y : typ, {x = y} + {~ x = y}.
  intros.
  decide equality.
  decide equality.
Defined.

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...

    destruct (k === n)... simpl. destruct (X == X)...

    destruct (a == X)... contradict Fr; fsetdec.
Qed.

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
  assumption.
Qed.

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
    destruct (j === n)... destruct (i === n)...
Qed.

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...

    unfold open_tt in *.
    pick fresh X.
    apply open_tt_rec_type_aux with (j:=0) (V:=X).
    auto.
    auto.
Qed.

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with auto.
  induction T; simpl; intro H; f_equal...

    destruct (a == Z)...
    contradict H; fsetdec.
Qed.
    
Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...

    destruct (k === n); subst...

    destruct (a == X); subst... apply open_tt_rec_type...
Qed.

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...

  destruct (X == Z)...

    pick fresh Y and apply type_mu...
    rewrite subst_tt_open_tt_var...
Qed.

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with congruence || eauto.
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...

    destruct (j===n)... destruct (i===n)...
Qed.


Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with auto.
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    auto
  ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_exp e ->
  e = subst_ee x u e.
Proof with auto.
  intros x u e; induction e; simpl; intro H; f_equal...

    destruct (a==x)...
    contradict H; fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with auto.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...

    destruct (k === n); subst...

    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with congruence || auto.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.


Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_exp e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e).
Proof with congruence || auto.
  induction e; intros u k Fr; simpl in *; f_equal...

    destruct (k === n)... simpl. destruct (x == x)...

    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_exp e ->
  open_ee e u = subst_ee x u (open_ee e x).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


(* ================================================ *)
(* ================================================ *)
(* ================================================ *)
(* ================================================ *)
(* ================================================ *)
(* ================================================ *)


Lemma In_lemmaR : forall {X: Type} (E1:list X) A  E2,
    In A E2 -> In A (E1 ++ E2).
Proof.
  induction E1; intros. simpl. auto.
  rewrite <- app_comm_cons.
  apply in_cons.
  apply  IHE1.
  assumption.
Qed.  

Lemma In_lemmaL : forall {X: Type}  E2 (E1:list X) A,
    In A E1 -> In A ( E1 ++ E2).
Proof.
  induction E2;intros.
  -
    rewrite app_nil_r.
    assumption.
  -
    rewrite cons_app_one.
    rewrite <- app_assoc.
    apply IHE2.
    apply in_split in H.
    destruct H.
    destruct H.
    rewrite H.
    rewrite app_assoc.
    apply In_lemmaR.
    rewrite cons_app_one.
    rewrite app_assoc.
    rewrite <-cons_app_one.
    apply in_eq.
Qed.



Lemma wfs_type: forall E T,
    WFS E T -> type T.
Proof with auto.
  intros.
  induction H...
  apply type_mu with (L:=L)...
Qed.

Lemma subst_open_tt_rec : forall T A, type A -> forall Y X,
    Y `notin` fv_tt T ->
    X `notin` fv_tt T -> forall n,
        subst_tt X Y (open_tt_rec n A T) = open_tt_rec n (subst_tt X Y A) T.
Proof with auto.
  induction T; intros; unfold open_tt in *; simpl in *; try solve [f_equal;eauto]; eauto.
  - destruct (n0 == n); simpl; eauto.
  - destruct (a == X); simpl; eauto; subst.
    apply notin_singleton_1 in H1.
    destruct H1...
Qed.


Lemma wfs_weakening: forall E1 E2 T E,
    WFS (E1 ++ E2) T ->
    WFS (E1 ++ E ++ E2) T.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    apply WFS_fvar with (im:=im)...
  -
    apply WFS_rec with (L:=L) (im:=im)...
    intros.
    rewrite_alist (([(X, bind_sub im)] ++ E1) ++ E ++ E2).
    apply H0...
Qed.

Lemma subst_tt_wfs: forall A B E X,
    WFS E A ->
    WFS E B ->
    WFS E (subst_tt X A B).
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H0;intros...
  -
    simpl.
    destruct (X0==X)...
    apply WFS_fvar with (im:=im)...
  -
    simpl in *...
  -
    simpl.
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A0) (im:=im)...
    intros.
    rewrite subst_tt_open_tt_var...
    apply H0...
    rewrite_alist (nil ++ [(X0, bind_sub im)] ++ E).
    apply wfs_weakening...
    apply wfs_type with (E:=E)...
Qed.

Lemma notin_fv_subst: forall X A B Y,
    X \notin fv_tt A ->
    X \notin fv_tt B ->
    X <> Y ->
    X \notin fv_tt (subst_tt Y A B).
Proof with auto.
  intros.
  induction B;simpl in *...
  destruct (a == Y)...
Qed.

Lemma notin_union: forall X A B,
    X `notin` (union A B) <->
    X `notin` A /\ X `notin` B.
Proof.
  intros.
  split.
  split; auto.
  intros.
  destruct H.
  auto.  
Qed.


Lemma notin_fv_tt_open_aux : forall X U T,
    X `notin` fv_tt T ->
    X \notin fv_tt U ->
    X `notin` fv_tt (open_tt T U).
Proof with auto.
  intros.
  simpl.
  unfold open_tt.
  unfold open_tt_rec.
  generalize 0.
  induction T;simpl in *;intros...
  destruct (n0==n)...
Qed.

Lemma in_dec: forall T X,
    X \notin T \/ X \in T.
Proof with auto.
  intros.
  apply notin_diff_1.
  assert (AtomSetImpl.diff T T [=] Metatheory.empty).
  apply AtomSetProperties.diff_subset_equal.
  apply KeySetProperties.subset_refl.
  rewrite H...
Qed.

Lemma in_open: forall A X Y,
    X `in` fv_tt A ->
    X <> Y ->
    X `in` fv_tt (open_tt A Y).
Proof with auto.
  intros A X Y.
  unfold open_tt.
  generalize 0.
  induction A;intros;simpl in *...
  apply AtomSetProperties.FM.empty_iff in H.
  destruct H.
  apply AtomSetImpl.union_1 in H.
  destruct H.
  apply AtomSetImpl.union_2.
  apply IHA1...
  apply AtomSetImpl.union_3.
  apply IHA2...
Qed.

Lemma open_rec_eq :
  forall A1 A2 X n,
    open_tt_rec n (typ_fvar X) A1 = open_tt_rec n X A2 ->
    X \notin (union (fv_tt A1) (fv_tt A2)) ->
    A1 = A2.
Proof with auto.
  induction A1; intros; simpl in *.
  -
    destruct A2; simpl in *; try (inversion H); eauto.
    destruct (n == n0); inversion H.
  - destruct A2; simpl in *; try (inversion H); eauto.
    destruct (n == n0); inversion H.
  - destruct (n0 == n).
    destruct A2; simpl in *; try (inversion H); eauto.
    destruct (n0 == n1); subst; eauto.
    inversion H. subst.
    apply notin_union in H0.
    destruct H0.
    apply notin_singleton_1 in H1.
    destruct H1...
    destruct A2; simpl in *; try (inversion H); eauto.
    destruct (n0 == n2); try (inversion H).
    subst. eauto.
  - destruct A2; simpl in *; try (inversion H); eauto.
    destruct (n == n0); try (inversion H).
    apply notin_union in H0.
    destruct H0.
    apply notin_singleton_1 in H0.
    destruct H0...
  - destruct A2; simpl in *; try (inversion H); eauto.
    destruct (n == n0); inversion H.
    apply IHA1 in H2; eauto. rewrite H2.
    eauto.
  - destruct A2; simpl in *; try (inversion H); eauto.
    destruct (n == n0); inversion H.
    apply IHA1_1 in H2; eauto.
    apply IHA1_2 in H3; eauto.
    subst. eauto.
Qed.

Lemma in_open0: forall A X Y k,
    X `in` fv_tt (open_tt_rec k A Y) ->
    X `in` fv_tt A \/ X \in fv_tt Y.
Proof with auto.
  intros.
  generalize dependent k.
  induction Y;intros;simpl in *...
  -
    destruct (k==n)...
  -
    specialize (IHY (S k)).
    apply IHY in H.
    destruct H...
  -
    apply AtomSetImpl.union_1 in H. 
    destruct H.
    specialize (IHY1 k).
    apply IHY1 in H.
    destruct H...
    specialize (IHY1 k).
    apply IHY2 in H.
    destruct H...
Qed.

Lemma in_open1: forall A X Y ,
    X `in` fv_tt (open_tt Y A) ->
    X `in` fv_tt A \/ X \in fv_tt Y.
Proof with auto.
  intros.
  unfold open_tt in *.
  apply in_open0 with (k:=0)...
Qed.

  

Lemma in_notin: forall T X Y,
    X \in T ->
          Y \notin T ->
          X <> Y.
Proof with auto.
  intros.
  apply AtomSetProperties.add_equal in H.  
  rewrite AtomSetProperties.add_union_singleton in H.
  rewrite <- H in H0.
  auto.
Qed.
