Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Rules.

Lemma notin_fv_tt_open : forall X U T,
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


Lemma notin_fl_tt_open : forall X U T,
    X `notin` fl_tt T ->
    X \notin fl_tt U ->
    X `notin` fl_tt (open_tt T U).
Proof with auto.
  intros.
  unfold open_tt.
  unfold open_tt_rec.
  generalize 0.
  induction T;simpl in *;intros...
  destruct (n0==n)...
Qed.

Lemma notin_union: forall X A B,
    X `notin` (union A B) <->
    X `notin` A /\ X `notin` B.
Proof with auto.
  split.
  intros;split...
  intros;destruct H...
Qed.

Lemma notin_fv_subst2: forall X A B Y,
    X \notin fv_tt A ->
    X \notin fv_tt B ->
    X <> Y ->
    X \notin fv_tt (subst_tt Y A B).
Proof with auto.
  intros.
  induction B...
  -
    simpl.
    destruct (a == Y)...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
Qed.

Lemma notin_fv_subst: forall X A B,
    X \notin fv_tt A ->
    X \notin fv_tt B ->
    X \notin fv_tt (subst_tt X A B).
Proof with auto.
  intros.
  induction B...
  -
    simpl.
    destruct (a == X)...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
Qed.



Lemma in_dec: forall T X,
    X \notin T \/ X \in T.
Proof.
  intros.
  apply notin_diff_1.
  assert (AtomSetImpl.diff T T [=] {}).
  apply AtomSetProperties.diff_subset_equal.
  apply KeySetProperties.subset_refl.
  rewrite H.
  auto.
Qed.

Ltac destruct_hypos :=
  repeat
    match goal with
    | [H : _ /\ _ |- _ ] => destruct H
    | [H : exists _,_ |- _ ] => destruct H                                  
    end.

Ltac specialize_x_and_L X L :=
  repeat match goal with
         | [H : forall _, _ \notin L -> _, Q : X \notin L |- _ ] => specialize (H _ Q); clear Q
         | [H : forall _, _ \notin L -> _ |- _ ] => assert (X \notin L) by auto
         end.


Ltac add_nil :=
    match goal with
    | [ |- WFS ?E _ ] => rewrite_alist (nil ++ E)                               
    | [ |- Sub ?E _ _ ] => rewrite_alist (nil ++ E)                                  
    end.


Lemma type_subst : forall A, 
    forall X B, type B -> type (subst_tt X B A) -> type A.
Proof with auto.
  intros.
  dependent induction H0;try solve [destruct A; simpl in *; inversion x; eauto]...
    destruct A; simpl in *; inversion x; eauto.
    apply type_mu with (L := union L (singleton X)).
    intros.
    specialize_x_and_L X0 L.
    eapply (H0 B H X); eauto.
    subst.
    apply subst_tt_open_tt_var; eauto.
Defined.

Lemma WFS_type: forall E T,
    WFS E T -> type T.
Proof with auto.
  intros.
  induction H...
  apply type_mu with (L:=L)...
Qed.

Lemma subst_tt_rcd: forall  Y X A B,
    (typ_rcd X (subst_tt Y A B)) = subst_tt Y A (typ_rcd X B).
Proof with auto.
  intros...
Qed.  


Lemma WFS_weakening: forall E1 E2 T E,
    WFS (E1 ++ E2) T ->
    WFS (E1 ++ E ++ E2) T.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    apply WFS_rec with (L:=L)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H0...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H2...
Qed.

Lemma subst_tt_wfs: forall A B E X,
    WFS E A ->
    WFS E B ->
    WFS E (subst_tt X A B).
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H0;intros;simpl in *...
  -
    destruct (X0==X)...
  -
    assert (type A0).
    apply WFS_type in H3...
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A0).
    intros.
    rewrite  subst_tt_open_tt_var...
    rewrite  subst_tt_rcd.
    rewrite  <- subst_tt_open_tt...
    apply H0...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
    apply WFS_weakening...
    intros.
    rewrite  subst_tt_open_tt_var...
    apply H2...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
    apply WFS_weakening...
Qed.

Lemma subst_tt_wfs2: forall Y B E1 E2 X,
    WFS (E1 ++ (X ~ bind_sub) ++ E2) B ->
    WFS (E1 ++ (Y ~ bind_sub) ++ E2) (subst_tt X Y B).
Proof with auto.
  intros.
  dependent induction H;intros;simpl in *...
  -
    destruct (X0==X)...
    analyze_binds H...
  -
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A \u {{Y}});intros.
    rewrite  subst_tt_open_tt_var...
    rewrite  subst_tt_rcd.
    rewrite  <- subst_tt_open_tt...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ (Y, bind_sub) :: E2).
    apply H0...
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ (Y, bind_sub) :: E2).
    apply H2...
Qed.

Lemma subst_tt_wfs3: forall  B E1 E2 X A,
    WFS (E1 ++ (X ~ bind_sub) ++ E2) B ->
    WFS (E1 ++ E2 ) A ->
    X \notin fv_tt A ->
    WFS (E1 ++ E2) (subst_tt X A B).
Proof with auto.
  intros.
  dependent induction H;intros;simpl in *...
  -
    destruct (X0==X)...
    analyze_binds H...
  -
    assert (type A).
    apply WFS_type in H3...
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A );intros.
    rewrite  subst_tt_open_tt_var...
    rewrite  subst_tt_rcd.
    rewrite  <- subst_tt_open_tt...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
    apply WFS_weakening...
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H2...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
    apply WFS_weakening...
Qed.

Lemma sub_regular : forall E A B ,
    Sub E A B -> wf_env E /\ WFS E A /\ WFS E B.
Proof with auto.
  intros.
  dependent induction H;try solve [destruct_hypos;repeat split;auto]...
  -
    split.
    pick fresh X.
    specialize_x_and_L X L.
    destruct_hypos.
    dependent destruction H2...
    split;
      apply WFS_rec with (L:=L \u fv_tt A1 \u fv_tt A2);intros...
    eapply H2...
    eapply H2...
Qed.  

Lemma open_subst_twice : forall A (X Y:atom),
    X \notin fv_tt A ->
    subst_tt X Y (open_tt A (open_tt A X)) = (open_tt A (open_tt A Y)).
Proof with auto.
  intros.
  remember (open_tt A X).
  rewrite subst_tt_open_tt...
  rewrite <- subst_tt_fresh...
  f_equal...
  subst.
  rewrite <- subst_tt_intro...
Qed.  


    
(* =============================== *)
(* =============================== *)
(* =============================== *)
(* =============================== *)
(* =============================== *)
(* =============================== *)


Ltac get_well_form :=
    repeat match goal with
           | [ H : Sub _ _ _ |- _ ] => apply sub_regular in H;destruct_hypos
           end.

Ltac get_type :=
    repeat match goal with
           | [ H : Sub _ _ _ |- _ ] => get_well_form
           | [ H : WFS _ _ |- _ ] => apply WFS_type in H
           end.



Lemma Reflexivity : forall E A,
    wf_env E ->
    WFS E A ->
    Sub E A A.
Proof with auto.
  intros.
  induction H0...
  apply S_rec with (L:=L \u dom E);intros...
Qed.

Lemma WFS_strengthening: forall E1 E2 T X m,
    WFS (E1 ++ X ~ m ++ E2) T->
    X \notin fv_tt T ->
    WFS (E1 ++ E2) T.
Proof with auto.
  intros.
  dependent induction H;try solve [simpl in *;constructor;eauto]...
  -
    analyze_binds H...
    simpl.
    apply D.F.singleton_iff...
  -
    simpl in *.
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A).
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (m0:=m)...
    apply notin_fv_tt_open...
    simpl.
    apply notin_fv_tt_open...
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H2 with (X1:=X) (m0:=m)...
    apply notin_fv_tt_open...
Qed.

Lemma Sub_weakening: forall E E1 E2 A B,
    Sub (E1++E2) A B ->
    wf_env (E1 ++ E ++ E2) ->
    Sub (E1++E++E2) A B.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    constructor...
    apply WFS_weakening...
  -
    apply S_rec with (L:=L \u dom (E1 ++ E ++ E2))...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply WFS_weakening...
    rewrite_alist ([(X, bind_sub)] ++ E1 ++ E2)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply WFS_weakening...
    rewrite_alist ([(X, bind_sub)] ++ E1 ++ E2)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H2...
    rewrite_alist ([(X, bind_sub)] ++ E1 ++ E ++ E2)...
  -
    apply S_top...
    apply WFS_weakening...
Qed.