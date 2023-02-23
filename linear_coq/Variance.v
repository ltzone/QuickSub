Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Infra.



Ltac specialize_x_and_L X L :=
  repeat match goal with
         | [H : forall _, _ \notin L -> _, Q : X \notin L |- _ ] => specialize (H _ Q); clear Q
         | [H : forall _, _ \notin L -> _ |- _ ] => assert (X \notin L) by auto
         end.

Lemma WFS_im_inv: forall E1 E2 X im1 im2 A,
    WFS (E1 ++ X ~ bind_sub im1 ++ E2) A ->
    WFS (E1 ++ X ~ bind_sub im2 ++ E2) A.
Proof with auto.
  intros. generalize dependent im2. dependent induction H;intros...
  - analyze_binds H.
    + apply WFS_fvar with (im:=im)...
    + apply WFS_fvar with (im:=im2)...
    + apply WFS_fvar with (im:=im)...
  - apply WFS_arrow. apply IHWFS1 with (im2:=im1)... apply IHWFS2 with (im2:=im1)...
  - apply WFS_rec with (L:=L) (im:=im)... intros.
    specialize_x_and_L X0 L. rewrite <- app_assoc. apply H0 with (im2:=im1)...
Qed.

Lemma WFS_type: forall E A,
    WFS E A -> type A.
Proof with auto.
  intros.
  induction H...
  - apply type_mu with (L:=L)...
Qed.


Lemma uniq_from_wf_env : forall E,
  wf_env E -> uniq E.
Proof with auto.
  intros. induction H...
Qed.

#[global]
Hint Resolve uniq_from_wf_env : core.


Lemma open_tt_fresh_eq_inv: forall A B X,
  X `notin` fv_tt A ->
  X `notin` fv_tt B ->
  open_tt A X = open_tt B X ->
  A = B.
Proof with auto.
  unfold open_tt. generalize 0.
  intros. unfold open_tt in H1. generalize dependent B.
  generalize dependent n.
  induction A;intros...
  - induction B;inversion H1...
    destruct (n == n0);inversion H3.
  - induction B;inversion H1...
    destruct (n == n0);inversion H3.
  - simpl in H1.
    destruct (n0 == n).
    + induction B;inversion H1...
      { destruct (n0 == n1);inversion H1;subst...
        inversion H3. }
      { simpl in H1. subst. exfalso... apply H0. simpl... }
    + induction B;inversion H1...
      { destruct (n0 == n2);inversion H1;subst...
        inversion H3. }
  - induction B;inversion H1...
    destruct (n == n0);inversion H3.
    simpl in H1. subst. exfalso... apply H. simpl...
  - induction B;inversion H1...
    destruct (n == n0);inversion H3.
    rewrite IHA with (n:=S n) (B:=B)...
  - induction B;inversion H1...
    destruct (n == n0);inversion H3. simpl in H, H0.
    rewrite IHA1 with (n:=n) (B:=B1)...
    rewrite IHA2 with (n:=n) (B:=B2)...
Qed.



Theorem Msub_refl_inv: forall E im A B evs,
    Sub im Eq evs E A B -> A = B.
Proof with auto.
  intros. dependent induction H...
  - destruct cm1, cm2; try solve [ simpl in H1;
      destruct (AtomSetImpl.is_empty evs2);
      destruct (AtomSetImpl.is_empty evs1);inversion H1].
    specialize (IHSub1 eq_refl).
    specialize (IHSub2 eq_refl). subst...
  - pick_fresh X. specialize_x_and_L X L.
    specialize (H0 eq_refl). apply open_tt_fresh_eq_inv in H0... subst...
  - pick_fresh X. specialize_x_and_L X L.
    specialize (H0 eq_refl). apply open_tt_fresh_eq_inv in H0... subst...
Qed.

Lemma Msub_lt_not_eq: forall im evs E A B,
  Sub im Lt evs E A B -> A <> B.
Proof with auto.
  intros. dependent induction H...
  - destruct cm1.
    { intros C. inversion C;subst. apply IHSub1... }
    destruct cm2.
    { intros C. inversion C;subst. apply IHSub2... }
    simpl in H1. inversion H1.
  - pick_fresh X. specialize_x_and_L X L.
    intros C. inversion C;subst.
    apply H0...
Qed.


Ltac solve_notin :=
  repeat
    match goal with
    | [H : _ |- _ \notin fv_tt (open_tt _ _) ] => apply notin_fv_tt_open_aux
    | [H : _ |- _ \notin fv_tt (subst_tt _ _ _) ] => apply notin_fv_subst
    | [H : _ |- _ \notin (_ \u _) ] => apply notin_union;split
    | [H : _ |- _ \notin _ ] => simpl;auto               
    end.


Theorem sub_regular: forall E im cm evs A B,
  Sub im cm evs E A B -> wf_env E /\ WFS E A /\ WFS E B.
Proof with auto.
  intros. induction H...
  - split... split... 
    apply WFS_fvar with (im:=im)...
    apply WFS_fvar with (im:=im)...
  - split... split...
    apply WFS_fvar with (im:=flip_im im)...
    apply WFS_fvar with (im:=flip_im im)...
  - destruct_hypos. split...
  - split;[|split].
    + pick_fresh X. specialize_x_and_L X L. destruct_hypos...
      inversion H0...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
  - split;[|split].
    + pick_fresh X. specialize_x_and_L X L. destruct_hypos...
      inversion H0...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
  -  split;[|split].
    + pick_fresh X. specialize_x_and_L X L. destruct_hypos...
      inversion H0...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
Qed.



Lemma compose_cm_eq_inv: forall cm1 cm2 evs1 evs2,
  compose_cm cm1 cm2 evs1 evs2 = Some Eq ->
    cm1 = Eq /\ cm2 = Eq.
Proof with auto.
  intros.
  destruct cm1, cm2;inversion H...
  - destruct (AtomSetImpl.is_empty evs2);inversion H1...
  - destruct (AtomSetImpl.is_empty evs1);inversion H1...
Qed.


Theorem Msub_eq_sem: forall E im evs A B,
    Sub im Eq evs E A B -> A = B.
Proof with auto.
  intros.
  dependent induction H...
  - apply compose_cm_eq_inv in H1. destruct_hypos.
    rewrite IHSub1... rewrite IHSub2...
  - pick_fresh X. specialize_x_and_L X L.
    apply open_tt_fresh_eq_inv with (X:=X) in H0...
    subst...
  - pick_fresh X. specialize_x_and_L X L.
    apply open_tt_fresh_eq_inv with (X:=X) in H0...
    subst...
Qed.

Theorem sub_evs_fv: forall E im evs A B,
  Sub im Eq evs E A B -> evs [<=] fv_tt A /\ evs [<=] fv_tt B.
Proof with auto.
  intros. induction H;simpl;try solve [split;fsetdec]...
  + split.
    * intros a. intros.
      pick_fresh X. specialize_x_and_L X L. destruct_hypos.
      apply H0 in H1. apply in_open1 in H1. destruct H1... exfalso. simpl in H1. fsetdec.
    * intros a. intros.
      pick_fresh X. specialize_x_and_L X L. destruct_hypos.
      apply H2 in H1. apply in_open1 in H1. destruct H1... exfalso. simpl in H1. fsetdec.
  + split.
    * intros a. intros.
      pick_fresh X. specialize_x_and_L X L. destruct_hypos.
      apply H0 in H1. apply in_open1 in H1. destruct H1... exfalso. simpl in H1. fsetdec.
    * intros a. intros.
      pick_fresh X. specialize_x_and_L X L. destruct_hypos.
      apply H2 in H1. apply in_open1 in H1. destruct H1... exfalso. simpl in H1. fsetdec.
  + split.
    * intros a. intros. apply union_iff in H1. destruct H1...
      pick_fresh X. specialize_x_and_L X L. destruct_hypos.
      apply (@KeySetProperties.subset_add_2 evs evs X) in H1;try reflexivity.
      apply H0 in H1. apply in_open1 in H1. destruct H1... exfalso. simpl in H1. fsetdec.
    * intros a. intros. apply union_iff in H1. destruct H1...
      { pick_fresh X. specialize_x_and_L X L. destruct_hypos.
        apply (@KeySetProperties.subset_add_2 evs evs X) in H1;try reflexivity.
        apply H2 in H1. apply in_open1 in H1. destruct H1... exfalso. simpl in H1. fsetdec. }
      { assert (Sub im Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2))... apply  Sa_rec_eq_in with (L:=L)...
        apply Msub_eq_sem in H2. inversion H2;subst... }
Qed.