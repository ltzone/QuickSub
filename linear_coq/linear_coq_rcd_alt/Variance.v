Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Infra.



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
  - apply WFS_rcd...
    intros. apply H1 with (i:=i) (im2:=im1)...
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
(* 
Lemma fv_tt_rcd: forall l A ls,
  fv_tt (typ_rcd ((l, A) :: ls)) [=]
  fv_tt A \u fv_tt (typ_rcd ls).
Proof with auto.
  intros.
  induction ls.
  - simpl. fsetdec.
  - simpl in *.  fsetdec.  *)


Lemma open_tt_fresh_eq_inv: forall A B X,
  X `notin` fv_tt A ->
  X `notin` fv_tt B ->
  open_tt A X = open_tt B X ->
  A = B.
Proof with auto.
  unfold open_tt. generalize 0.
  intros. unfold open_tt in H1. generalize dependent B.
  generalize dependent n.
  induction A using typ_rec';intros...
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
  -
    induction B using typ_rec';inversion H1...
    destruct (n == n0);inversion H3.
  -
    induction B using typ_rec';inversion H1...
    { simpl in H1. destruct (n == n0);inversion H3. }
    f_equal. f_equal.
    + f_equal. apply IHA with (n:=n)...
      { simpl in H... }
      { simpl in H0... }
    + apply typ_rcd_inj. apply IHA0 with (n:=n)...
      { simpl in H... } 
      { simpl in H0... } 
      { simpl... rewrite H5... }
Qed.

Theorem fv_tt_open_tt_eq:
  forall A1 A2 X,
    X `notin` fv_tt A1 -> X `notin` fv_tt A2 ->
    fv_tt (open_tt A1 X) [=] fv_tt (open_tt A2 X) ->
    fv_tt A1 [=] fv_tt A2.
Proof with auto.
  intros. intro r. split; intros.
  + destruct (r == X)... { subst. exfalso... }
    apply in_open with (Y:=X) in H2...
    rewrite H1 in H2.
    apply in_open1 in H2. destruct H2...
    simpl in H2. exfalso... apply n. fsetdec.
  + destruct (r == X)... { subst. exfalso... }
    apply in_open with (Y:=X) in H2...
    rewrite <- H1 in H2.
    apply in_open1 in H2. destruct H2...
    simpl in H2. exfalso... apply n. fsetdec.
Qed.



Lemma fold_right_union_base: forall a b l,
  fold_right union (a `union` b) l [=] union a (fold_right union b l).
Proof with auto.
  intros. induction l...
  - simpl. reflexivity.
  - simpl. rewrite IHl. fsetdec.
Qed.

Lemma fold_right_union_app: forall l l1 l2,
  fold_right union l (l1 ++ l2) [=] fold_right union (fold_right union l l1) l2.
Proof with auto.
  induction l1.
  - simpl. reflexivity.
  - simpl. intros. rewrite (IHl1 l2).
    revert a.
    induction l2...
    + simpl. reflexivity.
    + intros. simpl. rewrite IHl2.
      rewrite fold_right_union_base.
      rewrite fold_right_union_base.
      fsetdec. 
Qed.


Lemma fold_union_app3: forall l1 l2 l3 b,
 fold_right union b (l1 ++ l2 ++ l3) [=] fold_right union (fold_right union b l1) (l2 ++ l3).
Proof with auto.
  intros.
  induction l1...
  - simpl. reflexivity.
  - simpl. rewrite IHl1.
    rewrite fold_right_union_base.
    reflexivity.
Qed.


Theorem Msub_refl_eq_fv: forall E im A B evs,
    Sub im Eq evs E A B -> fv_tt A [=] fv_tt B.
Proof with auto.
  intros. dependent induction H; try solve [reflexivity]...
  - destruct cm1, cm2; try solve [ simpl in H1;
      destruct (AtomSetImpl.is_empty evs2);
      destruct (AtomSetImpl.is_empty evs1);inversion H1].
    specialize (IHSub1 eq_refl).
    specialize (IHSub2 eq_refl). 
    simpl. rewrite IHSub1. rewrite IHSub2.
    reflexivity.
  - pick_fresh X. specialize_x_and_L X L.
    specialize (H0 eq_refl).
    apply fv_tt_open_tt_eq in H0...
  - pick_fresh X. specialize_x_and_L X L.
    specialize (H0 eq_refl).
    apply fv_tt_open_tt_eq in H0...
  - cbn [fv_tt]. rewrite !List.map_app. 
    rewrite !fold_union_app3.
    simpl.
    destruct cm1, cm2; try solve [ simpl in H1;
      destruct (AtomSetImpl.is_empty evs2);
      destruct (AtomSetImpl.is_empty evs1);inversion H1].
    rewrite IHSub1... 
    cbn [fv_tt] in IHSub2. 
    rewrite !List.map_app in IHSub2.
    rewrite !fold_right_union_app in IHSub2.
    rewrite IHSub2... reflexivity.
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
  - split;[|split]...
    + apply WFS_rcd... intros. inversion H0.
    + apply WFS_rcd... intros. inversion H0.
  - split;[|split]...
    + apply WFS_rcd... intros. inversion H3.
  - destruct_hypos. split;[|split]...
    + apply WFS_rcd...
      { inversion H3;subst... }
      { intros. inversion H3;subst...
        analyze_binds H8... apply H12 with (i:=i)...
        apply H12 with (i:=i)... }
    + apply WFS_rcd...
      { inversion H4;subst... }
      { intros. inversion H4;subst...
        analyze_binds H8... apply H12 with (i:=i)...
        apply H12 with (i:=i)... }
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


(* Theorem Msub_eq_sem: forall E im evs A B,
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
Qed. *)


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
        apply Msub_refl_eq_fv in H2.
        simpl in H2. rewrite <- H2... }
  + destruct_hypos. split.
    * rewrite List.map_app. rewrite fold_right_union_app.
      simpl. apply union_s_m...
      simpl in H2.
      rewrite List.map_app in H2. rewrite fold_right_union_app in H2...
    * rewrite List.map_app. rewrite fold_right_union_app.
      simpl. apply union_s_m...
      simpl in H3.
      rewrite List.map_app in H3. rewrite fold_right_union_app in H3...
Qed.




Ltac get_well_form :=
    repeat match goal with
    | [ H : Sub _ _ _ _ _ _ |- _ ] => apply sub_regular in H;destruct_hypos   
           end.

Ltac get_type :=
    repeat match goal with
           | [ H : Sub _ _ _ _ _ _ |- _ ] => get_well_form
           | [ H : WFS _ _ |- _ ] => apply WFS_type in H
           end.

           

Ltac add_nil :=
    match goal with
    | [ |- WFS ?E _ ] => rewrite_alist (nil ++ E)                               
    | [ |- Sub _ _ _ ?E _ _ ] => rewrite_alist (nil ++ E)      
    end.



Lemma WFS_weakening: forall E1 E2 T E,
WFS (E1 ++ E2) T ->
WFS (E1 ++ E ++ E2) T.
Proof with auto.
intros.
generalize dependent E.
dependent induction H;intros...
-
apply WFS_fvar with (im:=im)...
-
apply WFS_rec with (L:=L) (im:=im);intros...
+
  rewrite_alist (([(X, bind_sub im)] ++ E1) ++ E ++ E2).
  apply H0...
- 
  apply WFS_rcd...
  intros. apply H1 with (i:=i)...
Qed.


Lemma wf_env_weakening: forall E1 E2 X im,
wf_env (E1++E2) ->
X \notin dom (E1++E2) ->
wf_env (E1 ++ (X~bind_sub im) ++ E2).
Proof with auto.
intros E1.
induction E1;intros...
+ constructor...
+ destruct a.
rewrite_alist ((a, b) :: E1 ++ E2) in H.
rewrite_alist ((a, b) :: E1 ++ [(X, bind_sub im)] ++ E2).
dependent destruction H.
- constructor...
- constructor...
  apply WFS_weakening...
Qed.


Lemma subst_tt_wfs2: forall A B E1 E2 X im,
    WFS (E1 ++ E2) A ->
    WFS (E1 ++ (X ~ bind_sub im) ++ E2) B ->
    WFS (E1 ++ E2) (subst_tt X A B).
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H0;intros...
  -
    simpl.
    destruct (X0==X)...
    apply WFS_fvar with (im:=im0)...
    analyze_binds H...
    
  -
    simpl in *...
    apply WFS_arrow.
    apply IHWFS1 with (im0:=im)...
    apply IHWFS2 with (im0:=im)...
  -
    simpl.
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A0) (im:=im0).
    intros.
    rewrite subst_tt_open_tt_var... 2:{ apply WFS_type in H1... }
    rewrite_alist (([(X0, bind_sub im0)] ++ E1) ++ E2).
    apply H0 with (im1:=im)...
    { add_nil. rewrite app_assoc. apply WFS_weakening... }
  -
    simpl.
    apply WFS_rcd...
    intros. apply binds_map_3 in H3.
    destruct H3 as [A1 [H3 H4]]. subst.
    apply H1 with (i:=i) (im0:=im)...
Qed.
