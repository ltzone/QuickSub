Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import Infra.


Ltac specialize_x_and_L X L :=
  repeat match goal with
         | [H : forall _, _ \notin L -> _, Q : X \notin L |- _ ] => specialize (H _ Q); clear Q
         | [H : forall _, _ \notin L -> _ |- _ ] => assert (X \notin L) by auto
         end.


#[global]
Instance sub_m : Proper (eq ==> eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> eq ==> iff) Sub.
Proof with auto.
  intros.
  repeat (hnf; intros). split.
  + intros. subst. apply Sa_evs_proper with (evs:=x1)...
  + intros. subst. apply Sa_evs_proper with (evs:=y1)... symmetry...
Qed.

(* 
Example test_Sub_1: forall evs, ~ Sub Pos Lt evs empty (typ_mu (typ_arrow typ_top (typ_mu (typ_arrow 0 1))))
    (typ_mu (typ_arrow 0 (typ_mu (typ_arrow 0 1)))).
Proof with auto.
  intros evs Hsub.
  inversion Hsub;subst...
  pick_fresh X. specialize_x_and_L X L.
  unfold open_tt in H4. simpl in H4. simpl_env in H4.
  inversion H4;subst...
  destruct cm1. 2:{ destruct cm2;try solve [inversion H10].
    (* 2 is Lt *)
    inversion H9;subst...
    pick_fresh Y. specialize_x_and_L Y L0.
    unfold open_tt in H5. simpl in H5. simpl_env in H5.
    inversion H5;subst...
    inversion H12;subst. { simpl in H7. admit. }
    inversion H13;subst. 2:{ simpl in H15. admit. }
    simpl in H14. inversion H14.
  }
  destruct cm2. 2:{ inversion H9;subst...
    { (* rec_eq_notin *)
      pick_fresh Y. specialize_x_and_L Y L0.
      unfold open_tt in H5. simpl in H5. simpl_env in H5.
      inversion H5;subst...
      inversion H12;subst. { simpl in H7. admit. }
      exfalso. apply Fr0... (* Y should not be in the set *)
    }
    { (* rec_eq_in *)
      pick_fresh Y. specialize_x_and_L Y L0.
      destruct H5 as [evs' [Hevs' H5]].
      unfold open_tt in H5. simpl in H5. simpl_env in H5.
      inversion H5;subst...
      inversion H12;subst. { simpl in H7. admit. }
      inversion H13;subst. 2:{ simpl in H15. admit. }
      simpl in Hevs'.
      simpl in H10. admit.
    
    }
  }
  admit.
Admitted. *)

(* 
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union`  E \u C \u D \u F). *)

Ltac simple_if_tac := 
  match goal with |- context [if ?A then _ else _] => 
    lazymatch type of A with
    | bool => destruct A 
    | sumbool _ _ => fail "Use if_tac instead of simple_if_tac, since your expression "A" has type sumbool"
    | ?t => fail "Use simple_if_tac only for bool; your expression"A" has type" t
  end end.


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

Lemma WFS_dom: forall E A,
  WFS E A -> fv_tt A [<=] dom E.
Proof with auto.
  intros. induction H;simpl;try apply KeySetProperties.subset_empty...
  + hnf. intros. apply AtomSetImpl.singleton_1 in H0. subst.
    apply binds_In in H...
  + apply AtomSetProperties.union_subset_3...
  + pick_fresh X. specialize_x_and_L X L.
    intros r. intros. pose proof (in_open A r X).
    specialize (H0 r). simpl in H0. apply add_iff in H0.
    2:{ apply H2... intros C. subst. exfalso... }
    destruct H0...
    { subst. exfalso... }
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

Lemma WF_replacing: forall E1 E2 T U (X Y:atom),
    WFS ( E1 ++ X ~ bind_sub U ++E2) T ->
    Y <> X ->
    WFS ( E1 ++ Y ~ bind_sub U ++E2) (subst_tt X Y T).
Proof with auto.
  intros. generalize dependent Y.
  dependent induction H;intros...
  - (* var *)
    simpl. simpl_env. destruct (X0 == X)...
    + subst. apply WFS_fvar with (im:=U)...
    + apply binds_app_iff in H. destruct H.
      * apply WFS_fvar with (im:=im)...
      * apply WFS_fvar with (im:=im)...
        simpl. analyze_binds H.
  -
    (* arrow *)
    simpl. simpl_env. constructor...
  -
    (* rec *)
    simpl. simpl_env.
    apply WFS_rec with (L:=L \u{{X}}) (im:=im)...
    intros. specialize_x_and_L X0 L.
    rewrite  subst_tt_open_tt_var...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma uniq_from_wf_env : forall E,
  wf_env E -> uniq E.
Proof with auto.
  intros. induction H...
Qed.

#[global]
Hint Resolve uniq_from_wf_env : core.

Lemma eqb_refl: forall x, eqb x x = true.
Proof.
  intros. unfold eqb. destruct (KeySetFacts.eq_dec x x);auto.
Qed.


Lemma eqb_false: forall x y, x <> y -> eqb x y = false.
Proof.
  intros. unfold eqb. destruct (KeySetFacts.eq_dec x y);auto.
  exfalso. auto.
Qed.

Lemma compose_cm_inv_1: forall cm1 cm2 evs1 evs1' evs2,
  AtomSetImpl.is_empty evs1 = AtomSetImpl.is_empty evs1' ->
  compose_cm cm1 cm2 evs1 evs2 = compose_cm cm1 cm2 evs1' evs2.
Proof with auto.
  intros.
  destruct cm1, cm2...
  simpl. rewrite H...
Qed.

Lemma compose_cm_inv_2: forall cm1 cm2 evs1 evs2 evs2',
  AtomSetImpl.is_empty evs2 = AtomSetImpl.is_empty evs2' ->
  compose_cm cm1 cm2 evs1 evs2 = compose_cm cm1 cm2 evs1 evs2'.
Proof with auto.
  intros.
  destruct cm1, cm2...
  simpl. rewrite H...
Qed.

Lemma empty_add_remove_mem: forall X Y evs1,
  AtomSetImpl.mem X evs1 = true ->
  AtomSetImpl.is_empty (add Y (remove X evs1)) = AtomSetImpl.is_empty evs1.
Proof.
  intros. destruct (AtomSetImpl.is_empty evs1) eqn:Heq.
  + apply is_empty_iff in Heq. exfalso. apply mem_iff in H. fsetdec.
  + destruct (AtomSetImpl.is_empty (add Y (remove X evs1))) eqn:Heq2;auto.
    exfalso. apply is_empty_iff in Heq2. apply mem_iff in H.
    apply KeySetProperties.empty_is_empty_1 in Heq2.
    hnf in Heq2. specialize (Heq2 Y).
    assert (Y `in` add Y (remove X evs1));auto. apply Heq2 in H0. fsetdec.
Qed.

Ltac solve_mem_case :=
  repeat match goal with 
  | [ H: AtomSetImpl.mem _ _ = true |- _ ] => apply mem_iff in H 
  | [ H: AtomSetImpl.mem _ _ = false |- _ ] => apply not_mem_iff in H end;
  try solve [exfalso;auto];
  try fsetdec.

Lemma subst_tt_mem_remove: forall A1 X Y,
  ((if AtomSetImpl.mem X (fv_tt A1)
  then add Y (remove X (fv_tt A1))
  else fv_tt A1) [=]
  fv_tt (subst_tt X Y A1)).
Proof with auto.
  intros.
  induction A1;simpl in *...
  - destruct (AtomSetImpl.mem X Metatheory.empty) eqn:E;try solve_mem_case.
  - destruct (AtomSetImpl.mem X Metatheory.empty) eqn:E;try solve_mem_case.
  - destruct (AtomSetImpl.mem X Metatheory.empty) eqn:E;try solve_mem_case.
  - destruct (AtomSetImpl.mem X (singleton a)) eqn:E;try solve_mem_case.
    + destruct (a == X);simpl;fsetdec ...
    + destruct (a == X);simpl;fsetdec...
  - destruct (AtomSetImpl.mem X (fv_tt A1_1)) eqn:E1;
    destruct (AtomSetImpl.mem X (fv_tt A1_2)) eqn:E2;
    destruct (AtomSetImpl.mem X (union (fv_tt A1_1) (fv_tt A1_2))) eqn:E3;try solve_mem_case.
Qed.

Lemma sub_replacing: forall E1 E2 A B im cm evs im' X Y,
    Sub im cm evs (E1++ X ~ bind_sub im' ++E2) A B ->
    X <> Y ->
    wf_env (E1 ++ Y ~ bind_sub im' ++ E2) ->
    Sub im cm (if AtomSetImpl.mem X evs then add Y (remove X evs) else evs) 
      ( E1 ++ Y ~ bind_sub im' ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros. generalize dependent Y.
  dependent induction H;intros;simpl;simpl_env;try rewrite empty_b; try solve[constructor;auto]...
  - (* lt top *)
    constructor... 2:{ intros C. destruct A;try solve [inversion C]... simpl in C.
      destruct (a == X);inversion C. }
    apply WF_replacing with (X:=X)...
  - (* fvar pos *)
    destruct (  X0 == X).
    + subst. apply binds_mid_eq in H0...
    + apply Sa_fvar_pos... apply binds_app_iff in H0. destruct H0...
      apply binds_app_iff in H0. destruct H0...
      inversion H0;subst... inversion H3;subst... exfalso... inversion H3.
  - (* fvar neg *)
    destruct (  X0 == X).
    + subst. rewrite singleton_b. rewrite eqb_refl.
      assert (add Y (remove X (singleton X)) [=] singleton Y) by fsetdec.
      rewrite H3.
      apply binds_mid_eq in H0...
    + rewrite singleton_b. rewrite eqb_false...
      apply Sa_fvar_neg... apply binds_app_iff in H0. destruct H0...
      apply binds_app_iff in H0. destruct H0...
      inversion H0;subst... inversion H3;subst... exfalso... inversion H3.
  - (* arrow *)
    specialize (IHSub1 E1 E2 im' X JMeq_refl Y H2 H3)...
    specialize (IHSub2 E1 E2 im' X JMeq_refl Y H2 H3)...
    destruct (AtomSetImpl.mem X evs1) eqn:Eevs1, (AtomSetImpl.mem X evs2) eqn:Eevs2...
    + destruct (AtomSetImpl.mem X (union evs1 evs2)) eqn:Eevs.
      2:{ apply mem_iff in Eevs1. apply not_mem_iff in Eevs. exfalso... }
      assert (add Y (remove X (union evs1 evs2)) [=] union (add Y (remove X evs1)) (add Y (remove X evs2))) by fsetdec.
      rewrite H4.
      apply Sa_arrow with (cm1:=cm1) (cm2:=cm2)...
      rewrite compose_cm_inv_1 with (evs1':= evs1). 
      2:{ apply empty_add_remove_mem... }
      rewrite compose_cm_inv_2 with (evs2':= evs2).
      2:{ apply empty_add_remove_mem... }
      auto.
    + destruct (AtomSetImpl.mem X (union evs1 evs2)) eqn:Eevs.
      2:{ apply mem_iff in Eevs1. apply not_mem_iff in Eevs. exfalso... }
      apply not_mem_iff in Eevs2.
      assert (add Y (remove X (union evs1 evs2)) [=] union (add Y (remove X evs1)) evs2) by fsetdec.
      rewrite H4.
      apply Sa_arrow with (cm1:=cm1) (cm2:=cm2)...
      rewrite compose_cm_inv_1 with (evs1':= evs1). 
      2:{ apply empty_add_remove_mem... }
      auto.
    + destruct (AtomSetImpl.mem X (union evs1 evs2)) eqn:Eevs.
      2:{ apply mem_iff in Eevs2. apply not_mem_iff in Eevs. exfalso... }
      apply not_mem_iff in Eevs1.
      assert (add Y (remove X (union evs1 evs2)) [=] union evs1 (add Y (remove X evs2))) by fsetdec.
      rewrite H4.
      apply Sa_arrow with (cm1:=cm1) (cm2:=cm2)...
      rewrite compose_cm_inv_2 with (evs2':= evs2).
      2:{ apply empty_add_remove_mem... }
      auto.
    + destruct (AtomSetImpl.mem X (union evs1 evs2)) eqn:Eevs.
      { apply not_mem_iff in Eevs1. apply not_mem_iff in Eevs2. apply mem_iff in Eevs.
        apply union_iff in Eevs. destruct Eevs; exfalso... }
      apply not_mem_iff in Eevs1. apply not_mem_iff in Eevs2. apply not_mem_iff in Eevs.
      apply Sa_arrow with (cm1:=cm1) (cm2:=cm2)...
  -
    (* rec lt *)
    apply Sa_rec_lt with (L:=L\u{{X}}\u dom (E1 ++ Y ~ bind_sub im' ++ E2)). intros.
    specialize_x_and_L X0 L.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    specialize (H0 (X0 ~ bind_sub im ++E1) E2 im' X JMeq_refl Y H1).
    apply H0...
    simpl_env...
  - (* rec eq notin *)
    apply Sa_rec_eq_notin with (L:=L\u{{X}}\u dom (E1 ++ Y ~ bind_sub im' ++ E2)). intros.
    specialize_x_and_L X0 L.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    specialize (H0 (X0 ~ bind_sub im ++E1) E2 im' X JMeq_refl Y H1).
    apply H0...
    simpl_env...
  - (* rec eq in *)
    assert (
    (if AtomSetImpl.mem X (union evs (fv_tt A1))
    then add Y (remove X (union evs (fv_tt A1)))
    else union evs (fv_tt A1))
    [=] union (if AtomSetImpl.mem X (evs)
      then add Y (remove X (evs))
      else evs) (if AtomSetImpl.mem X (fv_tt A1) then add Y (remove X (fv_tt A1)) else fv_tt A1)).
    { destruct (AtomSetImpl.mem X (evs)) eqn:Evs1, 
      (AtomSetImpl.mem X (union evs (fv_tt A1))) eqn:Evs2,
      (AtomSetImpl.mem X (fv_tt A1)) eqn:Evs3;solve_mem_case.
    } rewrite H3. clear H3.

    pose proof subst_tt_mem_remove A1 X Y as H3.
    rewrite H3. clear H3.

    apply Sa_rec_eq_in with (L:=L\u{{X}}\u dom (E1 ++ Y ~ bind_sub im' ++ E2) \u fv_tt A1). intros.
    specialize_x_and_L X0 L.
    specialize (H0 (X0 ~ bind_sub im ++E1) E2 im' X JMeq_refl Y H1).
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...

    assert (
      (add X0 (if AtomSetImpl.mem X evs then add Y (remove X evs) else evs)) [=]
      (if AtomSetImpl.mem X (add X0 evs)
        then add Y (remove X (add X0 evs))
        else add X0 evs)
    ).
    { destruct (AtomSetImpl.mem X (add X0 evs)) eqn:Evs1, 
      (AtomSetImpl.mem X evs) eqn:Evs2;try solve_mem_case.
    } rewrite H4. clear H4.

    apply H0. simpl_env. constructor...

  - (* proper *)
    assert (
      (if AtomSetImpl.mem X evs' then add Y (remove X evs') else evs')
      [=] (if AtomSetImpl.mem X evs then add Y (remove X evs) else evs)
    ).
    { destruct (AtomSetImpl.mem X evs) eqn:Evs1, 
      (AtomSetImpl.mem X evs') eqn:Evs2;try solve_mem_case.
    } rewrite H3. apply IHSub...
Qed.


Lemma sub_replacing_var: forall E1 E2 A B im cm evs im' X Y,
    Sub im cm evs (E1++ X ~ bind_sub im' ++E2) (open_tt A X) (open_tt B X) ->
    X \notin fv_tt A \u fv_tt B \u  {{ Y }} ->
    wf_env (E1 ++ Y ~ bind_sub im' ++ E2) ->
    Sub im cm (if AtomSetImpl.mem X evs then add Y (remove X evs) else evs) 
      ( E1 ++ Y ~ bind_sub im' ++E2) (open_tt A Y) (open_tt B Y).
Proof with auto.
  intros.
  rewrite subst_tt_intro with (X:=X)...
  rewrite subst_tt_intro with (T2:=B) (X:=X)...
  apply sub_replacing...
Qed.

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


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union`  E \u C \u D \u F).



Theorem Msub_refl: forall E im A,
    wf_env E -> type A -> WFS E A -> exists evs, Sub im Eq evs E A A.
Proof with auto.
  intros. generalize dependent im. generalize dependent E. induction H0;intros...
  - exists emp...
  - exists emp...
  - inversion H1;subst. destruct im, im0.
    + exists emp...
    + exists (singleton X)...
    + exists (singleton X)...
    + exists emp...
  - inversion H1;subst. destruct IHtype1 with (im:=flip_im im) (E:=E) as [evs1 ?], IHtype2 with (im:=im) (E:=E) as [evs2 ?]...
    exists (union evs1 evs2)...
    apply Sa_arrow with (cm1:=Eq) (cm2:=Eq)...
  - 
    inversion H2;subst.
    pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
    (* need to decide whether X is in evs of (open_tt T X), so we need replacing_var lemma *)
    destruct H0 with (im:=im) (E:=X ~ bind_sub im ++ E) as [evs1 ?]...
    { rewrite_alist (nil ++ X ~ bind_sub im ++ E). apply WFS_im_inv with (im1:=im0)... }
    exists (if AtomSetImpl.mem X evs1 then (remove X evs1) \u fv_tt T else evs1)...
    destruct (AtomSetImpl.mem X evs1) eqn:Evs1.
    + apply mem_iff in Evs1.
      apply Sa_rec_eq_in with (L:=L \u {{X}} \u evs1 \u dom E).
      intros.
      rewrite_alist (nil ++ (X0 ~ bind_sub im) ++ E).
      replace (add X0 (remove X evs1)) with 
      (if AtomSetImpl.mem X evs1 then add X0 (remove X evs1) else evs1)...
      2:{ destruct (AtomSetImpl.mem X evs1) eqn:Evs2;
          repeat match goal with 
          | [ H: AtomSetImpl.mem _ _ = true |- _ ] => apply mem_iff in H 
          | [ H: AtomSetImpl.mem _ _ = false |- _ ] => apply not_mem_iff in H end;
          try solve [exfalso;auto];
          try fsetdec. }
      rewrite_alist (nil ++ (X0 ~ bind_sub im) ++ E).
      apply sub_replacing_var... constructor...
    + apply not_mem_iff in Evs1.
      apply Sa_rec_eq_notin with (L:=L \u {{X}} \u evs1 \u dom E).
      intros.
      rewrite_alist (nil ++ (X0 ~ bind_sub im) ++ E).
      replace (evs1) with 
      (if AtomSetImpl.mem X evs1 then add X0 (remove X evs1) else evs1)...
      2:{ destruct (AtomSetImpl.mem X evs1) eqn:Evs2;
          repeat match goal with 
          | [ H: AtomSetImpl.mem _ _ = true |- _ ] => apply mem_iff in H 
          | [ H: AtomSetImpl.mem _ _ = false |- _ ] => apply not_mem_iff in H end;
          try solve [exfalso;auto];
          try fsetdec. }
      apply sub_replacing_var... constructor...
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


Lemma is_not_empty_iff: forall s,
  AtomSetImpl.is_empty s = false <-> ~ AtomSetImpl.Empty s .
Proof with auto.
  intros. split;intros. 
  + intros C. apply is_empty_iff in C. congruence.
  + destruct (AtomSetImpl.is_empty s) eqn:E... apply is_empty_iff in E.
    congruence.
Qed.

Lemma not_empty_has: forall s, ~ AtomSetImpl.Empty s -> exists x, AtomSetImpl.In x s.
Proof with auto.
  intros. destruct (AtomSetImpl.choose s) eqn:E.
  - exists a. apply AtomSetImpl.choose_1 in E...
  - apply AtomSetImpl.choose_2 in E... congruence.
Qed.

Lemma generalized_unfolding_lemma:
  forall E1 E2 C D A B X im evs,
    wf_env (E1 ++ E2) -> X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2) ->
    Sub im Lt evs (E1 ++ X ~ bind_sub im ++ E2) A B ->
    Sub im Lt evs (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B).
Proof with auto.
  intros.
  dependent induction H1;intros...
  -
    (* Top *)
    simpl. admit.

  -
    (* arrow *)
    simpl. apply Sa_arrow with (cm1:=Lt) (cm2:=Lt).
    
    (* 
   
    TODO: 
    1) add the second conclusion: flip im ~ subst D and C
    2) case analysis on cm1 cm2

    *)

    admit. admit. admit.
  
  -
    (* mu *)
    simpl. apply Sa_rec_lt with (L:=L \u fv_tt C \u fv_tt D \u fv_tt A1 \u fv_tt A2 \u {{X}}).
    intros. specialize_x_and_L X0 L.
    rewrite subst_tt_open_tt_var...
    2:{ admit. }
    rewrite subst_tt_open_tt_var...
    2:{ admit. }
    rewrite <- app_assoc.
    apply H2... admit.
  -
     (* proper *)
     apply Sa_evs_proper with (evs:=evs)...
Admitted.

Lemma unfolding_lemma :
  forall E A B evs,
    Sub Pos Lt evs E (typ_mu A) (typ_mu B) ->
    Sub Pos Lt evs E (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Hq:=H).
  dependent induction H.
  +
    pick fresh X. specialize_x_and_L X L.
    rewrite_alist (nil ++ E).
    rewrite subst_tt_intro with (X:=X)...
    rewrite subst_tt_intro with (X:=X) (T2:=B)...
    subst.
    apply sub_regular in Hq.
    destruct_hypos.
    apply generalized_unfolding_lemma...
  +
    apply Sa_evs_proper with (evs:=evs)...
Qed.