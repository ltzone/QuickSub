Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export PosVar.


#[global]
Instance sub_m : Proper (eq ==> eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> eq ==> iff) Sub.
Proof with auto.
  intros.
  repeat (hnf; intros). split.
  + intros. subst. apply Sa_evs_proper with (evs:=x1)...
  + intros. subst. apply Sa_evs_proper with (evs:=y1)... symmetry...
Qed.




Definition mode_xor (m1 m2 : IsoMode) : IsoMode :=
  match m1 with
  | Pos => match m2 with
           | Pos => Pos
           | Neg => Neg
           end
  | Neg => match m2 with
           | Pos => Neg
           | Neg => Pos
           end
  end.


Lemma xor_prop_1: forall m,
(mode_xor Pos m) = m.
Proof with auto.
  intros.
  destruct m...
Qed.

Lemma xor_prop_2: forall m,
(mode_xor m Pos) = m.
Proof with auto.
  intros.
  destruct m...
Qed.

Lemma xor_prop_3: forall m1 m2,
(mode_xor m1 m2) = mode_xor (flip_im m1) (flip_im m2).
Proof with auto.
  intros.
  destruct m1;destruct m2...
Qed.

Lemma xor_prop_4: forall m1 m2,
flip_im (mode_xor m1 m2) = mode_xor (flip_im m1) ( m2).
Proof with auto.
  intros.
  destruct m1;destruct m2...
Qed.

Lemma xor_prop_5: forall m1 m2 m3,
mode_xor (mode_xor m1 m2) (mode_xor m1 m3) = mode_xor m2 m3.
Proof with auto.
  intros.
  destruct m1;destruct m2;destruct m3...
Qed.

Lemma xor_prop_refl: forall m,
mode_xor m m = Pos.
Proof with auto.
  intros.
  destruct m...
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

Definition mode_choose {A:Type} im im_x (C D:A) := 
  match im, im_x with
  | Pos, Pos => C
  | Pos, Neg => D
  | Neg, Pos => D
  | Neg, Neg => C
  end.  


Lemma mode_choose_switch: forall {A:Type} im im_x (C D:A),
mode_choose im im_x C D = mode_choose (flip_im im) im_x D C.
Proof.
intros. destruct im, im_x;simpl;auto.
Qed.

(* Lemma generalized_unfolding_lemma:

only LT: cannot deal with

A2 = A1 , B1 <: B2
-----------------
[X -> mu. C ] A1 -> B1 <: [X -> mu. D ] A2 -> B2

  forall E1 E2 C D A B X im im_x evs,
    wf_env (E1 ++ E2) -> X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2) ->
    Sub im Lt evs (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    forall cm' evs',
    Sub Pos cm' evs' E2 (typ_mu (mode_choose im im_x C D)) (typ_mu (mode_choose im im_x D C)) ->
    (Sub im Lt evs (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B))
    . *)

(* 

not dealing with Pos/Neg of C/D properly

when A = B = X, im_x = Neg, im = Pos

cannot expect Sub Neg Lt evs (typ_mu C) (typ_mu D)

Lemma generalized_unfolding_lemma:
  forall E1 E2 C D A B X im im_x evs cm,
    wf_env (E1 ++ E2) -> X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2) ->
    Sub im cm evs (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    forall cm' evs',
    Sub Pos cm' evs' E2 (typ_mu (mode_choose im im_x C D)) (typ_mu (mode_choose im im_x D C)) ->
    exists evs'', (Sub im cm evs'' (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B)). *)


(* Idea:

- need to flip the environment E2?

- need the global invariant for all positive ?

*)



(* 
Try global invariant:
*)



(* Definition well_bind_env im (E:env) (A B : typ) :=
  (forall X, 
    (binds X (bind_sub im) E -> posvar Pos  X A B) /\
    (binds X (bind_sub (flip_im im)) E -> posvar Neg X A B)). *)


Definition well_bind_env im (E:env) (A B : typ) :=
  (forall X im_x, 
    (binds X (bind_sub im_x) E -> posvar (mode_xor im im_x) X A B)).

Lemma well_bind_env_fvar_x: forall E X im im_x,
    well_bind_env im E (typ_fvar X) (typ_fvar X) ->    
    binds X (bind_sub im_x) E ->
    im = im_x.
Proof with auto.
  intros. hnf in H. specialize (H X). destruct im_x, im...
  - specialize (H _ H0). inversion H;subst. exfalso...
  - specialize (H _ H0). inversion H;subst. exfalso...
Qed.

(* 

C and D need to have empty evs


Lemma generalized_unfolding_lemma:
  forall E1 E2 C D A B X im im_x evs cm,
    wf_env (E1 ++ E2) -> X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2) ->
    Sub im cm evs (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    well_bind_env im (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    forall cm' evs',
    Sub im_x cm' evs' E2 (typ_mu (mode_choose im im_x C D)) (typ_mu (mode_choose im im_x D C)) ->
    exists cm'' evs'', (Sub im cm'' evs'' (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B)).

To derive a contradition that


          (2) cm1 = Lt -> evs2 is empty ->

          need a lemma:
          A <: B |> emp
          C <: D |> emp
          --------------
          A[X->C] <: B[X->D] |> emp

          evs2' should be empty, contradiction


*)


Inductive typePairR : typ -> typ -> Prop :=
| tp_nat: 
    typePairR  typ_nat typ_nat
| tp_top: forall  A ,
    type A ->
    typePairR  A typ_top
| tp_top_flip: forall A ,
    type A ->
    typePairR  typ_top A
| tp_fvar_x: forall X,
    typePairR (typ_fvar X) (typ_fvar X)
| tp_arrow: forall  A1 A2 B1 B2,
    typePairR  B1 A1 ->
    typePairR  A2 B2 ->
    typePairR  (typ_arrow A1 A2) (typ_arrow B1 B2)
| tp_rec: forall  A B L,
    (forall X, X \notin L ->
               typePairR (open_tt A X) (open_tt B X)) ->
    typePairR (typ_mu A) (typ_mu B).

Lemma type_pairR_type: forall A B,
    typePairR A B ->
    type A /\ type B.
Proof with auto.
  intros. induction H...
  - destruct_hypos...
  - split...
    + apply type_mu with (L:=L)... intros. specialize_x_and_L X L. destruct_hypos...
    + apply type_mu with (L:=L)... intros. specialize_x_and_L X L. destruct_hypos...
Qed.


Lemma subst_reverse: forall A B X C D,
    typePairR A B -> type (typ_mu C) -> type (typ_mu D) ->
    subst_tt X (typ_mu C) A = subst_tt X (typ_mu D) B ->
    (C = D \/ (X \notin fv_tt A \u fv_tt B)) /\ (A=B).
Proof with auto.
  intros. revert C D H0 H1 H2. induction H;intros;simpl in *...
  - destruct A;simpl in *;try solve [inversion H2]...
    destruct (a == X);try solve [inversion H2].
  - destruct A;simpl in *;try solve [inversion H2]...
    destruct (a == X);try solve [inversion H2].
  - destruct (X0 == X)...
    inversion H2...
  - inversion H3;subst.
    symmetry in H5. apply IHtypePairR1 in H5...
    apply IHtypePairR2 in H6...
    destruct_hypos. destruct H5, H4;subst...
  - pick_fresh X0. specialize_x_and_L X0 L.
    destruct H0 with (C:=C) (D:=D)...
    { rewrite subst_tt_open_tt...
      rewrite subst_tt_open_tt with (P:= typ_mu D)...
      inversion H3;subst. rewrite H5. f_equal.
      simpl. destruct (X0 == X)... exfalso... }
    apply open_tt_fresh_eq_inv in H5... subst.
    split... destruct H4... right.
    intros Hc. apply union_iff in Hc. destruct Hc.
    { apply in_open with (Y:=X0) in H5... }
    { apply in_open with (Y:=X0) in H5... }
Qed.

#[global] Hint Constructors typePairR :core.

Lemma Sub_typePairR:
  forall E im cm evs A B,
    Sub im cm evs E A B ->
    typePairR A B.
Proof with auto.
  intros. induction H...
  - apply tp_top. apply WFS_type in H0...
  - apply tp_rec with (L:=L)...
  - apply tp_rec with (L:=L)...
  - apply tp_rec with (L:=L)...
Qed.


Lemma posvar_comm: forall m A B X,
    posvar m X A B ->
    posvar m X B A.
Proof with auto.
  intros.
  induction H...
  -
    apply pos_rec with (L:=L)...
  -
    apply pos_rec_t with (L:=L)...
Qed.


Lemma pos_rename_3: forall X m n A B Y,
    posvar m X A B ->
    Y \notin {{X}} \u fv_tt A \u fv_tt B ->
    posvar n Y A B.
Proof with auto.
  intros.
  generalize dependent Y.
  generalize dependent n.
  induction H;intros...
  -
    simpl in *...
  -
    simpl in *...
  -
    simpl in *...
    apply pos_rec with (L:=L \u {{X}} \u {{Y}} \u fv_tt A \u fv_tt B).
    +
      intros.
      apply H2...
      apply notin_union...
      split...
      apply notin_union...
      split...
      apply notin_fv_tt_open_aux... 
      apply notin_fv_tt_open_aux...
    +
      intros.
      apply H1...
  -
    simpl in *.
    apply pos_rec_t with (L:=L \u {{X}} \u {{Y}})...
Qed.


Lemma posvar_calc_sign: forall A B,
    typePairR A B ->
    forall X m1 Y m2 m4 C D,
    posvar m1 X A B ->  
    posvar m2 Y A B ->
    posvar (mode_xor m1 m2) X C D ->
    posvar m4 Y C D ->
    X <> Y ->
    posvar m1 X (subst_tt Y C A) (subst_tt Y D B) /\
    posvar (mode_xor m2 m4) Y (subst_tt Y C A) (subst_tt Y D B).
Proof with auto.
  intros A B  H.
  dependent induction H;intros...
  -
    split.
    simpl...
    constructor...
    apply subst_tt_type...
    apply posvar_regular in H2...
    destruct H2...
    simpl...
    constructor...
    apply subst_tt_type...
    apply posvar_regular in H2...
    destruct H2...
  -
    split.
    simpl...
    constructor...
    apply subst_tt_type...
    apply posvar_regular in H2...
    destruct H2...
    simpl...
    constructor...
    apply subst_tt_type...
    apply posvar_regular in H2...
    destruct H2...
  -
    split.
    simpl.
    destruct (X==Y)...
    dependent destruction H...
    destruct H3...
    dependent destruction H0...
    rewrite xor_prop_2 in H1...
    destruct H0...
    simpl.
    destruct (X==Y)...
    dependent destruction H0...
    dependent destruction H...
    destruct H3...
    rewrite xor_prop_1...
    destruct H0...
  -
    dependent destruction H1...
    dependent destruction H2...
    simpl in *...
    split...
    +
      constructor...
      apply IHtypePairR1 with (m2:=flip_im m0) (m4:=m4)...
      rewrite <- xor_prop_3...
      apply posvar_comm...
      apply posvar_comm...
      apply IHtypePairR2 with (m2:=m0) (m4:=m4)...
    +
      constructor...
      rewrite xor_prop_4...
      apply IHtypePairR1 with (m1:=flip_im m) (X:=X)...
      rewrite <- xor_prop_3...
      apply posvar_comm...
      apply posvar_comm...
      apply IHtypePairR2 with (m1:=m) (X:=X)...
  -
    split.
    +
      simpl...
      assert (type C /\ type D).
      apply posvar_regular in H4...
      destruct H6.
      dependent destruction H2;dependent destruction H1.
      *
        apply pos_rec with (L:=L \u L0 \u L1 \u {{X}} \u {{X0}}  \u fv_tt A \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          eapply H0...
          eassumption.
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          eapply H0...
          eapply pos_rename_3...
          eassumption.
          eassumption.
      *
        apply pos_rec with (L:=L \u L0 \u L1 \u {{X}} \u {{X0}}  \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          eapply posvar_self_notin...
          apply notin_fv_tt_open_aux... 
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          apply pos_rename_3 with (X:=X0) (m:=m4)...
      *
        apply pos_rec with (L:=L \u L0 \u L1 \u {{X}} \u {{X0}}  \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          eapply posvar_self_notin...
          apply notin_fv_tt_open_aux... 
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          eapply posvar_self_notin...
          apply notin_fv_tt_open_aux... 
          apply pos_rename_3 with (X:=X0) (m:=m4)...
      *
        rewrite <- subst_tt_fresh...
        rewrite <- subst_tt_fresh...
        apply pos_rec_t with (L:=L0)...        
    +
      simpl...
      assert (type C /\ type D).
      apply posvar_regular in H4...
      destruct H6.
      dependent destruction H2;dependent destruction H1.
      *
        apply pos_rec with (L:=L \u L0 \u L1 \u {{X}} \u {{X0}}  \u fv_tt A \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          eapply H0...
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          eapply H0...
          eapply pos_rename_3...
          eassumption.
          eassumption.
      *
        apply pos_rec with (L:=L \u L0 \u L1 \u {{X}} \u {{X0}}  \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          eapply H0 with (m2:=m0) (m4:=m4) (X0:=X) (m1:=m)...
          eapply posvar_self_notin...
          apply notin_fv_tt_open_aux... 
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          apply pos_rename_3 with (X:=X0) (m:=m4)...
      *
        apply pos_rec with (L:=L \u L0 \u L1 \u {{X}} \u {{X0}}  \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          eapply H0 with (m2:=m0) (m4:=m4) (X0:=X) (m1:=m)...
          eapply posvar_self_notin...
          apply notin_fv_tt_open_aux... 
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          eapply posvar_self_notin...
          apply notin_fv_tt_open_aux... 
          apply pos_rename_3 with (X:=X0) (m:=m4)...
      *
        rewrite <- subst_tt_fresh...
        rewrite <- subst_tt_fresh...
        apply pos_rec_t with (L:=L1)...
Qed.        

(* Lemma subst_lemma:
  forall E A B C D X evs im im_x cm',
    Sub im Lt evs E A B -> evs [=] emp ->
    Sub im_x cm' emp E C D ->
    binds X (bind_sub im_x) E ->
    Sub im Lt emp E (subst_tt X (typ_mu (mode_choose im im_x C D)) A) (subst_tt X (typ_mu (mode_choose im im_x D C)) B).
Proof with auto.
  intros. dependent induction H.
  - admit.

  -
    assert (He1: evs1 [=] emp) by fsetdec.
    assert (He2: evs2 [=] emp) by fsetdec.
    rewrite He1, He2 in *. clear He1 He2.
    destruct cm1, cm2;simpl in H1...
    +
      simpl. rewrite <- H2. apply Sa_arrow with (cm1:=Lt) (cm2:=Lt)...
      * rewrite mode_choose_switch with (C0:=C).
        rewrite mode_choose_switch with (C0:=D).
        apply IHSub1... reflexivity.
      * apply IHSub2... reflexivity.
    +
      destruct (AtomSetImpl.is_empty evs2) eqn:Hempty;inversion H1. simpl.
      rewrite <- H2. apply Sa_arrow with (cm1:=Lt) (cm2:=Lt)...
       *)




(* 
  forall E1 E2 C D A B X im im_x evs cm,
    wf_env (E1 ++ E2) -> X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2) ->
    Sub im cm evs (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    well_bind_env im (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    forall cm',
    Sub im_x cm' emp E2 (typ_mu (mode_choose im im_x C D)) (typ_mu (mode_choose im im_x D C)) ->
    exists cm'' evs'', (Sub im cm'' evs'' (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B)). *)




(* C and D must produce empty evs', otherwise fails *)


(* Lemma in_env_case: forall E0 X im,
X \in dom E0 ->
(binds X (bind_sub im) E0 \/ binds X (bind_sub (flip_im im)) E0).
Proof with auto.
  intros.
  induction E0...
  - fsetdec.
  - simpl in H. destruct a;simpl... apply add_iff in H. destruct H.
    + subst. destruct b. destruct i
  
  apply  destruct H. analyze_binds H0.
    + destruct im...
    + destruct IHis_Menv...
  - analyze_binds H0.
    destruct IHis_Menv...
Qed. *)


Theorem soundness_posvar_simpl: forall E im im_x cm evs A B,
  Sub im cm evs E A B -> forall X, X `notin` evs -> 
    binds X (bind_sub im_x) E -> posvar (mode_xor im im_x) X A B.
Proof with auto.
  intros.
  pose proof soundness_posvar _ _ _ _ _ _ H _ H0.
  destruct H2.
  destruct im, im_x...
Qed.



Theorem posvar_false_simpl: forall E im cm evs A B,
  Sub im cm evs E A B ->  forall X im_x, X `in` evs -> 
    (binds X (bind_sub im_x) E ->  ~ posvar (mode_xor im im_x) X A B).
Proof with auto.
  intros.
  pose proof posvar_false _ _ _ _ _ _ H _ H0.
  destruct H2.
  destruct im, im_x...
Qed.


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


Lemma sub_weakening: forall E1 E2 E3 im cm evs A B,
  Sub im cm evs (E1 ++ E2) A B -> wf_env (E1 ++ E3 ++ E2) ->
  Sub im cm evs (E1 ++ E3 ++ E2) A B.
Proof with auto using WFS_weakening.
  intros.
  dependent induction H...
  - apply Sa_arrow with (cm1:=cm1) (cm2:=cm2)...
  - apply Sa_rec_lt with (L:=L \u dom (E1 ++ E3 ++ E2)) (im:=im)...
    intros. specialize_x_and_L X L.
    rewrite <- app_assoc.
    apply H0... simpl.
    constructor...
  - apply Sa_rec_eq_notin with (L:=L \u dom (E1 ++ E3 ++ E2)) (im:=im)...
    intros. specialize_x_and_L X L.
    rewrite <- app_assoc.
    apply H0... simpl.
    constructor...
  - apply Sa_rec_eq_in with (L:=L \u dom (E1 ++ E3 ++ E2)) (im:=im)...
    intros. specialize_x_and_L X L.
    rewrite <- app_assoc.
    apply H0... simpl.
    constructor...
  - rewrite <- H0. apply IHSub...
Qed.


Lemma generalized_unfolding_lemma:
  forall E1 E2 C D A B X im im_x evs cm,
    wf_env (E1 ++ E2) -> X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2) ->
    Sub im cm evs (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    well_bind_env im (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    forall cm',
    Sub im_x cm' emp E2 (typ_mu (mode_choose im im_x C D)) (typ_mu (mode_choose im im_x D C)) ->
    exists cm'' evs'', (Sub im cm'' evs'' (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B)).
Proof with auto.
  intros.
  generalize dependent C. generalize dependent D.
  dependent induction H1;intros...
  -
    (* Nat *)
    simpl. exists Eq, emp...

  -
    (* Top *)
    simpl. exists Eq, emp...

  -
    (* Top Lt *)
    simpl. exists Lt, emp. apply Sa_top_lt...
    
    admit. admit.

  -
    (* Var pos *)
    simpl. destruct (X0 == X)...
    +
      (* X0 == X *)
      subst. analyze_binds_uniq H0. inversion BindsTacVal;subst.
      exists cm', emp. destruct im_x;simpl in H4...
      admit. admit. (* weakening *)
    +
      (* X0 != X *)
      destruct im.
      * exists Eq, emp. apply Sa_fvar_pos... analyze_binds_uniq H0...
      * exists Eq, emp. apply Sa_fvar_pos... analyze_binds_uniq H0...
      (* weird? *)
  -
    (* Var neg *)
    simpl. destruct (X0 == X)...
    +
      (* X0 == X *)
      subst. analyze_binds_uniq H0.
      apply well_bind_env_fvar_x with (im_x:=im_x) in H2...
      subst... destruct im_x;inversion BindsTacVal.
      (* contradiction on the global invariant *)
    +
      (* X0 != X *)
      destruct im.
      * exists Eq, {{ X0}} . apply Sa_fvar_neg... analyze_binds_uniq H0...
      * exists Eq, {{ X0 }}. apply Sa_fvar_neg... analyze_binds_uniq H0...

  -
    (* arrow *)
    simpl. 
    
    destruct (IHSub1) with (im_x0:=im_x) (cm':=cm') (X0:=X) (E3:=E2) (E4:=E1) (D:=C) (C:=D) as [cm1' [evs1' IHSub1']] ...
    { hnf in H2. hnf. intros.
      apply H2 in H4. inversion H4;subst...
      destruct im, im_x0; simpl in H10;simpl...
    }
    (* split;intros.
      + specialize (H2 X0). destruct H2.
        specialize (H5 H4). inversion H5;subst...
      + specialize (H2 X0). destruct H2.
        destruct im; specialize (H2 H4); inversion H2;subst... } *)
    { destruct im, im_x;simpl in H2;simpl... }
    destruct (IHSub2) with (im_x0:=im_x) (cm':=cm') (X0:=X) (E3:=E2) (E4:=E1) (D:=D) (C:=C) as [cm2' [evs2' IHSub2']]...
    { hnf in H2. hnf. intros.
      apply H2 in H4. inversion H4;subst... }
    (* split;intros.
      + specialize (H2 X0). destruct H2.
        specialize (H2 H4). inversion H2;subst...
      + specialize (H2 X0). destruct H2.
        destruct im; specialize (H5 H4); inversion H5;subst... } *)

      
    destruct ((compose_cm cm1' cm2' evs1' evs2')) eqn:Ecomp.
    2:{
      destruct cm1', cm2';inversion Ecomp.
      + destruct (AtomSetImpl.is_empty evs2') eqn:Eempty; try solve [inversion H5].
        apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
        destruct Eempty as [X' Eempty].
        assert (exists im_x', binds X' (bind_sub im_x') (E1 ++ E2)) by admit.
        destruct H4 as [im_x' H4].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub2' X' im_x' Eempty.
        exfalso. apply H6...
        
        apply posvar_calc_sign with (m2:=mode_xor im im_x) (m4:=im_x) ...
        - admit.
        - hnf in H2. specialize (H2 X' im_x').
          assert (binds X' (bind_sub im_x') (E1 ++ X ~ bind_sub im_x ++ E2))...
          specialize (H2 H7).
          inversion H2;subst...
        - hnf in H2. specialize (H2 X im_x).
          assert (binds X (bind_sub im_x) (E1 ++ X ~ bind_sub im_x ++ E2))...
          specialize (H2 H7).
          inversion H2;subst...
        - rewrite_alist (nil ++ E2) in H3.
          apply sub_weakening with (E3:=E1) in H3...
          apply soundness_posvar_simpl with (X:=X') (im_x:=im_x') in H3...
          rewrite xor_prop_5.
          destruct im, im_x, im_x';
            simpl in H3;simpl;auto;
            apply posvar_comm;auto.
        - apply soundness_posvar_fresh with (X:=X) (im':=im_x) in H3...
          destruct im, im_x;
            simpl in H3;simpl;auto;
            apply posvar_comm;auto.
        - intros Hc. subst.
          apply sub_evs_fv in IHSub2'...
          destruct_hypos.
          admit.
        + destruct (AtomSetImpl.is_empty evs1') eqn:Eempty; try solve [inversion H5].
        apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
        destruct Eempty as [X' Eempty].
        assert (exists im_x', binds X' (bind_sub im_x') E2) by admit.
        destruct H4 as [im_x' H4].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub1' X' im_x' Eempty.
        exfalso. apply H6...
        apply posvar_calc_sign with (m2:=mode_xor (flip_im im) im_x) (m4:=im_x) ...
        - admit.
        - hnf in H2. specialize (H2 X' im_x').
          assert (binds X' (bind_sub im_x') (E1 ++ X ~ bind_sub im_x ++ E2))...
          specialize (H2 H7).
          inversion H2;subst...
          rewrite <- xor_prop_4...
        - hnf in H2. specialize (H2 X im_x).
          assert (binds X (bind_sub im_x) (E1 ++ X ~ bind_sub im_x ++ E2))...
          specialize (H2 H7).
          inversion H2;subst...
          rewrite <- xor_prop_4...
        - apply soundness_posvar_simpl with (X:=X') (im_x:=im_x') in H3...
          rewrite xor_prop_5.
          destruct im, im_x, im_x';
            simpl in H3;simpl;auto;
            apply posvar_comm;auto.
        - apply soundness_posvar_fresh with (X:=X) (im':=im_x) in H3...
          destruct im, im_x;
            simpl in H3;simpl;auto;
            apply posvar_comm;auto.
        - intros Hc. subst.
          apply sub_evs_fv in IHSub1'...
          destruct_hypos.
          admit.
    }
      (* 
      
[[New neat idea]]

      evs2' is not empty:

      exists X' in (E1 ++ E2), 
      ~ posvar X' A2[X-> mu a. C] B2[X-> mu a. D]

      but  posvar X' A2 B2 <--------- requires evs to be empty?
      and  posvar X' mu a. C mu a. D

      uses [posvar_calc_sign]

      gets posvar X' [X-> mu a. C]A2  [X-> mu a. D]B2

      contradiction
      
      *)
        

        (* idea: 
         Sub im Eq evs2' (E1 ++ E2) (subst_tt X (typ_mu C) A2) (subst_tt X (typ_mu D) B2)
         
         
      (i) assume A2 = B2 and cm2 = Eq

         (1) cm1 = Eq -> A1 = B1 -> X in A1 and B1, and C != D -> X notin A2 B2 ->
             
             [Sub im Eq evs2' (E1 ++ E2) (subst_tt X (typ_mu C) A2) (subst_tt X (typ_mu D) B2)]
             becomes [Sub im Eq evs2' (E1 ++  X ~ bind_sub im_x ++ E2) A2 B2]
             -> (deterministic results of the linear algorithm)
             evs2' [=] evs2
             -> exists X in evs2, ~ posvar X A2 B2 -> contradiction with well-bind-env condition

          (2) cm1 = Lt -> evs2 is empty ->

          need a lemma:
          A <: B |> emp
          C <: D |> emp
          --------------
          A[X->C] <: B[X->D] |> emp

          evs2' should be empty, contradiction

      (ii) assume A2 < B2 and cm2 = Lt
            
            (1) cm1 = Eq -> A1 = B1 -> X in A1 and B1, and C != D -> X notin A2 B2 ->
              
              [Sub im Eq evs2' (E1 ++ E2) (subst_tt X (typ_mu C) A2) (subst_tt X (typ_mu D) B2)]
              becomes [Sub im Eq evs2' (E1 ++  X ~ bind_sub im_x ++ E2) A2 B2]
              -> (deterministic results of the linear algorithm)
              Lt != Eq -> contradiction
  
            (2) cm1 = Lt -> evs2 is empty ->


            need another lemma: if Lt then emp,
            to get a contradiction that evs2' should be empty


          *)


    exists c, (union evs1' evs2').
    apply Sa_arrow with (cm1:=cm1') (cm2:=cm2')...
  
  -
    (* rec-lt *)
    simpl.
    pick_fresh X'.
    specialize_x_and_L X' L.
    destruct (H0 im_x X E2 (X' ~ bind_sub im ++ E1)) with (cm' := cm') (C:=C) (D:=D) as [cm1' [evs1' IHSub1']]...
    { constructor... }
    { hnf. intros. pose proof (H2 X0 im_x0) as H2'. 
      destruct (KeySetFacts.eq_dec X' X0).
      { 
        subst. inversion H5;subst...
        2:{ apply binds_In in H6. rewrite !dom_app in H6.
            exfalso. clear - X0 H6 Fr. apply Fr... simpl in H6.
            clear Fr. fsetdec. }
        inversion H6;subst...  
        rewrite xor_prop_refl. 
        apply soundness_posvar_simpl with (X:=X0) (im_x := im_x0) in H1...
        rewrite xor_prop_refl in H1...
      }
      {
        inversion H5;subst...
        { inversion H6;subst;exfalso... } 
        apply H2 in H6.
        inversion H6;subst... 
        { 
          pick_fresh Y. specialize_x_and_L Y (union L0 (singleton X0)).
          rewrite subst_tt_intro with (X:=Y) (T2:=A1)...
          rewrite subst_tt_intro with (X:=Y) (T2:=A2)...
          apply pos_rename_fix... }
        { apply posvar_self_notin...
          { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
            rewrite subst_tt_intro with (X:=Z)...
            apply subst_tt_type... }
          { apply notin_fv_tt_open_aux... }
        }
      }
    }
    rewrite <- subst_tt_open_tt_var in IHSub1'... 2:{ admit. }
    rewrite <- subst_tt_open_tt_var with (P:=(typ_mu D)) in IHSub1'... 
    2:{ admit. }
    destruct cm1'. 2:{ (* TODO: contradiction on Lt/Eq 
    
    !!!! may relies on syntactic equality??

     (subst_tt X (typ_mu C) A1) = (subst_tt X (typ_mu D) A2)
     => A1 = A2
     contradict on H1
    
    *)
      apply Msub_refl_inv in IHSub1'...
      apply open_tt_fresh_eq_inv in IHSub1'...
      2:{ apply notin_fv_subst... }
      2:{ apply notin_fv_subst... }
      apply subst_reverse in IHSub1'...
      2:{ admit. }
      2:{ admit. }
      2:{ admit. }
      destruct_hypos.
      subst...
      apply Msub_lt_not_eq in H1...
      exfalso...
    }
    { exists Lt, evs1'. apply Sa_rec_lt with (L:= L \u {{X}} \u {{X' }}\u dom (E1 ++ E2)).
      intros.  
      replace evs1' with (if AtomSetImpl.mem X' evs1' then AtomSetImpl.add X0 (remove X' evs1') else evs1')...
      2:{ destruct (AtomSetImpl.mem X' evs1') eqn:Eevs...
          apply mem_iff in Eevs.
          pose proof posvar_false_simpl _ _ _ _ _ _ IHSub1' X' im Eevs.
          exfalso. apply H6... rewrite xor_prop_refl.
          rewrite subst_tt_open_tt_var... 2:{ admit. }
          rewrite subst_tt_open_tt_var... 2:{ admit. }
          apply posvar_calc_sign with (m2:=mode_xor im im_x) (m4:=Pos)...
          + admit.
          + apply soundness_posvar_simpl with (X:=X') (im_x:=im) in H1...
            rewrite xor_prop_refl in H1...
          + specialize (H2 X im_x).
            assert ( binds X (bind_sub im_x) (E1 ++ X ~ bind_sub im_x ++ E2))...
            specialize (H2 H7).
            inversion H2;subst...
            { 
              pick_fresh Y. specialize_x_and_L Y (union L0 (singleton X0)).
              rewrite subst_tt_intro with (X:=Y) (T2:=A1)...
              rewrite subst_tt_intro with (X:=Y) (T2:=A2)...
              apply pos_rename_fix... }
            {
              apply posvar_self_notin...
              { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
                rewrite subst_tt_intro with (X:=Z)...
                apply subst_tt_type... }
              { apply notin_fv_tt_open_aux... }
            }
          + rewrite xor_prop_1. 
            rewrite_alist (nil ++ E2) in H4.
            apply sub_weakening with (E3:= (X' ~ bind_sub im ++ E1 ++ X ~ bind_sub im_x)) in H4...
            2:{ simpl. constructor...
                rewrite app_assoc. apply wf_env_weakening... }
            apply soundness_posvar_simpl with (X:=X') (im_x:=im) in H4...
            destruct im,im_x;simpl in H4;auto;apply posvar_comm;auto.
          + rewrite_alist (nil ++ E2) in H4.
            apply sub_weakening with (E3:= (E1 ++ X ~ bind_sub im_x)) in H4...
            2:{ simpl. rewrite app_assoc. apply wf_env_weakening... }
            apply soundness_posvar_simpl with (X:=X) (im_x:=im_x) in H4...
            rewrite xor_prop_refl in H4.
            destruct im,im_x;simpl in H4;auto;apply posvar_comm;auto.
      }
      rewrite_alist (nil ++ X0 ~ bind_sub im ++ E1 ++ E2).
      apply sub_replacing_var...
      { solve_notin... }
      { constructor...  }
    }
    
  -
    (* rec-eq *)
    admit.
  -
    (* rec-eq-notin *)
    admit.
  -
    (* proper *)
    destruct (IHSub im_x X E2 E1) with (cm':=cm') (C:=C) (D:=D) as [cm1' [evs1' IHSub1']]...
    exists cm1', evs1'...

Admitted.


(* but one problem of making C and D equal is that

the unfolding lemma also requires emp in the result
*)

Lemma sub_lt_then_emp: forall im cm evs E A B,
    Sub im cm evs E A B ->
    cm = Lt ->
    evs [=] emp.
Proof with auto.
  intros.
  dependent induction H;subst;try solve [reflexivity]...
  - inversion H1.
  - destruct cm1, cm2; inversion H1;subst...
    + rewrite IHSub1... rewrite IHSub2... fsetdec.
    + destruct (AtomSetImpl.is_empty evs2) eqn:Eevs;
        try solve [inversion H3]. apply is_empty_iff in Eevs.
      apply KeySetProperties.empty_is_empty_1 in Eevs.
      rewrite IHSub1... fsetdec.
    + destruct (AtomSetImpl.is_empty evs1) eqn:Eevs;
        try solve [inversion H3]. apply is_empty_iff in Eevs.
      apply KeySetProperties.empty_is_empty_1 in Eevs.
      rewrite IHSub2... fsetdec.
  - pick_fresh X. specialize_x_and_L X L. rewrite H0... fsetdec.
  - inversion H1.
  - inversion H1.
  - rewrite <- H0. rewrite IHSub... fsetdec.
Qed.


Lemma unfolding_lemma :
  forall A B evs,
    Sub Pos Lt evs nil (typ_mu A) (typ_mu B) ->
    evs [=] emp ->
    Sub Pos Lt emp nil (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Hq:=H).
  rename H0 into Hemp.
  replace empty with (empty ++ empty)...
  dependent induction H;subst...
  { clear H0. specialize_x_and_L X L.
    pick_fresh X. specialize_x_and_L X L.
    destruct (generalized_unfolding_lemma
      nil nil A B (open_tt A X) (open_tt B X) X Pos Pos evs Lt
    ) with (cm':=Lt) ...
    { hnf. intros.
      apply soundness_posvar_simpl with (X:=X0) (im_x:=im_x) in H...
      analyze_binds H0. }
    { simpl. apply Sa_evs_proper with (evs := evs)... }
    destruct H0 as [evs' ?].

    destruct x.
    2:{

      apply Msub_refl_inv in H0...
      apply subst_reverse in H0...
      2:{ admit. }
      2:{ admit. }
      2:{ admit. }
      destruct_hypos.
      subst...
      apply Msub_lt_not_eq in H...
      exfalso...
    }

    pose proof sub_lt_then_emp _ _ _ _ _  _ H0 eq_refl...
    rewrite H1 in *. unfold emp in *.
    rewrite <- subst_tt_intro in H0...
    rewrite <- subst_tt_intro in H0...

    (* needs to reason about Lt/Eq 
    A[x -> mu a. A] = B[x -> mu a. B]
    -> A = B 
    -> contradiction
    *)
  }
  apply IHSub...
  rewrite H0. rewrite Hemp. reflexivity. 
Admitted.


(* Expected lemma:

equiv (A [x -> C]) (B [x -> D]) -> 
equiv A B /\ (X in A B -> equiv C D)


no?

equiv (nat [X -> nat]) (X [X -> nat]) ->
equiv nat X [x]

*)
