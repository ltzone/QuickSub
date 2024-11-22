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

Instance typ_eq_dec: EqDec_eq typ.
Proof with auto.
  hnf. apply decide_typ.
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
  + clear H0. induction T.
    - simpl. fsetdec.
    - simpl. apply KeySetProperties.union_subset_3.
      * destruct a. simpl. apply H1 with (i:=a)...
      * apply IHT... { inversion H;subst... }
        intros. apply H1 with (i:=i)...
        right...
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
  -
    (* rcd *)
    simpl. apply WFS_rcd...
    intros.
    apply binds_map_3 in H3. destruct_hypos.
    subst. apply H1 with (i:=i)...
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
  induction A1 using typ_rec'.
  - simpl in *.
    destruct (AtomSetImpl.mem X Metatheory.empty) eqn:E;try solve_mem_case.
  - simpl in *.
    destruct (AtomSetImpl.mem X Metatheory.empty) eqn:E;try solve_mem_case.
  - simpl in *.
    destruct (AtomSetImpl.mem X Metatheory.empty) eqn:E;try solve_mem_case.
  - simpl in *.
    destruct (AtomSetImpl.mem X (singleton x)) eqn:E;try solve_mem_case.
    + destruct (x == X);simpl;fsetdec ...
    + destruct (x == X);simpl;fsetdec...
  - simpl in *...
  - simpl in *...
    destruct (AtomSetImpl.mem X (fv_tt A1_1)) eqn:E1;
    destruct (AtomSetImpl.mem X (fv_tt A1_2)) eqn:E2;
    destruct (AtomSetImpl.mem X (union (fv_tt A1_1) (fv_tt A1_2))) eqn:E3;try solve_mem_case.
  - simpl in *. destruct (AtomSetImpl.mem X Metatheory.empty) eqn:E;try solve_mem_case.
  -
    replace (fv_tt (typ_rcd ((l, A1) :: ls))) with (fv_tt A1 `union` fv_tt (typ_rcd ls)).
    2:{ simpl. reflexivity. }
    replace (fv_tt (subst_tt X Y (typ_rcd ((l, A1) :: ls)))) with
        (fv_tt (subst_tt X Y A1) `union` fv_tt (subst_tt X Y (typ_rcd ls))).
    2:{ simpl. reflexivity. }
    destruct (AtomSetImpl.mem X (fv_tt A1)) eqn:E1;
    destruct (AtomSetImpl.mem X (fv_tt (typ_rcd ls))) eqn:E2;
    destruct (AtomSetImpl.mem X (union (fv_tt A1) (fv_tt (typ_rcd ls)))) eqn:E3;try solve_mem_case.
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

  - (* rcd *)
    apply Sa_rcd_lt...
    { destruct tys... intros C. simpl in C. inversion C. }
    intros.
    apply binds_map_3 in H5. destruct_hypos.
    subst.
    apply WF_replacing with (X:=X)...
    apply H2 with (l:=l)...

  - 
    (* rcd cons *)
    specialize (IHSub1 E1 E2 im' X JMeq_refl Y H2 H3)...
    specialize (IHSub2 E1 E2 im' X JMeq_refl Y H2 H3)...
    destruct (AtomSetImpl.mem X evs1) eqn:Eevs1, (AtomSetImpl.mem X evs2) eqn:Eevs2...
    + destruct (AtomSetImpl.mem X (union evs1 evs2)) eqn:Eevs.
      2:{ apply mem_iff in Eevs1. apply not_mem_iff in Eevs. exfalso... }
      assert (add Y (remove X (union evs1 evs2)) [=] union (add Y (remove X evs1)) (add Y (remove X evs2))) by fsetdec.
      rewrite H4.
      apply Sa_rcd_cons with (cm1:=cm1) (cm2:=cm2)...
      { simpl in IHSub2. rewrite !map_app in IHSub2... }
      { rewrite compose_cm_inv_1 with (evs1':= evs1). 
        2:{ apply empty_add_remove_mem... }
        rewrite compose_cm_inv_2 with (evs2':= evs2).
        2:{ apply empty_add_remove_mem... }
        auto.
      }
    + destruct (AtomSetImpl.mem X (union evs1 evs2)) eqn:Eevs.
      2:{ apply mem_iff in Eevs1. apply not_mem_iff in Eevs. exfalso... }
      apply not_mem_iff in Eevs2.
      assert (add Y (remove X (union evs1 evs2)) [=] union (add Y (remove X evs1)) evs2) by fsetdec.
      rewrite H4.
      apply Sa_rcd_cons with (cm1:=cm1) (cm2:=cm2)...
      { simpl in IHSub2. rewrite !map_app in IHSub2... }
      { rewrite compose_cm_inv_1 with (evs1':= evs1). 
        2:{ apply empty_add_remove_mem... }
        auto.
      }
    + destruct (AtomSetImpl.mem X (union evs1 evs2)) eqn:Eevs.
      2:{ apply mem_iff in Eevs2. apply not_mem_iff in Eevs. exfalso... }
      apply not_mem_iff in Eevs1.
      assert (add Y (remove X (union evs1 evs2)) [=] union evs1 (add Y (remove X evs2))) by fsetdec.
      rewrite H4.
      apply Sa_rcd_cons with (cm1:=cm1) (cm2:=cm2)...
      { simpl in IHSub2. rewrite !map_app in IHSub2... }
      { rewrite compose_cm_inv_2 with (evs2':= evs2).
        2:{ apply empty_add_remove_mem... }
        auto.
      }
    + destruct (AtomSetImpl.mem X (union evs1 evs2)) eqn:Eevs.
      { apply not_mem_iff in Eevs1. apply not_mem_iff in Eevs2. apply mem_iff in Eevs.
        apply union_iff in Eevs. destruct Eevs; exfalso... }
      apply not_mem_iff in Eevs1. apply not_mem_iff in Eevs2. apply not_mem_iff in Eevs.
      apply Sa_rcd_cons with (cm1:=cm1) (cm2:=cm2)...
      { simpl in IHSub2. rewrite !map_app in IHSub2... }

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
  - induction l.
    + exists emp...
    + inversion H2;subst.
      destruct IHl as [evs1 ?]...
      { inversion H4;subst... }
      { intros. apply H with (i:=i)... right... }
      { intros. apply H0 with (i:=i)... right... }
      { inversion H4;subst. apply WFS_rcd... intros. apply H6 with (i:=i)... }
      destruct a as [l1 T1].
      destruct H0 with (E:=E) (i:=l1) (T:=T1) (im:=im) as [evs2 ?]...
      { apply H6 with (i:=l1)... }
      exists (union evs2 evs1)...
      rewrite_alist (nil ++ l1 ~ T1 ++ l). inversion H4;subst.
      apply Sa_rcd_cons with (cm1:=Eq) (cm2:=Eq)...
Qed.


Theorem Msub_refl_equiv_aux: forall E im A B,
    wf_env E -> WFS E A -> WFS E B -> equiv A B -> exists evs, Sub im Eq evs E A B /\ Sub im Eq evs E B A.
Proof with auto.
  intros. generalize dependent im. generalize dependent E. induction H2;intros...
  - exists emp...
  - exists emp...
  - inversion H1;subst. destruct im, im0.
    + exists emp...
    + exists (singleton X)...
    + exists (singleton X)...
    + exists emp...
  - inversion H1;subst. inversion H0;subst. 
    destruct IHequiv1 with (im:=flip_im im) (E:=E) as [evs1 ?], IHequiv2 with (im:=im) (E:=E) as [evs2 ?]...
    destruct_hypos.
    exists (union evs1 evs2)... split.
    + apply Sa_arrow with (cm1:=Eq) (cm2:=Eq)...
    + apply Sa_arrow with (cm1:=Eq) (cm2:=Eq)...
  - 
    inversion H2;subst. inversion H3;subst.
    assert (Hfv: fv_tt (typ_mu A) [=] fv_tt (typ_mu B)).
    { apply equiv_fv_tt with (E:=E)... apply eqv_mu with (L:=L)... }
    pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0. specialize_x_and_L X L1.
    (* need to decide whether X is in evs of (open_tt T X), so we need replacing_var lemma *)
    destruct H0 with (im:=im) (E:=X ~ bind_sub im ++ E) as [evs1 ?]...
    { rewrite_alist (nil ++ X ~ bind_sub im ++ E). apply WFS_im_inv with (im1:=im0)... }
    { rewrite_alist (nil ++ X ~ bind_sub im ++ E). apply WFS_im_inv with (im1:=im1)... }
    destruct_hypos.
    exists (if AtomSetImpl.mem X evs1 then (remove X evs1) \u fv_tt A else evs1)...
    destruct (AtomSetImpl.mem X evs1) eqn:Evs1.
    + apply mem_iff in Evs1.
      split.
      * apply Sa_rec_eq_in with (L:=L \u {{X}} \u evs1 \u dom E).
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
      * simpl in Hfv. rewrite Hfv.
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
      split.
      * apply Sa_rec_eq_notin with (L:=L \u {{X}} \u evs1 \u dom E).
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
      * apply Sa_rec_eq_notin with (L:=L \u {{X}} \u evs1 \u dom E).
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
  - generalize dependent l2. induction l1;intros.
    + 
      destruct l2. { exists emp... }
      { simpl in H. destruct p. specialize (H a). fsetdec. }
    + 
      destruct a.
      assert (binds a t ((a,t)::l1))...
      apply binds_In in H5. rewrite H in H5.
      apply binds_In_inv in H5. destruct_hypos.
      apply binds_split in H5. destruct H5 as (l2a & l2b & ?).
      subst.
      destruct IHl1 with (l2:=l2b++l2a)...
      { inversion H3;subst... apply WFS_rcd... inversion H6... intros. apply H8 with (i:=i)... }
      { simpl in H. rewrite dom_app in H. simpl in H.
        rewrite KeySetProperties.union_sym in H.
        rewrite KeySetProperties.union_add in H.
        apply dom_add_drop with (a0:=a) (t1:=t) (t2:=x)...
        { inversion H3... }  { inversion H4;subst.
          constructor...
          { rewrite cons_app_one in H6. apply uniq_remove_mid in H6... }
          { rewrite dom_app. apply notin_union_3.
            apply fresh_mid_head in H6...
            apply fresh_mid_tail in H6... }
        }
        rewrite dom_app. fsetdec.
      }
      { intros. apply H0 with (i:=i)... }
      { intros. apply H1 with (i:=i)... }
      { inversion H4;subst. apply WFS_rcd.
        { rewrite cons_app_one in H6. apply uniq_remove_mid in H6... }
        intros. apply H8 with (i:=i)... analyze_binds H5. }
      destruct H1 with (im:=im)(i:=a) (T1:=t) (T2:=x) (E:=E) as [evs1 ?]...
      { inversion H3;subst. apply H9 with (i:=a)... }
      { inversion H4;subst. apply H9 with (i:=a)... }
      destruct_hypos.
      exists (union evs1 x0)...
      split.
      * rewrite_alist (nil ++ a ~ t ++ l1). apply Sa_rcd_cons with (cm1:=Eq) (cm2:=Eq)...
        { inversion H3;subst. inversion H10;subst... }
        { inversion H4;subst. rewrite dom_app.
          rewrite cons_app_one in H10. apply notin_union_3.
          { apply fresh_mid_head in H10... }
          { apply fresh_mid_tail in H10... }
        }
      * rewrite_alist (nil ++ a ~ t ++ l1). apply Sa_rcd_cons with (cm1:=Eq) (cm2:=Eq)...
        { inversion H4;subst. rewrite dom_app.
          rewrite cons_app_one in H10. apply notin_union_3.
          { apply fresh_mid_head in H10... }
          { apply fresh_mid_tail in H10... }
        }
        { inversion H3;subst. inversion H10;subst... }
Qed.


Theorem Msub_refl_equiv: forall E im A B,
    wf_env E -> WFS E A -> WFS E B -> equiv A B -> exists evs, Sub im Eq evs E A B.
Proof with auto.
  intros. destruct Msub_refl_equiv_aux with (E:=E) (im:=im) (A:=A) (B:=B) as [evs ?]...
  exists evs. destruct_hypos...
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
    typePairR (typ_mu A) (typ_mu B)
| tp_rcd: forall l1 l2,
    type (typ_rcd l1) ->
    type (typ_rcd l2) ->
    (forall l A B, binds l A l1 -> binds l B l2 -> typePairR A B) ->
    typePairR (typ_rcd l1) (typ_rcd l2)
.

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




Lemma subst_reverse_equiv: forall A B X C D,
    typePairR A B -> type (typ_mu C) -> type (typ_mu D) ->
    equiv (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B) ->
    (equiv (typ_mu C) (typ_mu D) \/ (X \notin fv_tt A \u fv_tt B)) /\ (equiv A B).
Proof with auto.
  intros. revert C D H0 H1 H2. induction H;intros;simpl in *...
  - destruct A;simpl in *;try solve [inversion H2]...
    destruct (a == X);try solve [inversion H2].
  - destruct A;simpl in *;try solve [inversion H2]...
    destruct (a == X);try solve [inversion H2].
  - destruct (X0 == X)...
  - inversion H3;subst.
    apply equiv_symm in H7. apply IHtypePairR1 in H7...
    apply IHtypePairR2 in H9...
    destruct_hypos. apply equiv_symm in H7. destruct H6, H4;subst;try solve [apply equiv_symm in H6;auto]...
  - 
    inversion H3;subst.
    split...
    { pick_fresh X0. specialize_x_and_L X0 L.
      destruct H0 with (C:=C) (D:=D)...
      { specialize_x_and_L X0 L0.
        rewrite subst_tt_open_tt_var in H6...
        rewrite subst_tt_open_tt_var in H6...
      }
      destruct H4... right.
      intros Hc. apply union_iff in Hc. destruct Hc.
      { apply in_open with (Y:=X0) in H7... }
      { apply in_open with (Y:=X0) in H7... }
    }
    { apply eqv_mu with (L:=L \u L0 \u {{ X }}). intros.
      specialize_x_and_L X0 L.
      destruct H0 with (C:=C) (D:=D)...
      { specialize_x_and_L X0 L0.
        rewrite subst_tt_open_tt_var in H6...
        rewrite subst_tt_open_tt_var in H6...
      }
    }
  -
    inversion H5;subst.
    rewrite !dom_map in H8.
    split...
    { generalize dependent l2. induction l1;intros.
      + destruct l2. { right. simpl. fsetdec. }
        { destruct p. simpl in H8. hnf in H8. exfalso. specialize (H8 a). fsetdec. }
      + destruct a.
        assert (binds a t ((a, t) :: l1))...
        apply binds_In in H6. rewrite H8 in H6.
        apply binds_In_inv in H6. destruct_hypos.
        apply binds_split in H6. destruct H6 as (l2a & l2b & ?). subst.
        assert (Hdom: dom l1 [=] dom (l2b ++ l2a)).
        { apply dom_add_drop with (a0:=a) (t1:=t) (t2:=x)...
          { inversion H;subst... }
          { inversion H0;subst...
            apply uniq_reorder_2... }
          rewrite !dom_app in *.
          simpl in H8. fsetdec.
        } 
        destruct IHl1 with (l2:=l2b++l2a)...
        { inversion H;subst. apply type_rcd...
          { inversion Huniq... }
          intros. apply H7 with (i:=i)... }
        { inversion H0;subst. apply type_rcd.
          { apply uniq_remove_mid with (F:=a~x)... }
          intros. apply H7 with (i:=i)... analyze_binds H6... }
        { intros. apply H1 with (l:=l)... }
        { intros. apply H2 with (l:=l)... }
        { inversion H5;subst. apply eqv_rcd...
          { rewrite !dom_map. simpl in H10. rewrite !dom_map in H10... }
          { intros. apply H11 with (i:=i)...
            rewrite map_app in H7. rewrite map_app. simpl. analyze_binds H7. }
        }
        (* needs WFS to ensure uniq label *)
        { intros. apply H9 with (i:=i);simpl...
          rewrite map_app in *. simpl. analyze_binds H7... }
        {  destruct (H2 a t x) with (C:=C) (D:=D)...
          { apply H9 with (i:=a)... }
          { destruct H7... right. repeat apply notin_union_3...
            rewrite !List.map_app.
            rewrite fold_union_app3. simpl. 
            apply notin_union_3...
            apply notin_union in H6. destruct H6.
            rewrite List.map_app in H11.
            rewrite fold_right_union_app in H11...
        }
        }
    }
    {
      apply eqv_rcd...
      intros. destruct (H2 i T1 T2) with (C:=C) (D:=D)...
      apply H9 with (i:=i)...
    }
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
  - apply tp_rcd.
    { constructor... intros. inversion H0. }
    { constructor... intros. inversion H0. }
    { intros. inversion H0. }
  - apply tp_rcd...
    { constructor... intros. apply WFS_type with (E:=E). apply H2 with (l:=i)... }
    { constructor... intros. inversion H3. }
    { intros. inversion H4. }
  - 
    assert (Hu1: uniq (tys1 ++ tys1'))...
    { get_well_form. inversion H2... }
    assert (Hu2: uniq (tys2 ++ tys2'))...
    { get_well_form. inversion H3... }


    apply tp_rcd...
    { get_type... inversion H2;subst. apply type_rcd... intros.
      analyze_binds_uniq H6.
      + apply H7 with (i:=i)...
      + apply H7 with (i:=i)...
    }
    { get_type... inversion H3;subst. apply type_rcd... intros.
      analyze_binds_uniq H6.
      + apply H7 with (i:=i)...
      + apply H7 with (i:=i)...
    }
    intros.
    inversion IHSub2;subst.
    analyze_binds_uniq H2.
    + apply H8 with (l:=l0)... analyze_binds_uniq H3.
    + analyze_binds_uniq H3.
    + apply H8 with (l:=l0)... analyze_binds_uniq H3.
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
    apply equiv_symm...
  -
    apply pos_rcd... intros...
    apply H2 with (l:=l)...

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
  -
    apply pos_rcd...
    intros.
    apply H2 with (l:=l)...
    apply fv_tt_rcd_field in H4.
    apply fv_tt_rcd_field in H5.
    rewrite H4. rewrite H5...
Qed.


Theorem posvar_self_notin_equiv: forall (A B: typ) (m : IsoMode) (X : atom),
    type A -> type B -> X `notin` fv_tt A -> X `notin` fv_tt B ->
    equiv A B ->
    posvar m X A B.
Proof with auto.
  intros. generalize dependent m.
  induction H3;intros...
  - constructor... simpl in H1...

  -
    inversion H;subst.
    inversion H0;subst. simpl in H1. simpl in H2.
    constructor...
    +
      apply posvar_comm.
      apply IHequiv1...

  -
    inversion H;subst.
    inversion H0;subst.
    apply pos_rec_t with (L:=L \u L0 \u L1)...
    (* { intros. specialize_x_and_L Y L0. apply WFS_type in H7... }
    { intros. specialize_x_and_L Y L1. apply WFS_type in H8... } *)
    apply eqv_mu with (L:=L \u L0 \u L1)...
  -
    apply pos_rcd...
    (* { get_type... }
    { get_type... } *)
    intros.
    apply H5 with (i:=l)...
    { inversion H;subst. apply H9 with (i:=l)... }
    { inversion H0;subst. apply H9 with (i:=l)... }
    { apply fv_tt_rcd_field in H6... }
    { apply fv_tt_rcd_field in H7... }
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
        inversion H5;subst.
        apply pos_rec with (L:=L \u L0 \u L1 \u L2 \u {{X}} \u {{X0}}  \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          eapply posvar_self_notin_equiv...
          { apply notin_fv_tt_open_aux... }
          { apply notin_fv_tt_open_aux... }

        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          apply pos_rename_3 with (X:=X0) (m:=m4)...
      *
        inversion H7;subst.
        apply pos_rec with (L:=L \u L0 \u L1 \u L2 \u {{X}} \u {{X0}}  \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          eapply posvar_self_notin_equiv...
          { apply notin_fv_tt_open_aux...  }
          { apply notin_fv_tt_open_aux...  }
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          eapply posvar_self_notin_equiv...
          { apply notin_fv_tt_open_aux...  }
          { apply notin_fv_tt_open_aux...  }
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
        inversion H5;subst.
        apply pos_rec with (L:=L \u L0 \u L1 \u L2 \u {{X}} \u {{X0}}  \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          eapply H0 with (m2:=m0) (m4:=m4) (X0:=X) (m1:=m)...
          eapply posvar_self_notin_equiv...
          { apply notin_fv_tt_open_aux...  }
          { apply notin_fv_tt_open_aux...  }
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          apply pos_rename_3 with (X:=X0) (m:=m4)...
      *
        inversion H7;subst.
        apply pos_rec with (L:=L \u L0 \u L1 \u L2 \u {{X}} \u {{X0}}  \u fv_tt B \u fv_tt C \u fv_tt D).
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          eapply H0 with (m2:=m0) (m4:=m4) (X0:=X) (m1:=m)...
          eapply posvar_self_notin_equiv...
          { apply notin_fv_tt_open_aux... }
          { apply notin_fv_tt_open_aux... }
        --
          intros.
          rewrite subst_tt_open_tt_var...
          rewrite subst_tt_open_tt_var...
          apply H0 with (m2:=m0) (m4:=m4)...
          eapply posvar_self_notin_equiv...
          { apply notin_fv_tt_open_aux... }
          { apply notin_fv_tt_open_aux... }
          apply pos_rename_3 with (X:=X0) (m:=m4)...
      *
        rewrite <- subst_tt_fresh...
        rewrite <- subst_tt_fresh...
        apply pos_rec_t with (L:=L1)...
  -
    split.
    +
      simpl...
      apply pos_rcd.
      { apply subst_tt_type with (Z:=Y) (P:=C) in H... apply posvar_regular in H6. destruct_hypos... }
      { apply subst_tt_type with (Z:=Y) (P:=D) in H0... apply posvar_regular in H6. destruct_hypos... }
      intros.
      apply binds_map_3 in H8. apply binds_map_3 in H9.
      destruct_hypos. subst.
      inversion H3;subst. inversion H4;subst.
      specialize (H16 _ _ _ H11 H10).
      specialize (H19 _ _ _ H11 H10).
      destruct (H2 _ _ _ H11 H10 _ _ _ _ _ _ _ H16 H19 H5 H6)...
    +
      simpl...
      apply pos_rcd.
      { apply subst_tt_type with (Z:=Y) (P:=C) in H... apply posvar_regular in H6. destruct_hypos... }
      { apply subst_tt_type with (Z:=Y) (P:=D) in H0... apply posvar_regular in H6. destruct_hypos... }
      intros.
      apply binds_map_3 in H8. apply binds_map_3 in H9.
      destruct_hypos. subst.
      inversion H3;subst. inversion H4;subst.
      specialize (H16 _ _ _ H11 H10).
      specialize (H19 _ _ _ H11 H10).
      destruct (H2 _ _ _ H11 H10 _ _ _ _ _ _ _ H16 H19 H5 H6)...
Qed.        


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
  -
    apply Sa_rcd_lt...
    intros. apply H2 in H4...
  -
    apply Sa_rcd_cons with (cm1:=cm1) (cm2:=cm2)...
  - rewrite <- H0. apply IHSub...
Qed.



Lemma bind_typ_WFS: forall X E A t, 
  wf_env E ->
  WFS E A -> binds X (bind_typ t) E ->
  X `notin` fv_tt A.
Proof with auto.
  intros.
  induction H0...
  - destruct (X == X0)... subst.
    apply uniq_from_wf_env in H.
    pose proof binds_unique _ _ _ _ _ H1 H0 H.
    inversion H2.
  - pick_fresh Y. specialize_x_and_L Y L.
    apply rename_env_open in H2...
  - 
    induction T...
    destruct a. simpl.
    apply notin_union_3.
    { apply H3 with (i:=a)... }
    { inversion H0;subst. apply IHT...
      + intros. apply H2 with (i:=i)...
      + intros. apply H3 with (i:=i)... }
Qed.



Lemma bind_typ_Sub: forall X E evs im cm A B t, 
  Sub im cm evs E A B -> binds X (bind_typ t) E ->
  X `notin` fv_tt A /\ X `notin` fv_tt B.
Proof with auto.
  intros.
  induction H...
  - 
    apply bind_typ_WFS with (X:=X) (t:=t) in H1...
  -
    destruct (X == X0)... subst.
    apply uniq_from_wf_env in H.
    pose proof binds_unique _ _ _ _ _ H1 H0 H.
    inversion H2.
  -
    destruct (X == X0)... subst.
    apply uniq_from_wf_env in H.
    pose proof binds_unique _ _ _ _ _ H1 H0 H.
    inversion H2.
  -
    pick_fresh Y. specialize_x_and_L Y L.
    destruct H1...
    apply rename_env_open in H1...
    apply rename_env_open in H2...
  -
    pick_fresh Y. specialize_x_and_L Y L.
    destruct H1...
    apply rename_env_open in H1...
    apply rename_env_open in H2...
  -
    pick_fresh Y. specialize_x_and_L Y L.
    destruct H1...
    apply rename_env_open in H1...
    apply rename_env_open in H2...
  -
    induction tys...
    destruct a. destruct tys.
    { simpl. assert (WFS E t0). { apply H3 with (l:=a)... }
      apply bind_typ_WFS with (X:=X) (t:=t) in H4... }
    destruct IHtys...
    { intros C. inversion C. }
    { inversion H1... }
    { intros. apply H3 with (l:=l)... }
    { simpl in H4. simpl... split... 
      assert (WFS E t0). { apply H3 with (l:=a)... }
      apply bind_typ_WFS with (X:=X) (t:=t) in H6...
    }
  -
    destruct IHSub1... destruct IHSub2...
    cbn [fv_tt]. rewrite !List.map_app.
    rewrite !fold_union_app3...
    simpl. split...
    { apply notin_union_3...
      simpl in H5. rewrite List.map_app in H5. rewrite fold_right_union_app in H5... }
    { apply notin_union_3...
      simpl in H6. rewrite List.map_app in H6. rewrite fold_right_union_app in H6... }
Qed.


Lemma bind_ex_evs: forall X E evs im cm A B, 
  Sub im cm evs E A B ->  X `in` evs ->
  (exists im_x, binds X (bind_sub im_x) E).
Proof with auto.
  intros. generalize dependent X.
  induction H;intros;try solve [exfalso;fsetdec]...
  -
    assert (X0 = X) by fsetdec. subst. exists (flip_im im)...
  -
    apply union_iff in H2. destruct H2.
    +
      apply IHSub1 in H2...
    +
      apply IHSub2 in H2...
  -
    pick_fresh X'. specialize_x_and_L X' L.
    apply H0 in H1... destruct H1.
    analyze_binds H1...
    exists x...
  -
    pick_fresh X'. specialize_x_and_L X' L.
    apply H0 in H1... destruct H1.
    analyze_binds H1...
    exists x...
  -
    assert (Sub im Eq (evs \u fv_tt A1) E (typ_mu A1) (typ_mu A2))...
    { apply Sa_rec_eq_in with (L:=L)... }
    pick_fresh X'. specialize_x_and_L X' L.
    apply union_iff in H1. destruct H1.
    +
      destruct (H0 X)... analyze_binds H3. exists x...
    +
      get_well_form... pose proof WFS_dom _ _ H3. simpl in H7.
      destruct (binds_In_inv _ X E)... destruct x. exists  i...
      { apply bind_typ_WFS with (X:=X) (t:=t) in H3... exfalso... }
  -
    apply union_iff in H2. destruct H2.
    +
      apply IHSub1 in H2...
    +
      apply IHSub2 in H2...

  -
    rewrite <- H0 in H1...
Qed.


Lemma notin_fv_subst_strong: forall X A B,
    X \notin fv_tt A ->
    X \notin fv_tt (subst_tt X A B).
Proof with auto.
  intros.
  induction B using typ_rec' ...
  -
    simpl.
    destruct (x == X)...
Qed.



(* Lemma open_tt_fresh_equiv_inv: forall A B X,
  type (typ_mu A) -> type (typ_mu B) ->
  X `notin` fv_tt A ->
  X `notin` fv_tt B ->
  equiv (open_tt A X) (open_tt B X) ->
  equiv A B.
Proof with auto.
  unfold open_tt. generalize 0.
  intros n A B X typA typB fvA fvB Heqv.
  generalize dependent B. generalize dependent X.
  revert n.
  induction A using typ_rec';intros...
  - induction B;inversion Heqv...
    destruct (n == n0);inversion H.
  - induction B;inversion Heqv...
    destruct (n == n0);inversion H.
  - simpl in Heqv.
    destruct (n0 == n).
    + induction B;inversion Heqv...
      { destruct (n0 == n1);inversion H;subst...
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
Qed. *)



Lemma generalized_unfolding_lemma:
  forall E1 E2 C D A B X im im_x evs cm,
    wf_env (E1 ++ E2) -> X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2) \u evs ->
    Sub im cm evs (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    well_bind_env im (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
    forall cm',
    Sub im_x cm' emp E2 ( (mode_choose im im_x C D)) ( (mode_choose im im_x D C)) ->
    exists cm'' evs'', (Sub im cm'' evs'' (E1 ++ E2) (subst_tt X ( C) A) (subst_tt X ( D) B)).
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
    simpl. destruct (subst_tt X C A == typ_top).
    + exists Eq, emp. rewrite e. apply Sa_top_eq...
    + exists Lt, emp. apply Sa_top_lt...
      apply subst_tt_wfs2 with (im:=im_x)...
      { get_well_form. add_nil. apply WFS_weakening. destruct im, im_x... }

  -
    (* Var pos *)
    simpl. destruct (X0 == X)...
    +
      (* X0 == X *)
      subst. analyze_binds_uniq H0. inversion BindsTacVal;subst.
      exists cm', emp. destruct im_x;simpl in H3...
      { add_nil. apply sub_weakening... }
      { add_nil. apply sub_weakening... }
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
      (* apply well_bind_env_fvar_x with (im_x:=im_x) in H2...
      subst... destruct im_x;inversion BindsTacVal. *)
      (* contradiction on the global invariant evs constraint *)
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
    { destruct im, im_x; simpl in H2;simpl... }
    
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
        assert (exists im_x', binds X' (bind_sub im_x') (E1 ++ E2)).
        { apply bind_ex_evs with (X:=X') in IHSub2'... }
        destruct H4 as [im_x' H4].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub2' X' im_x' Eempty.
        exfalso. apply H6...
        
        apply posvar_calc_sign with (m2:=mode_xor im im_x) (m4:=im_x) ...
        - apply Sub_typePairR in H1_0...
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
          pose proof notin_fv_subst_strong X D B2. fsetdec.
      + destruct (AtomSetImpl.is_empty evs1') eqn:Eempty; try solve [inversion H5].
        apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
        destruct Eempty as [X' Eempty].
        assert (exists im_x', binds X' (bind_sub im_x') (E1++E2)).
        { apply bind_ex_evs with (X:=X') in IHSub1'... }
        destruct H4 as [im_x' H4].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub1' X' im_x' Eempty.
        exfalso. apply H6...
        apply posvar_calc_sign with (m2:=mode_xor (flip_im im) im_x) (m4:=im_x) ...
        - apply Sub_typePairR in H1_...
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
          apply sub_evs_fv in IHSub1'...
          destruct_hypos.
          pose proof notin_fv_subst_strong X D B1. fsetdec.
    }

    exists c, (union evs1' evs2').
    apply Sa_arrow with (cm1:=cm1') (cm2:=cm2')...
  
  -
    (* rec-lt *)
    simpl.
    assert (Ewf: Sub im Lt evs (E1 ++ X ~ bind_sub im_x ++ E2) (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_lt with (L:=L)... }

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
        { 
          inversion H15;subst.
          (* rename the pos argument *)
          pick_fresh Z. specialize_x_and_L Z L1.
          rewrite subst_tt_intro with (X:=Z)...
          rewrite subst_tt_intro with (X:=Z) (T2:=A2)...
          apply pos_rename_fix...
          apply posvar_self_notin_equiv...
          (* { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
            rewrite subst_tt_intro with (X:=Z)...
            apply subst_tt_type... } *)
          { apply notin_fv_tt_open_aux... }
          { apply notin_fv_tt_open_aux... }
        }
      }
    }
    rewrite <- subst_tt_open_tt_var in IHSub1'... 2:{ get_type. destruct im, im_x... }
    rewrite <- subst_tt_open_tt_var with (P:=( D)) in IHSub1'... 
    2:{ get_type. destruct im, im_x... }
    destruct cm1'. 2:{ (* TODO: contradiction on Lt/Eq 
    
    !!!! may relies on syntactic equality??

     (subst_tt X (typ_mu C) A1) = (subst_tt X (typ_mu D) A2)
     => A1 = A2
     contradict on H1
    
    *)
      exists Eq.
      apply Msub_refl_equiv...
      { get_well_form. replace (typ_mu (subst_tt X C A1)) with (subst_tt X C (typ_mu A1))...
        apply subst_tt_wfs2 with (im:=im_x)...
        add_nil. apply WFS_weakening... destruct im,im_x... }
      { get_well_form. replace (typ_mu (subst_tt X D A2)) with (subst_tt X D (typ_mu A2))...
        apply subst_tt_wfs2 with (im:=im_x)...
        add_nil. apply WFS_weakening... destruct im,im_x... }

      apply Msub_refl_inv in IHSub1'...
      apply eqv_mu with (L:=L \u  {{ X'}})... intros.
      rewrite subst_tt_intro with (X:=X') (T2:=subst_tt X C A1)...
      2:{ apply notin_fv_subst... }
      rewrite subst_tt_intro with (X:=X') (T2:=subst_tt X D A2)...
      2:{ apply notin_fv_subst... }
      apply equiv_rename_fix...
    }
    
    { exists Lt, evs1'. apply Sa_rec_lt with (L:= L \u {{X}} \u {{X' }}\u dom (E1 ++ E2)).
      intros.  
      replace evs1' with (if AtomSetImpl.mem X' evs1' then AtomSetImpl.add X0 (remove X' evs1') else evs1')...
      2:{ destruct (AtomSetImpl.mem X' evs1') eqn:Eevs...
          apply mem_iff in Eevs.
          pose proof posvar_false_simpl _ _ _ _ _ _ IHSub1' X' im Eevs.
          exfalso. apply H6... rewrite xor_prop_refl.
          rewrite subst_tt_open_tt_var... 2:{ get_type. destruct im, im_x... }
          rewrite subst_tt_open_tt_var... 2:{ get_type. destruct im, im_x... }
          apply posvar_calc_sign with (m2:=mode_xor im im_x) (m4:=Pos)...
          + apply Sub_typePairR in H1...
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
              apply posvar_self_notin_equiv...
              { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
                rewrite subst_tt_intro with (X:=Z)...
                apply subst_tt_type... }
              { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
                rewrite subst_tt_intro with (X:=Z)...
                apply subst_tt_type... }
              { apply notin_fv_tt_open_aux... }
              { apply notin_fv_tt_open_aux... }
              inversion H16;subst. pick_fresh Z.
              specialize_x_and_L Z L1.
              rewrite subst_tt_intro with (X:=Z) (T2:=A1)...
              rewrite subst_tt_intro with (X:=Z) (T2:=A2)...
              apply equiv_rename_fix...
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
        { 
          apply posvar_self_notin_equiv...
          { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
            rewrite subst_tt_intro with (X:=Z)...
            apply subst_tt_type... }
          { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
            rewrite subst_tt_intro with (X:=Z)...
            apply subst_tt_type... }
          { apply notin_fv_tt_open_aux... }
          { apply notin_fv_tt_open_aux... }
          inversion H15;subst. pick_fresh Z.
          specialize_x_and_L Z L1.
          rewrite subst_tt_intro with (X:=Z) (T2:=A1)...
          rewrite subst_tt_intro with (X:=Z) (T2:=A2)...
          apply equiv_rename_fix...
        }
      }
    }
    {
      destruct cm1'.
      +
        exists Lt, evs1'. apply Sa_rec_lt with (L:= L \u {{X}} \u {{X' }}\u dom (E1 ++ E2)).
        intros.
        rewrite_alist (nil ++ X0 ~ bind_sub im ++ E1 ++ E2).
        replace evs1' with (if AtomSetImpl.mem X' evs1' then AtomSetImpl.add X0 (remove X' evs1') else evs1')...
        apply sub_replacing_var...
        { rewrite subst_tt_open_tt_var... 2:{ get_type. destruct im, im_x... }
          rewrite subst_tt_open_tt_var... { get_type. destruct im, im_x... }
        }
        { solve_notin... }
        { constructor...  }
        {
          destruct (AtomSetImpl.mem X' evs1') eqn:Ex'...
          apply mem_iff in Ex'.
          pose proof posvar_false_simpl _ _ _ _ _ _ IHSub1' X' im Ex'.
          exfalso. apply H6... rewrite xor_prop_refl.
          apply posvar_calc_sign with (m2:=mode_xor im im_x) (m4:=Pos)...
          + apply Sub_typePairR in H1...
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
              apply posvar_self_notin_equiv...
              { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
                rewrite subst_tt_intro with (X:=Z)...
                apply subst_tt_type... }
              { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
                rewrite subst_tt_intro with (X:=Z)...
                apply subst_tt_type... }
              { apply notin_fv_tt_open_aux... }
              { apply notin_fv_tt_open_aux... }
              inversion H16;subst. pick_fresh Z.
              specialize_x_and_L Z L1.
              rewrite subst_tt_intro with (X:=Z) (T2:=A1)...
              rewrite subst_tt_intro with (X:=Z) (T2:=A2)...
              apply equiv_rename_fix...
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
      +
        exists Eq, evs1'. apply Sa_rec_eq_notin with (L:= L \u {{X}} \u {{X' }}\u dom (E1 ++ E2)).
        intros.
        rewrite_alist (nil ++ X0 ~ bind_sub im ++ E1 ++ E2).
        replace evs1' with (if AtomSetImpl.mem X' evs1' then AtomSetImpl.add X0 (remove X' evs1') else evs1')...
        apply sub_replacing_var...
        { rewrite subst_tt_open_tt_var... 2:{ get_type. destruct im, im_x... }
          rewrite subst_tt_open_tt_var... { get_type. destruct im, im_x... }
        }
        { solve_notin... }
        { constructor...  }
        {
          destruct (AtomSetImpl.mem X' evs1') eqn:Ex'...
          apply mem_iff in Ex'.
          pose proof posvar_false_simpl _ _ _ _ _ _ IHSub1' X' im Ex'.
          exfalso. apply H6... rewrite xor_prop_refl.
          apply posvar_calc_sign with (m2:=mode_xor im im_x) (m4:=Pos)...
          + apply Sub_typePairR in H1...
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
              apply posvar_self_notin_equiv...
              { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
                rewrite subst_tt_intro with (X:=Z)...
                apply subst_tt_type... }
              { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
                rewrite subst_tt_intro with (X:=Z)...
                apply subst_tt_type... }
              { apply notin_fv_tt_open_aux... }
              { apply notin_fv_tt_open_aux... }
              inversion H16;subst. pick_fresh Z.
              specialize_x_and_L Z L1.
              rewrite subst_tt_intro with (X:=Z) (T2:=A1)...
              rewrite subst_tt_intro with (X:=Z) (T2:=A2)...
              apply equiv_rename_fix...
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
    }
  -
    (* rec-eq-notin *)
    assert (Ewf: Sub im Eq (evs `union` fv_tt A1) (E1 ++ X ~ bind_sub im_x ++ E2) (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_eq_in with (L:=L)... }
    pose proof Ewf as Ewf'.
    pick_fresh X'.
    specialize_x_and_L X' L.
    exists Eq.
    apply Msub_refl_equiv...
    { get_well_form... 
      apply subst_tt_wfs2 with (im:=im_x)...
      add_nil. apply WFS_weakening... destruct im,im_x...
    }
    { get_well_form... 
      apply subst_tt_wfs2 with (im:=im_x)...
      add_nil. apply WFS_weakening... destruct im,im_x...
    }

    
    apply Msub_refl_inv in Ewf... simpl.
    rewrite <- subst_tt_fresh... rewrite <- subst_tt_fresh...
    { apply equiv_fv_tt with (E:=E1 ++ X ~ bind_sub im_x ++ E2) in Ewf... simpl in Ewf. rewrite <- Ewf...
      { get_well_form... } { get_well_form... } }


  -
    (* rcd nil *)
    exists Eq, emp...
  -
    (* rcd nil cons *)
    exists Lt, emp...
    simpl. apply Sa_rcd_lt...
    { destruct tys... intros C'. inversion C'. }
    { intros. apply binds_map_3 in H7. destruct_hypos.
      subst. apply subst_tt_wfs2 with (im:=im_x)...
      { add_nil. apply WFS_weakening. destruct im, im_x;get_well_form... }
      { apply H2 with (l:=l)... }
    }

  -
    (* rcd cons cons *)
    simpl. rewrite map_app. rewrite map_app. simpl. 

    destruct (IHSub1) with (im_x0:=im_x) (cm':=cm') (X0:=X) (E3:=E2) (E4:=E1) (D:=D) (C:=C) as [cm1' [evs1' IHSub1']] ...
    { hnf in H2. hnf. intros.
      apply H2 in H4. inversion H4;subst...
      destruct im, im_x0; simpl in H11;simpl;
      apply H11 with (l0:=l)...
    }
    destruct (IHSub2) with (im_x0:=im_x) (cm':=cm') (X0:=X) (E3:=E2) (E4:=E1) (D:=D) (C:=C) as [cm2' [evs2' IHSub2']]...
    { hnf in H2. hnf. intros.
      apply H2 in H4. inversion H4;subst...
      apply pos_rcd. { get_type... } { get_type... }
      intros. apply H11 with (l0:=l0)...
        analyze_binds H5...
        analyze_binds H6... }
    
          
    destruct ((compose_cm cm1' cm2' evs1' evs2')) eqn:Ecomp.
    2:{
      destruct cm1', cm2';inversion Ecomp.
      + destruct (AtomSetImpl.is_empty evs2') eqn:Eempty; try solve [inversion H5].
        apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
        destruct Eempty as [X' Eempty].
        assert (exists im_x', binds X' (bind_sub im_x') (E1 ++ E2)).
        { apply bind_ex_evs with (X:=X') in IHSub2'... }
        destruct H4 as [im_x' H4].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub2' X' im_x' Eempty.
        exfalso. apply H6...
        
        apply posvar_calc_sign with (m2:=mode_xor im im_x) (m4:=im_x) ...
        - apply Sub_typePairR in H1_0...
        - hnf in H2. specialize (H2 X' im_x').
          assert (binds X' (bind_sub im_x') (E1 ++ X ~ bind_sub im_x ++ E2))...
          specialize (H2 H7).
          inversion H2;subst...
          apply pos_rcd.  { get_type... } { get_type... }
          intros. apply H14 with (l0:=l0)...
            analyze_binds H8...
            analyze_binds H9...

        - hnf in H2. specialize (H2 X im_x).
          assert (binds X (bind_sub im_x) (E1 ++ X ~ bind_sub im_x ++ E2))...
          specialize (H2 H7).
          inversion H2;subst...
            apply pos_rcd. { get_type... } { get_type... }
            intros. apply H14 with (l0:=l0)...
              analyze_binds H8...
              analyze_binds H9...
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
          pose proof notin_fv_subst_strong X C (typ_rcd (tys1 ++ tys1')). fsetdec.
      + destruct (AtomSetImpl.is_empty evs1') eqn:Eempty; try solve [inversion H5].
        apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
        destruct Eempty as [X' Eempty].
        assert (exists im_x', binds X' (bind_sub im_x') (E1++E2)).
        { apply bind_ex_evs with (X:=X') in IHSub1'... }
        destruct H4 as [im_x' H4].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub1' X' im_x' Eempty.
        exfalso. apply H6...
        apply posvar_calc_sign with (m2:=mode_xor (im) im_x) (m4:=im_x) ...
        - apply Sub_typePairR in H1_...
        - hnf in H2. specialize (H2 X' im_x').
          assert (binds X' (bind_sub im_x') (E1 ++ X ~ bind_sub im_x ++ E2))...
          specialize (H2 H7).
          inversion H2;subst...
          apply H14 with (l0:=l)...
        - hnf in H2. specialize (H2 X im_x).
          assert (binds X (bind_sub im_x) (E1 ++ X ~ bind_sub im_x ++ E2))...
          specialize (H2 H7).
          inversion H2;subst...
          apply H14 with (l0:=l)...
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
          apply sub_evs_fv in IHSub1'...
          destruct_hypos.
          pose proof notin_fv_subst_strong X D (T2). fsetdec.
    }

    exists c, (union evs1' evs2').
    apply Sa_rcd_cons with (cm1:=cm1') (cm2:=cm2')...
    simpl in IHSub2'. rewrite !map_app in IHSub2'...
  



  -
    (* proper *)
    destruct (IHSub im_x X E2 E1) with (cm':=cm') (C:=C) (D:=D) as [cm1' [evs1' IHSub1']]...
    { rewrite H0... }
    exists cm1', evs1'...
Qed.


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
      nil nil (typ_mu A) (typ_mu B) (open_tt A X) (open_tt B X) X Pos Pos evs Lt
    ) with (cm':=Lt) ...
    { hnf. intros.
      apply soundness_posvar_simpl with (X:=X0) (im_x:=im_x) in H...
      analyze_binds H0. }
    { simpl. apply Sa_evs_proper with (evs := evs)... }
    destruct H0 as [evs' ?].

    destruct x.
    2:{

      apply Msub_refl_inv in H0...
      apply subst_reverse_equiv in H0...
      2:{ apply Sub_typePairR in H... }
      2:{ get_type... }
      2:{ get_type... }
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
Qed.


Lemma equiv_subst_tt: forall X A B C D,
  equiv A B ->
  equiv C D ->
  type C -> type D ->
  equiv (subst_tt X C A) (subst_tt X D B).
Proof with auto.
  intros. induction H...
  - simpl. destruct (X0 == X)...
  - simpl...
  - simpl... apply eqv_mu with (L:=L \u {{X}}).
    intros. specialize_x_and_L X L.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
  - simpl. apply eqv_rcd.
    { rewrite !dom_map... }
    intros. apply binds_map_3 in H5.
    apply binds_map_3 in H6.
    destruct_hypos.
    subst.
    apply H4 with (i:=i)...
Qed.




Lemma unfolding_lemma_eq :
  forall A B evs,
    Sub Pos Eq evs nil (typ_mu A) (typ_mu B) ->
    exists evs',
    Sub Pos Eq evs' nil (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Hq:=H).
  apply Msub_refl_inv in Hq.
  inversion Hq;subst...
  apply Msub_refl_equiv...
  { get_well_form... inversion H0;subst... pick_fresh X.
    replace (open_tt A (typ_mu A)) with (subst_tt X (typ_mu A) (open_tt A X))...
    2:{ rewrite subst_tt_open_tt... rewrite <- subst_tt_fresh... simpl. rewrite eq_dec_refl... get_type... }
    add_nil.
    apply subst_tt_wfs2 with (im:=im)... apply H5... 
  }
  { get_well_form... inversion H1;subst... pick_fresh Y.
    replace (open_tt B (typ_mu B)) with (subst_tt Y (typ_mu B) (open_tt B Y))...
    2:{rewrite subst_tt_open_tt... rewrite <- subst_tt_fresh... simpl. rewrite eq_dec_refl... get_type... }
    add_nil.
    apply subst_tt_wfs2 with (im:=im)... apply H5... }
  pick_fresh Z. rewrite subst_tt_intro with (X:=Z) (T2:=A)...
  rewrite subst_tt_intro with (X:=Z) (T2:=B)...
  apply equiv_subst_tt...
  { get_type... }
  { get_type... }
Qed.



(* Lemma unfolding_lemma_eq :
  forall A B evs,
    Sub Pos Eq evs nil (typ_mu A) (typ_mu B) ->
    evs [=] emp ->
    Sub Pos Eq emp nil (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Hq:=H).
  apply Msub_refl_inv in Hq.
  inversion Hq;subst...

  apply Msub_refl_equiv...
  { get_well_form... }
  { get_well_form... }


  pose proof Msub_refl empty Pos (open_tt B (typ_mu B))...
  assert (WFS empty (open_tt B (typ_mu B))).
  (* destruct H1...
  { get_type. inversion H2;subst... pick_fresh X.
    replace (open_tt B (typ_mu B)) with (subst_tt X (typ_mu B) (open_tt B X))...
    2:{rewrite subst_tt_open_tt... rewrite <- subst_tt_fresh... simpl. rewrite eq_dec_refl... }
    apply subst_tt_type; get_type...
  } *)
  { get_well_form. inversion H2;subst... pick_fresh X.
    replace (open_tt B (typ_mu B)) with (subst_tt X (typ_mu B) (open_tt B X))...
    2:{rewrite subst_tt_open_tt... rewrite <- subst_tt_fresh... simpl. rewrite eq_dec_refl... get_type... }
    add_nil.
    apply subst_tt_wfs2 with (im:=im)... apply H6... }
  destruct H1...
  { get_type... }
  assert (Hq':=H1).
  apply sub_evs_fv in H1.
  apply WFS_dom in H2.
  assert (x[=]emp) by fsetdec.
  rewrite H3 in Hq'...
Qed. *)
