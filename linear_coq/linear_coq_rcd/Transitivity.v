Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export LinearRule.



Ltac solve_by_inv H H1 := dependent destruction H;dependent destruction H1;auto.

Definition seq_cm cm1 cm2 :=
  match cm1, cm2 with
  | Eq, Eq => Eq
  | _, _ => Lt
  end.

Lemma seq_cm_lt1: forall cm, seq_cm Lt cm = Lt.
Proof.
  destruct cm;auto.
Qed.

Lemma seq_cm_lt2: forall cm, seq_cm cm Lt = Lt.
Proof.
  destruct cm;auto.
Qed.


Lemma trans_aux: forall B E,
    type B -> forall im A C evs1 evs2 cm1 cm2,
    Sub im cm1 evs1 E A B -> Sub im cm2 evs2 E B C -> 
    evs1 [=] emp -> evs2 [=] emp ->
    exists cm', Sub im cm' emp E A C.
Proof with auto.
  intros B E H. revert E.
  dependent induction H;intros;try solve [solve_by_inv H0 H|solve_by_inv H H0|solve_by_inv H0 H2]...
  - admit.
  - admit.
  - admit.
  - admit.
  -
    dependent induction H1;subst...
    +
      dependent induction H3;subst...
      *
        admit.
      *
        clear H2 H4.
        exists Lt.
        apply Sa_rec_lt with (L:=L \u L0 \u L1)...
        intros. specialize_x_and_L X L1.
        specialize_x_and_L X L0.
        specialize_x_and_L X L.
        destruct H0 with (im:=im) (A:=open_tt A1 X) (C:=open_tt A2 X)
        (evs1:=evs) (evs2:=evs0) (cm1:=Lt) (cm2:=Lt)
        (E:= X ~ bind_sub im ++ E)... destruct x...
        admit.
      * clear H2 H4.
Admitted.


Lemma trans_aux': forall B E,
    WFS E B -> forall im A C evs1 evs2,
    Sub im Lt evs1 E A B -> Sub im Lt evs2 E B C -> 
    evs1 [=] emp -> evs2 [=] emp ->
    Sub im Lt emp E A C.
Proof with auto.
  intros B E H.
  dependent induction H;intros;try solve [solve_by_inv H0 H|solve_by_inv H H0|solve_by_inv H0 H2]...
  -
    (* B = Top *)
    dependent induction H0;subst...
    { exfalso... }
    { rewrite <- H1 in *... }
  -
    (* B = Nat *)
    dependent induction H0;subst...
    +
      (* A <: nat <: Top *)
      dependent induction H;subst...
      { rewrite <- H0 in *... }
    +
      rewrite <- H1 in *...
  -
    (* B = X *)
    dependent induction H1;subst...
    +
      (* A <:  X <: Top *)
      dependent induction H0;subst...
      { rewrite <- H4 in *... apply IHSub with (X0:=X)... }
    +
      rewrite <- H2 in *... apply IHSub with (X0:=X)...
  -
    (* B = A -> B *)
    dependent induction H2;subst...
    +
      (* A0 < A -> B < Top *)
      dependent induction H1;subst...
      *
        (* A1 -> A2 < A -> B < Top *)
        apply Sa_top_lt...
        { get_well_form... } { intros C. inversion C. }
      *
        rewrite <- H5 in *... apply IHSub with (B0:=B) (A0:=A)...
    +
      (* A0 < A -> B < B1 -> B2 *)
      dependent induction H1;subst...
      *
        (* A1 -> A2 < A -> B < B1 -> B2 *)
        clear IHSub1. clear IHSub2. clear IHSub3. clear IHSub0.
        destruct cm0, cm3; try solve [inversion H1].
Admitted.

Lemma sub_eq_evs: forall im cm1 cm2 evs1 evs2 E A B,
    (* typePairR A B -> *)
    Sub im cm1 evs1 E A B -> 
    Sub im cm2 evs2 E A B ->
    evs1 [=] evs2 /\ cm1 = cm2.
Proof with auto.
  intros. generalize dependent evs2. generalize dependent cm2.
  induction H;intros...
  - dependent induction H0...
    + split... reflexivity.
    + rewrite <- H1. apply IHSub...
  - dependent induction H0...
    + split... reflexivity.
    + exfalso...
    + rewrite <- H1. apply IHSub...
  - dependent induction H2...
    + exfalso...
    + split... reflexivity.
    + rewrite <- H3. apply IHSub...
  - dependent induction H1...
    + split... reflexivity.
    + apply uniq_from_wf_env in H.
      pose proof binds_unique _ _ _ _ _ H0 H2 H.
      destruct im; inversion H3. 
    + rewrite <- H2. apply (IHSub X)...
  - dependent induction H1...
    + apply uniq_from_wf_env in H.
      pose proof binds_unique _ _ _ _ _ H0 H2 H.
      destruct im; inversion H3. 
    + split... reflexivity.
    + rewrite <- H2. apply IHSub...
  - dependent induction H2...
    + destruct (IHSub1 _ _ H2_).
      destruct (IHSub2 _ _ H2_0).
      subst. split.
      { rewrite H3, H5. reflexivity. }
      { destruct cm0, cm3; simpl in H2, H1; inversion H2; inversion H1; subst...
        * destruct (AtomSetImpl.is_empty evs3) eqn:Eevs3; try solve [inversion H2].
          destruct (AtomSetImpl.is_empty evs2) eqn:Eevs2; try solve [inversion H1].
          inversion H6; inversion H7...
        * destruct (AtomSetImpl.is_empty evs0) eqn:Eevs0; try solve [inversion H2].
          destruct (AtomSetImpl.is_empty evs1) eqn:Eevs1; try solve [inversion H1].
          inversion H6; inversion H7...
      }
    + rewrite <- H3. destruct IHSub with (A3:=A1) (A4:=A2) (B3:=B1) (B4:=B2) ...
  - dependent induction H1.
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      apply H0...
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      destruct H0 with (cm2:=Eq) (evs2:=evs0)...
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      destruct H0 with (cm2:=Eq) (evs2:=add X evs0)... inversion H4.
    +
      rewrite <- H2. destruct IHSub with (A3:=A1) (A4:=A2)...
  - dependent induction H1.
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      apply H0...
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      destruct H0 with (cm2:=Eq) (evs2:=evs0)...
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      destruct H0 with (cm2:=Eq) (evs2:=add X evs0)... exfalso. fsetdec.
    +
      rewrite <- H2. destruct IHSub with (A3:=A1) (A4:=A2)...
  - dependent induction H1.
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      destruct H0 with (cm2:=Lt) (evs2:=evs0)... inversion H4.
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      destruct H0 with (cm2:=Eq) (evs2:=evs0)... exfalso. fsetdec.
    +
      pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
      destruct H0 with (cm2:=Eq) (evs2:=add X evs0)... split...
      assert (remove X (add X evs) [=] remove X (add X evs0)). { rewrite H3. reflexivity. }
      rewrite KeySetProperties.remove_add in H5...
      rewrite KeySetProperties.remove_add in H5...
      rewrite H5. reflexivity.
    +
      rewrite <- H2. destruct IHSub with (A3:=A1) (A4:=A2)...
  - rewrite <- H0. apply IHSub...
Qed.


Lemma trans_aux2: forall B,
    type B -> forall E im cm1 cm2 A C evs1 evs2,
    Sub im cm1 evs1 E A B -> Sub im cm2 evs2 E B C -> 
    exists evs, evs [<=] evs1 `union` evs2 /\
      Sub im (seq_cm cm1 cm2) evs E A C.
Proof with auto.
  intros B H.
  dependent induction H;intros;try solve [solve_by_inv H0 H|solve_by_inv H H0|solve_by_inv H0 H2]...
  -
    (* B = Top *)
    dependent induction H0;subst...
    + 
      dependent induction H;subst...
      *
        (* Top <: Top, Top <: Top *)
        exists emp;split... fsetdec.
      *
        (* A <: Top, Top <: Top *)
        exists emp;split... fsetdec.
      *
        destruct IHSub as [evs0 [? ?]]...
        exists evs0;split... fsetdec.
    +
      exfalso...
    +
      destruct IHSub as [evs0 [? ?]]...
      exists evs0;split... fsetdec.
  -
    (* B = nat *)
    dependent induction H0;subst...
    +
      dependent induction H;subst...
      *
        (* nat <: nat, nat <: nat *)
        exists emp;split... fsetdec.
      *
        destruct IHSub as [evs0 [? ?]]...
        exists evs0;split... fsetdec.

    +
      dependent induction H;subst...
      *
        (* A <: nat, nat <: top *)
        exists emp;split... fsetdec.
      *
        destruct IHSub as [evs0 [? ?]]...
        exists evs0;split... fsetdec.
    +
      destruct IHSub as [evs0 [? ?]]...
      exists evs0;split... fsetdec.
  -
    (* B = X  *)
    dependent induction H;subst...
    +
      dependent induction H1;subst...
      *
        (* X <:(+) X, X <: top *)
        exists emp;split... fsetdec.
      *
        (* X <:(+) X, X <:(+) X *)
        exists emp;split... fsetdec.
      *
        (* X <:(+) X, X <:(-) X *)
        apply uniq_from_wf_env in H.
        pose proof binds_unique _ _ _ _ _ H0 H2 H as Eb.
        inversion Eb;subst... destruct im;inversion H4.
        (* contradiction *)
      *
        destruct (IHSub X) as [evs0 [? ?]]...
        exists evs0;split... fsetdec.
    +
      dependent induction H1;subst...
      *
        (* X <: (-) X, X <: Top
        Note: in this case, evs is not union evs1 evs2
        *)
        exists emp;split... fsetdec.
      *
        (* X <:(-) X, X <:(+) X *)
        apply uniq_from_wf_env in H1.
        pose proof binds_unique _ _ _ _ _ H0 H2 H1 as Eb.
        inversion Eb;subst... destruct im;inversion H4.
        (* contradiction *)
      *
        (* X <:(-) X, X <:(-) X *)
        exists {{ X }};split... fsetdec.
      *
        destruct (IHSub X) as [evs0 [? ?]]...
        exists evs0;split... fsetdec.
    +
      destruct IHSub with (X0:=X) as [evs0 [? ?]]...
      exists evs0;split... fsetdec.
  -
    (* B = A -> B *)
    dependent induction H1;subst...
    +
      clear IHSub1 IHSub2.
      dependent induction H2;subst...
      *
        (* A1 -> A2 < A -> B < Top  *)
        exists emp;split...
        { fsetdec. }
        rewrite seq_cm_lt2. apply Sa_top_lt...
        { get_well_form... } { intros C. inversion C. }
      *
        (* A1 -> A2 < A -> B < B1 -> B2 *)
        destruct IHtype1 with (im:=flip_im im) (E:=E)
          (cm1:=cm2) (evs1:=evs2) (A:=B1)
          (cm2:=cm1) (evs2:=evs1) (C:=A1) as [evs1' [Es1a Es1b]]...
        destruct IHtype2 with (im:=im) (E:=E)
          (cm1:=cm0) (evs1:=evs0) (A:=A2)
          (cm2:=cm3) (evs2:=evs3) (C:=B2) as [evs2' [Es2a Es2b]]...
        exists (evs1' `union` evs2'). split. { fsetdec. }
        apply Sa_arrow with (cm1:= seq_cm cm2 cm1) (cm2:= seq_cm cm0 cm3)...
        { 
          destruct cm2, cm3, cm1, cm0, cm, cm4; simpl in *;
          try solve 
          [ destruct (AtomSetImpl.is_empty evs2);inversion H2|
            destruct (AtomSetImpl.is_empty evs3);inversion H2|
            destruct (AtomSetImpl.is_empty evs1);inversion H1|
            destruct (AtomSetImpl.is_empty evs0);inversion H1
            ]...
          + 
            destruct (AtomSetImpl.is_empty evs3) eqn:Eevs3; try solve [inversion H2].
            destruct (AtomSetImpl.is_empty evs0) eqn:Eevs0; try solve [inversion H1].
            assert (AtomSetImpl.is_empty evs2' = true). 
            { apply is_empty_iff. apply is_empty_iff in Eevs3.
              apply is_empty_iff in Eevs0. fsetdec. }
            rewrite H3...
          +
            destruct (AtomSetImpl.is_empty evs3) eqn:Eevs3; try solve [inversion H2].
            apply is_empty_iff in Eevs3. destruct (AtomSetImpl.is_empty evs2') eqn:Eevs2'...
            apply Msub_eq_sem in H1_0. rewrite H1_0 in *. (*  require syntactic equal *)
            pose proof sub_eq_evs _ _ _ _ _ _ _ _ H2_0 Es2b.
            destruct_hypos.  
            apply is_not_empty_iff in Eevs2'. exfalso.
            rewrite H3 in *. congruence.
            (* destruct Eevs2' as [X' Eevs2'].
            pose proof bind_ex_evs _ _ _ _ _ _ _ Es2b Eevs2'.
            destruct H3 as [im_X' ?].
            exfalso. eapply posvar_false_simpl. { apply Es2b. } { apply Eevs2'. }
            { apply H3. } *)
          (* 
          require syntactic equal
          
          If B = A2 |> { ... } evs0 not empty
          then exists x, ~ posvar x B A2
          but A2 = B2
          so ~ posvar x B B2
          but B = B2 |> emp
          contradiction
          
          *)
          + admit.
          + admit.
          + 
          (* require syntactic *) admit.
          +
          (* require syntactic *) admit.
          
        }
      *
        destruct IHSub with (T3:=T2) (T4:=T1) as [evs2 [? ?]]...
        exists evs2;split... fsetdec.
    + destruct IHSub with (T3:=T2) (T4:=T1) as [evs0 [? ?]]...
      exists evs0;split... fsetdec.
  
  - 
    dependent induction H1.
    +
      (* Lt *)
      clear H2.
      dependent induction H3;subst...
      *
        (* Rec Lt + Top *)
        exists emp. split.
        { fsetdec. }
        { apply Sa_top_lt... admit. intros C. inversion C. }
      *
        (* Rec Lt + Lt *)
        clear H3.
        pick_fresh X.
        specialize_x_and_L X L.
        specialize_x_and_L X L0.
        specialize_x_and_L X L1.
        pose proof H0 _ _ _ _ _ _ _ _ H1 H2.
        destruct H3 as [evs1 [? ?]].
        exists evs1. split...
        apply Sa_rec_lt with (L:=L \u fv_tt A1 \u fv_tt A2 \u {{ X }} \u dom E)... intros.
        replace (evs1) with 
        (if AtomSetImpl.mem X evs1 then add X0 (remove X evs1) else evs1)...
        2:{ destruct (AtomSetImpl.mem X evs1) eqn:Evs2...
            apply mem_iff in Evs2. exfalso. clear - Fr Evs2 H3. fsetdec. }
        add_nil.
        apply sub_replacing_var...
        get_well_form... inversion H4;subst. constructor...
      *
        (* Rec Lt + Eq *)
        clear H3.
        pick_fresh X.
        specialize_x_and_L X L.
        specialize_x_and_L X L0.
        specialize_x_and_L X L1.
        pose proof H0 _ _ _ _ _ _ _ _ H1 H2.
        destruct H3 as [evs1 [? ?]].
        exists evs1. split...
        apply Sa_rec_lt with (L:=L \u fv_tt A1 \u fv_tt A2 \u {{ X }} \u dom E)... intros.
        replace (evs1) with 
        (if AtomSetImpl.mem X evs1 then add X0 (remove X evs1) else evs1)...
        2:{ destruct (AtomSetImpl.mem X evs1) eqn:Evs2...
            apply mem_iff in Evs2. exfalso. clear - Fr Evs2 H3. fsetdec. }
        add_nil.
        apply sub_replacing_var...
        get_well_form... inversion H4;subst. constructor...
      *
        (* Rec Lt + Eq in *)
        clear H3.
        pick_fresh X.
        specialize_x_and_L X L.
        specialize_x_and_L X L0.
        specialize_x_and_L X L1.
        pose proof H0 _ _ _ _ _ _ _ _ H1 H2.
        destruct H3 as [evs1 [? ?]].

        pose proof H4.
        apply sub_lt_then_emp in H4... exists emp.
        split... { clear - H. fsetdec. }
        apply Sa_rec_lt with (L:=L \u fv_tt A1 \u fv_tt A2 \u {{ X }} \u dom E)... intros.

(* Problem:

<  +  =

but = with some eq vars,

then RHS of < also have some eq vars

Solved by lt => emp

*)


        apply Sa_evs_proper with (evs:=
            if AtomSetImpl.mem X emp then add X0 (remove X emp) else emp)...
        2:{ destruct (AtomSetImpl.mem X emp) eqn:Evs2;try reflexivity.
            apply mem_iff in Evs2. exfalso. clear - Evs2. fsetdec. }
        add_nil. apply sub_replacing_var... { rewrite H4 in H5... }
        get_well_form... inversion H5;subst. constructor...
    *
      destruct IHSub with (T0:=T) as [evs1 [? ?]]...
      exists evs1;split... fsetdec.
  +
    (* Eq in *)
    (* dependent induction H3;subst... *)
    admit.
  +
    (* Eq not in *)
    clear H2.
    dependent induction H3;subst...
    *
      (* Rec Eq not in + Top *)
      exists emp. split.
      { fsetdec. }
      { apply Sa_top_lt... admit. intros C. inversion C. }
    *
      (* Rec Eq not in + Lt *)
      exists emp.
      split.
      { fsetdec. }
      pick_fresh X. specialize_x_and_L X L.
      specialize_x_and_L X L0.
      specialize_x_and_L X L1.
      pose proof H0 _ _ _ _ _ _ _ _ H1 H2.
      destruct H4 as [evs1 [? ?]].
      pose proof H5 as H7.
      apply sub_lt_then_emp in H5... rewrite H5 in H7.
      apply Sa_rec_lt with (L:=L \u fv_tt A1 \u fv_tt A2 \u {{ X }} \u dom E)... intros.
      apply Sa_evs_proper with (evs:=
          if AtomSetImpl.mem X emp then add X0 (remove X emp) else emp)...
      2:{ destruct (AtomSetImpl.mem X emp) eqn:Evs2;try reflexivity.
          apply mem_iff in Evs2. exfalso. clear - Evs2. fsetdec. }
      add_nil. apply sub_replacing_var...
      get_well_form... inversion H7;subst. constructor...
    *
      (* Rec Eq not in + Eq *)
      pick_fresh X. specialize_x_and_L X L.
      specialize_x_and_L X L0.
      specialize_x_and_L X L1.
      (* pose proof H0 _ _ _ _ _ _ _ _ H1 H3.
      destruct H5 as [evs1 [? ?]].
      exists ((remove X evs1) \u fv_tt A1). split.
      { rewrite H5. rewrite KeySetProperties.union_add. rewrite KeySetProperties.remove_add...
        clear - evs1. fsetdec. }
      apply Sa_rec_eq_in with (L:=L \u fv_tt A1 \u fv_tt A2 \u {{ X }} \u dom E \u evs1)... intros. *)
      (* replace (add X0 (remove X evs1)) with       
        (if AtomSetImpl.mem X evs1 then add X0 (remove X evs1) else evs1)...
        2:{ destruct (AtomSetImpl.mem X evs1) eqn:Evs2...
            apply not_mem_iff in Evs2. exfalso. clear - Fr Evs2 H5. *)
(* cannot be proved *)
      (* use syntactic equal *)
      pose proof H2. pose proof H1.
      apply Msub_eq_sem in H2.
      apply Msub_eq_sem in H1.
      apply open_tt_fresh_eq_inv in H2...
      apply open_tt_fresh_eq_inv in H1...
      subst.
       (* get_well_form. inversion H6;subst. *)
      destruct (Msub_refl E im (typ_mu A2)) as [evs1 ?]... { admit. } { admit. } { admit. }
      exists evs1. split...
      apply sub_evs_fv in H1. destruct_hypos. fsetdec.

    *
      (* Rec Eq not in + Rec Eq not in *)
      pick_fresh X. specialize_x_and_L X L.
      specialize_x_and_L X L0.
      specialize_x_and_L X L1.
      (* use syntactic equal *)
      pose proof H2. pose proof H1.
      apply Msub_eq_sem in H2.
      apply Msub_eq_sem in H1.
      apply open_tt_fresh_eq_inv in H2...
      apply open_tt_fresh_eq_inv in H1...
      subst.
       (* get_well_form. inversion H6;subst. *)
      destruct (Msub_refl E im (typ_mu A2)) as [evs1 ?]... { admit. } { admit. } { admit. }
      exists evs1. split...
      apply sub_evs_fv in H1. destruct_hypos. fsetdec.
    *
      destruct IHSub with (T0:=T) as [evs1 [? ?]]...
      { exists evs1;split... fsetdec. }
  +
    destruct IHSub with (T0:=T) as [evs1 [? ?]]...
    { exists evs1;split... fsetdec. }
Admitted.



