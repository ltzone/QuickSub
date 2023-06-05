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






Lemma sub_eq_evs: forall  B1 B2,
    (* typePairR A B -> *)
    equiv B1 B2 ->
    forall im cm1 cm2 evs1 evs2 E A ,
    Sub im cm1 evs1 E A B1 -> 
    Sub im cm2 evs2 E A B2 ->
    evs1 [=] evs2 /\ cm1 = cm2.
Proof with auto.
  intros B1 B2 Hequiv.
  induction Hequiv;intros...
  -
    dependent induction H.
    +
      dependent induction H0.
      *
        split... reflexivity.
      *
        rewrite <- H1. apply IHSub...
    +
      rewrite <- H0. apply IHSub...
  -
    admit.
  - admit.
  - dependent induction H.
    2:{ rewrite <- H0. apply (IHSub _ _ Hequiv1 Hequiv2)... }
    clear IHSub1 IHSub2.
    dependent induction H2.
    2:{ rewrite <- H3. apply (IHSub _ _ _ _ H H0 H1 Hequiv1 Hequiv2)... }
    clear IHSub1 IHSub2.
    pose proof IHHequiv2 _ _ _ _ _ _ _ H0 H2_0.
    destruct_hypos. rewrite H3. subst.
    admit. (* need auxliary equiv IH *)
  -
    dependent induction H1.
    +
      clear H2.
      (* Lt *)
      dependent induction H3.
      *
        (* Lt *)
        clear H3.
        split...
        pick_fresh X. specialize_x_and_L X L.
        specialize_x_and_L X L1.
        specialize_x_and_L X L0.
        destruct (H0 _ _ _ _ _ _ _ H1 H2)...
      *
        (* Lt + Eq *)
        clear H3.
        pick_fresh X. specialize_x_and_L X L.
        specialize_x_and_L X L1.
        specialize_x_and_L X L0.
        apply Msub_refl_inv in H2.
        apply Msub_lt_not_eq in H1.
        exfalso. apply H1.
        apply equiv_symm in H.
        apply equiv_trans with (B:=open_tt B X)...
      *
        (* Lt + Eq *)
        clear H3.
        pick_fresh X. specialize_x_and_L X L.
        specialize_x_and_L X L1.
        specialize_x_and_L X L0.
        apply Msub_refl_inv in H2.
        apply Msub_lt_not_eq in H1.
        exfalso. apply H1.
        apply equiv_symm in H.
        apply equiv_trans with (B:=open_tt B X)...
      *
        rewrite <- H2. apply (IHSub B A1)...
    +
      admit.
    +
      admit.
    +
    admit.
  -
    dependent induction H2.
    +
      admit.
    +

    Admitted.

Inductive typ_for_rcd: list (atom * typ) -> 
  list (atom * typ) ->  list (atom * typ) -> Prop :=
| tfr_nil: typ_for_rcd nil nil nil
| tfr_lt : forall ts, typ_for_rcd ts nil nil
| tfr_cons_l : forall l T1 T2 ts1a ts1b ts2a ts2b, 
    typ_for_rcd (ts1a ++ ts1b) (ts2a ++ ts2b) nil -> 
    typ_for_rcd (ts1a ++ l ~ T1 ++ ts1b) (ts2a ++ l ~ T2 ++ ts2b) nil
| tfr_cons_lr : forall l T1 T2 T3 ts1a ts1b ts2a ts2b ts3a ts3b, 
    typ_for_rcd (ts1a ++ ts1b) (ts2a ++ ts2b) (ts3a ++ ts3b) -> 
    typ_for_rcd (ts1a ++ l ~ T1 ++ ts1b) (ts2a ++ l ~ T2 ++ ts2b) (ts3a ++ l ~ T3 ++ ts3b).

Lemma sub_typ_label_incl: forall {im cm evs E ls1 ls2},
  Sub im cm evs E (typ_rcd ls1) (typ_rcd ls2) ->
  dom ls2 [<=] dom ls1.
Proof with auto.
  intros...
  dependent induction H...
  - reflexivity.
  - simpl. fsetdec.
  - rewrite !dom_app. simpl.
    specialize (IHSub2 _ _ eq_refl eq_refl).
    rewrite !dom_app in IHSub2.
    fsetdec.
Qed.

Fixpoint dropLabel lb (l: list (atom * typ)) :=
  match l with
  | nil => nil
  | (l1, T1) :: l' => if l1 == lb 
      then dropLabel lb l' 
      else (l1, T1) :: dropLabel lb l'
  end.

Fixpoint dropLabel_typ lb t :=
  match t with
  | typ_rcd l => typ_rcd (dropLabel lb l)
  | typ_arrow t1 t2 => typ_arrow (dropLabel_typ lb t1) (dropLabel_typ lb t2)
  | typ_mu t => typ_mu (dropLabel_typ lb t)
  | _ => t
  end.


(* Lemma dropLabel_mid:
  forall lb l1 T l3,
    dropLabel lb (l1 ++ lb ~ T ++ l3) = l1 ++ l3.
Admitted.
*)

Lemma dropLabel_dom: forall l lb,
  dom (dropLabel lb l) [<=] dom l.
Proof with auto.
  induction l;intros...
  + reflexivity.
  + destruct a. simpl. destruct (a == lb)...
    * rewrite IHl. fsetdec.
    * simpl. rewrite IHl. fsetdec.
Qed.

Lemma dropLabel_uniq: forall l lb, 
  uniq l -> uniq (dropLabel lb l).
Proof with auto.
  intros.
  induction l...
  - simpl. destruct a.
    inversion H;subst.
    destruct (a == lb)...
    constructor...
    rewrite dropLabel_dom...
Qed.

Lemma dropLabel_eq: forall l a,
  a `notin` dom l ->
  dropLabel a l = l.
Proof with auto.
  induction l;intros...
  destruct a. simpl.
  destruct (a == a0)...
  { subst. simpl in H. exfalso... }
  { rewrite IHl... }
Qed.

Lemma dropLabel_binds: forall ls l T lb,
  binds l T (dropLabel lb ls) ->
  binds l T ls.
Proof with auto.
  intros.
  induction ls;intros...
  destruct a. simpl in H.
  destruct (a == lb)...
  analyze_binds H...
Qed.

Lemma open_tt_dropLabel_comm: forall lb A (X:atom),
  open_tt (dropLabel_typ lb A) X = dropLabel_typ lb (open_tt A X).
Proof with auto.
  intros. unfold open_tt. generalize 0.
  induction A using typ_rec';intros...
  - simpl.
    destruct (n0 == n)...
  - simpl. rewrite IHA...
  - simpl. rewrite IHA1. rewrite IHA2...
  - simpl. destruct (l == lb)...
    { subst. simpl in IHA0. rewrite IHA0... }
    { simpl. f_equal. f_equal. simpl in IHA0. 
      apply typ_rcd_inj.
      rewrite IHA0... }
Qed.

Lemma dropLabel_fv_tt: forall lb A,
  fv_tt (dropLabel_typ lb A) [<=] fv_tt A.
Proof with auto.
  intros. induction A using typ_rec';intros;
  try solve [simpl;fsetdec]...
  - simpl. destruct (l == lb)...
    + simpl in IHA0. rewrite IHA0...
      fsetdec.
    + simpl. fsetdec.
Qed.




Lemma sub_typ_for_rcd: forall im cm1 cm2 evs1 evs2 E l1 l2 l3,
  Sub im cm1 evs1 E (typ_rcd l1) (typ_rcd l2) ->
  Sub im cm2 evs2 E (typ_rcd l2) (typ_rcd l3) ->
  typ_for_rcd l1 l2 l3.
Proof with auto.
  intros. revert H. revert l1 evs1 cm1.
  dependent induction H0;intros.
  3:{
    
    dependent induction H2.
    3:{
      


    }


  }
      admit.
    +
      (* cons *)
      clear IHSub1. clear IHSub2.
      dependent induction H3.
      *
        admit.
      *
        admit.
      *
        clear IHSub1. clear IHSub2.




Lemma sub_eq_evs': forall im cm1 cm2 evs1 evs2 E A B1 B2,
    (* typePairR A B -> *)
    equiv B1 B2 ->
    Sub im cm1 evs1 E B1 A -> 
    Sub im cm2 evs2 E B2 A ->
    evs1 [=] evs2 /\ cm1 = cm2.
Admitted.

Lemma sub_rcd_canonical: forall im cm evs E A l,
  Sub im cm evs E A (typ_rcd l) ->
  exists l', A = typ_rcd l'.
Proof with auto.
  intros. dependent induction H...
  - exists nil...
  - exists tys...
  - exists (tys1 ++ l0 ~ T1 ++ tys1')...
  - apply IHSub with (l0:=l)...
Qed.

Inductive typ_rcd_rec: list (atom * typ) -> list (atom * typ) -> 
  Prop :=
| trr_nil: typ_rcd_rec nil nil
| trr_lt : forall ts, typ_rcd_rec ts nil
| trr_cons: forall l T1 T2 ts1a ts1b ts2a ts2b, 
    typ_rcd_rec (ts1a++ts1b) (ts2a++ts2b) -> 
    typ_rcd_rec (ts1a ++ l ~ T1 ++ ts1b) (ts2a ++ l ~ T2 ++ ts2b).






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
            apply Msub_refl_inv in H1_0.
            pose proof sub_eq_evs' _ _ _ _ _ _ _ _ _ H1_0 Es2b H2_0.
            destruct_hypos.
            apply is_not_empty_iff in Eevs2'. exfalso.
            rewrite H3 in *. congruence.


          + 
            destruct (AtomSetImpl.is_empty evs2) eqn:Eevs2; try solve [inversion H2].
            apply is_empty_iff in Eevs2. destruct (AtomSetImpl.is_empty evs1') eqn:Eevs1'...
            apply Msub_refl_inv in H1_.
            pose proof sub_eq_evs _ _ _ _ _ _ _ _ _ H1_ H2_ Es1b.
            destruct_hypos.
            apply is_not_empty_iff in Eevs1'. exfalso.
            rewrite H3 in *. congruence.

          +
            destruct (AtomSetImpl.is_empty evs2) eqn:Eevs2; try solve [inversion H2].
            apply is_empty_iff in Eevs2. destruct (AtomSetImpl.is_empty evs1') eqn:Eevs1'...
            apply Msub_refl_inv in H1_.
            pose proof sub_eq_evs _ _ _ _ _ _ _ _ _ H1_ H2_ Es1b.
            destruct_hypos.  
            apply is_not_empty_iff in Eevs1'. exfalso.
            rewrite H3 in *. congruence.
          + 
            destruct (AtomSetImpl.is_empty evs0) eqn:Eevs0; try solve [inversion H1].
            apply is_empty_iff in Eevs0. destruct (AtomSetImpl.is_empty evs2') eqn:Eevs2'...
            apply Msub_refl_inv in H2_0.
            pose proof sub_eq_evs _ _ _ _ _ _ _ _ _ H2_0 H1_0 Es2b.
            destruct_hypos.  
            apply is_not_empty_iff in Eevs2'. exfalso.
            rewrite H3 in *. congruence.
          +
            destruct (AtomSetImpl.is_empty evs1) eqn:Eevs1; try solve [inversion H1].
            apply is_empty_iff in Eevs1. destruct (AtomSetImpl.is_empty evs1') eqn:Eevs1'...
            apply Msub_refl_inv in H2_.
            (* apply Msub_eq_sem in H2_. rewrite H2_ in *.  require syntactic equal *)
            pose proof sub_eq_evs' _ _ _ _ _ _ _ _ _ H2_ Es1b H1_.
            destruct_hypos.  
            apply is_not_empty_iff in Eevs1'. exfalso.
            rewrite H3 in *. congruence.
          
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
        { apply Sa_top_lt... 
          { assert (Sub im Lt evs E (typ_mu A1) (typ_mu T)). { apply Sa_rec_lt with (L:=L0)... }
            apply sub_regular in H5. destruct_hypos... }
          intros C. inversion C. }
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
    clear H2.
    (* assert ((Sub im Eq evs E (typ_mu A1) (typ_mu T))). { apply Sa_rec_eq_notin with (L:=L0)... } *)
    dependent induction H3;subst...
    *
      (* Rec Eq + Top *)
      exists emp. split.
      { fsetdec. }
      { apply Sa_top_lt...
        assert ((Sub im Eq evs E (typ_mu A1) (typ_mu T))). { apply Sa_rec_eq_notin with (L:=L0)... } 
        apply sub_regular in H5. destruct_hypos...
        intros C. inversion C. }
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
      pose proof H5 as H6.
      apply sub_lt_then_emp in H6... rewrite H6 in H5.
      apply Sa_rec_lt with (L:=L \u fv_tt A1 \u fv_tt A2 \u {{ X }} \u dom E)... intros.
      apply Sa_evs_proper with (evs:=
          if AtomSetImpl.mem X emp then add X0 (remove X emp) else emp)...
      2:{ destruct (AtomSetImpl.mem X emp) eqn:Evs2;try reflexivity.
          apply mem_iff in Evs2. exfalso. clear - Evs2. fsetdec. }
      add_nil. apply sub_replacing_var...
      get_well_form... inversion H5;subst. constructor...
    *
      (* Rec Eq not in + Rec Eq notin *)
      pick_fresh X. specialize_x_and_L X L.
      specialize_x_and_L X L0.
      specialize_x_and_L X L1.
      pose proof H0 _ _ _ _ _ _ _ _ H1 H2.
      destruct H4 as [evs1 [? ?]].
      exists evs1. split...
      apply Sa_rec_eq_notin with (L:=L \u fv_tt A1 \u fv_tt A2 \u {{ X }} \u dom E)... intros.
      apply Sa_evs_proper with (evs:=
          if AtomSetImpl.mem X evs1 then add X0 (remove X evs1) else evs1)...
      2:{ destruct (AtomSetImpl.mem X evs1) eqn:Evs2;try reflexivity.
          apply mem_iff in Evs2. exfalso. clear - Evs2 Fr H4. rewrite H4 in Evs2.
          apply Fr. clear - Evs2. fsetdec. }
      add_nil. apply sub_replacing_var...
      get_well_form... inversion H5;subst. constructor...
    *
      (* Rec Eq not in + Rec Eq in *)
      assert ((Sub im Eq evs E (typ_mu A1) (typ_mu T))). { apply Sa_rec_eq_notin with (L:=L0)... } 
      destruct (Msub_refl_equiv E im (typ_mu A1) (typ_mu A2)) as [evs1 ?];
        try solve [get_well_form;auto;get_type;auto].
      { apply WFS_rec with (L:=L \u L1) (im:=im)...
        intros. specialize_x_and_L X L1. get_well_form... }
      { apply eqv_mu with (L:=L \u L1 \u L0) ... intros.
        specialize_x_and_L X L1. specialize_x_and_L X L0.
        apply Msub_refl_inv in H2. apply Msub_refl_inv in H1.
        pose proof equiv_trans _ _ _ H1 H2...
      }

       (* get_well_form. inversion H6;subst. *)

      exists evs1. split...
      apply sub_evs_fv in H5. destruct_hypos.
      apply Msub_refl_inv in H4.
      apply equiv_fv_tt in H4. rewrite H4 in H5.
      fsetdec.
    *
      destruct IHSub with (T0:=T) as [evs1 [? ?]]...
      { exists evs1;split... fsetdec. }



  +
    (* Eq in *)
    clear H2.
    dependent induction H3;subst...
    *
      (* Rec Eq in + Top *)
      exists emp. split.
      { fsetdec. }
      { apply Sa_top_lt...
        assert ((Sub im Eq (evs \u fv_tt A1) E (typ_mu A1) (typ_mu T))). { apply Sa_rec_eq_in with (L:=L0)... }
        get_well_form...
        intros C. inversion C. }
    *
      (* Rec Eq in + Lt *)
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
      assert ((Sub im Eq (evs \u fv_tt A1) E (typ_mu A1) (typ_mu T))). { apply Sa_rec_eq_in with (L:=L0)... } 
      destruct (Msub_refl_equiv E im (typ_mu A1) (typ_mu A2)) as [evs1 ?];
        try solve [get_well_form;auto;get_type;auto].
      { apply WFS_rec with (L:=L \u L1) (im:=im)...
        intros. specialize_x_and_L X L1. get_well_form... }
      { apply eqv_mu with (L:=L \u L1 \u L0) ... intros.
        specialize_x_and_L X L1. specialize_x_and_L X L0.
        apply Msub_refl_inv in H2. apply Msub_refl_inv in H1.
        pose proof equiv_trans _ _ _ H1 H2...
      }

       (* get_well_form. inversion H6;subst. *)

      exists evs1. split...
      apply sub_evs_fv in H5. destruct_hypos.
      apply Msub_refl_inv in H4.
      apply equiv_fv_tt in H4. rewrite H4 in H5.
      fsetdec.


    *
    (* notin + notin *)
      assert (Esub: (Sub im Eq (evs \u fv_tt A1) E (typ_mu A1) (typ_mu T))). { apply Sa_rec_eq_in with (L:=L0)... }


      destruct (Msub_refl_equiv E im (typ_mu A1) (typ_mu A2)) as [evs1 ?];
        try solve [get_well_form;auto;get_type;auto].
      { apply WFS_rec with (L:=L \u L1) (im:=im)...
        intros. specialize_x_and_L X L1. get_well_form... }
      { apply eqv_mu with (L:=L \u L1 \u L0) ... intros.
        specialize_x_and_L X L1. specialize_x_and_L X L0.
        apply Msub_refl_inv in H2. apply Msub_refl_inv in H1.
        pose proof equiv_trans _ _ _ H1 H2...
      }

       (* get_well_form. inversion H6;subst. *)

      exists evs1. split...
      apply sub_evs_fv in H4. destruct_hypos.
      apply Msub_refl_inv in Esub.
      apply equiv_fv_tt in Esub. rewrite Esub in H4.
      fsetdec.

    *
      destruct IHSub with (T0:=T) as [evs1 [? ?]]...
      { exists evs1;split... fsetdec. }
  +
    destruct IHSub with (T0:=T) as [evs1 [? ?]]...
    { exists evs1;split... fsetdec. }

- 
  (* rcd : need to do induction from right to left to ensure label inclusion  *)
  assert (Hwf: WFS E A). { get_well_form... }
  generalize dependent A. generalize dependent cm1.
  generalize dependent evs1.
  dependent induction H2;intros;subst...
  *
    (* top *)
    dependent induction H4;subst;try solve
      [exists emp; split; auto; fsetdec].
    +
      exists emp... split... fsetdec.
      apply Sa_top_lt... intros C. inversion C.
    +
      exists emp... split... fsetdec.
      rewrite seq_cm_lt2. apply Sa_top_lt...
      intros C. inversion C.
    +
      destruct IHSub with (l0:=l)...
      destruct_hypos. exists x...
      split... fsetdec.
  *
    (* nil *)
    dependent induction H2;subst;try solve
      [exists emp; split; auto; fsetdec].
    + apply app_cons_not_nil in x. exfalso...
    + destruct (IHSub)... destruct_hypos. exists x.
      split... fsetdec.
  *
    (* cons <: nil *)
    dependent induction H5;subst;try solve
      [exists emp; split; auto; fsetdec].
    + rewrite seq_cm_lt2. exists emp. split...
      fsetdec. apply Sa_rcd_lt...
      { inversion Hwf... } { inversion Hwf... }
    + destruct (IHSub) with (l0:=l)... destruct_hypos. exists x.
      split... fsetdec.
  *
    pose proof sub_rcd_canonical _ _ _ _ _ _ H2.
    destruct H3 as [tys' ?]. subst.
    assert (l0 `in` dom tys') by admit.
    apply binds_In_inv in H3.
    destruct H3 as [T1' ?].
    apply binds_split in H3.
    destruct H3 as (tys0 & tys0' & ?). subst.
    Search binds ex.

    (* cons <: cons *)
    dependent induction H2;subst.
    +
      symmetry in x. apply app_cons_not_nil in x. exfalso...
    +
      symmetry in x. apply app_cons_not_nil in x. exfalso...
    +
      clear IHSub0. clear IHSub3.

  *
    (* rcd cons <: nil <: ? *)
    dependent induction H5;subst...
    +
      (* rcd cons + top *)
      exists emp... split... fsetdec.
      constructor... intros C. inversion C.
    +
      (* rcd cons + rcd nil *)
      exists emp... split... fsetdec.
    +
      (* rcd cons nil + rcd cons nil *)
      exfalso...
    +
      (* rcd cons nil ++ rcd cons *)
      apply app_cons_not_nil in x. exfalso...
    +
      destruct IHSub as [evs1 [? ?]]...
      { exists evs1;split... fsetdec. }
  *
    (* rcd cons ++ ? *)
    dependent induction H2;subst...
    +
      (* rcd cons + top *)
      exists emp... rewrite seq_cm_lt2. split... fsetdec.
      constructor... intros C. inversion C.
    +
      (* rcd cons + rcd nil *)
      symmetry in x. apply app_cons_not_nil in x. exfalso...
    +
      (* rcd cons nil + rcd cons nil *)
      exists emp... rewrite seq_cm_lt2. split... fsetdec.
      constructor... { inversion Hwf...  } { inversion Hwf... }
    +
      (* rcd cons ++ rcd cons *)
      clear IHSub0. clear IHSub3.
      destruct (H0 l0 T2) with (E:=E) () ...



  (* rcd *)
  assert (Hwf: WFS E A). { get_well_form... }
  generalize dependent C. generalize dependent cm2.
  generalize dependent evs2.
  dependent induction H1;intros;subst...
  *
    (* rcd nil *)
    dependent induction H2;subst...
    +
      (* rcd nil + top *)
      exists emp... split... fsetdec.
    +
      (* rcd nil + rcd nil *)
      exists emp... split... fsetdec.
    +
      (* rcd nil + rcd cons *)
      exfalso...
    +
      (* rcd nil ++ rcd *)
      apply app_cons_not_nil in x. exfalso...
    +
      destruct IHSub as [evs1 [? ?]]...
      { exists evs1;split... fsetdec. }
  *
    (* rcd cons <: nil <: ? *)
    dependent induction H5;subst...
    +
      (* rcd cons + top *)
      exists emp... split... fsetdec.
      constructor... intros C. inversion C.
    +
      (* rcd cons + rcd nil *)
      exists emp... split... fsetdec.
    +
      (* rcd cons nil + rcd cons nil *)
      exfalso...
    +
      (* rcd cons nil ++ rcd cons *)
      apply app_cons_not_nil in x. exfalso...
    +
      destruct IHSub as [evs1 [? ?]]...
      { exists evs1;split... fsetdec. }
  *
    (* rcd cons ++ ? *)
    dependent induction H2;subst...
    +
      (* rcd cons + top *)
      exists emp... rewrite seq_cm_lt2. split... fsetdec.
      constructor... intros C. inversion C.
    +
      (* rcd cons + rcd nil *)
      symmetry in x. apply app_cons_not_nil in x. exfalso...
    +
      (* rcd cons nil + rcd cons nil *)
      exists emp... rewrite seq_cm_lt2. split... fsetdec.
      constructor... { inversion Hwf...  } { inversion Hwf... }
    +
      (* rcd cons ++ rcd cons *)
      clear IHSub0. clear IHSub3.
      destruct (H0 l0 T2) with (E:=E) () ...
      






Qed.



