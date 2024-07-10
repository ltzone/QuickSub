Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export LinearRule.


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

Definition dropLabel_typ' lb t :=
  match t with
  | typ_rcd l => Some (typ_rcd (dropLabel lb l))
  | _ => None
  end.

Fixpoint getLabel lb (l: list (atom * typ)) :=
  match l with
  | nil => None
  | (l1, T1) :: l' => if l1 == lb 
      then Some T1
      else getLabel lb l'
  end.

Definition getLabel_typ lb t :=
  match t with
  | typ_rcd l => getLabel lb l
  | typ_arrow t1 t2 => None
  | typ_mu t => None
  | _ => None
  end.



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


Lemma dropLabel_dom_sem: forall l lb,
  dom (dropLabel lb l) [=] remove lb (dom l).
Proof with auto.
  intros.
  induction l.
  - simpl. fsetdec.
  - destruct a. simpl.
    destruct (a == lb).
    { subst. rewrite IHl. fsetdec. }
    { simpl. rewrite IHl. fsetdec. }
Qed.



Lemma dropLabel_dom_eq: forall l1 l2 lb,
  dom l1 [=] dom l2 ->
  dom (dropLabel lb l1) [=] dom (dropLabel lb l2).
Proof with auto.
  intros.
  rewrite !dropLabel_dom_sem...
  rewrite H.
  reflexivity.
Qed.



Lemma dropLabel_equiv: forall A B lb,
  equiv A B ->
  equiv (dropLabel_typ lb A) (dropLabel_typ lb B).
Proof with auto.
  intros.
  induction H;intros;simpl...
  - 
    apply eqv_mu with (L:=L).
    intros. specialize_x_and_L X L.
    rewrite !open_tt_dropLabel_comm...
  - apply eqv_rcd...
    { apply (dropLabel_dom_eq l1)... }
    { intros.
      apply dropLabel_binds in H2.
      apply dropLabel_binds in H3.
      apply H0 with (i:=i)... }
Qed.




Lemma dropLabel_type: forall A lb,
  type A ->
  type (dropLabel_typ lb A).
Proof with auto.
  intros. induction H...
  - simpl. constructor...
  - simpl...
  - simpl. apply type_mu with (L:=L)...
    intros. rewrite open_tt_dropLabel_comm...
  - simpl. apply type_rcd.
    { apply dropLabel_uniq... }
    intros. apply dropLabel_binds in H1.
    apply H with (i:=i)...
Qed.


Lemma posvar_dropLabel: forall im X A B lb,
  posvar im X A B ->
  posvar im X (dropLabel_typ lb A) (dropLabel_typ lb B).
Proof with auto.
  intros. induction H;intros;simpl...
  - apply pos_top... apply dropLabel_type...
  - apply pos_top_flip... apply dropLabel_type...
  - apply pos_rec with (L:=L).
    + intros. rewrite !open_tt_dropLabel_comm...
    + intros. rewrite !open_tt_dropLabel_comm...
  - apply pos_rec_t with (L:=L)...
    + rewrite dropLabel_fv_tt...
    + rewrite dropLabel_fv_tt...
    + intros. rewrite open_tt_dropLabel_comm.
      apply dropLabel_type...
    + intros. rewrite open_tt_dropLabel_comm.
      apply dropLabel_type...
    + inversion H3;subst.
      apply eqv_mu with (L:=L `union` L0).
      intros.
      rewrite !open_tt_dropLabel_comm.
      apply dropLabel_equiv...
  - apply pos_rcd...
    { inversion H;subst. constructor...
      + apply dropLabel_uniq...
      + intros. apply H4 with (i:=i)...
        eapply dropLabel_binds;eauto. }
    { inversion H0;subst. constructor...
      + apply dropLabel_uniq...
      + intros. apply H4 with (i:=i)...
        eapply dropLabel_binds;eauto. }

    intros.
    * apply dropLabel_binds in H3.
      apply dropLabel_binds in H4.
      apply H1 with (l:=l)...
Qed.

Lemma dropLabel_app: forall tys1 tys1' l T1  lb,
  uniq (tys1 ++ l ~ T1 ++ tys1') ->
  l <> lb ->
  dropLabel lb (tys1 ++ l ~ T1 ++ tys1') =
  (dropLabel lb tys1) ++ l ~ T1 ++ (dropLabel lb tys1').
Proof with auto.
  intros.
  induction tys1...
  - simpl... destruct (l == lb)... exfalso...
  - destruct a. simpl. destruct (a == lb).
    + apply IHtys1... inversion H...
    + simpl. f_equal...
      apply IHtys1... inversion H...
Qed.


Lemma dropLabel_app2: forall tys1 tys1'  lb,
  uniq (tys1 ++  tys1') ->
  dropLabel lb (tys1 ++  tys1') =
  (dropLabel lb tys1) ++(dropLabel lb tys1').
Proof with auto.
  intros.
  induction tys1...
  - destruct a. simpl. destruct (a == lb).
    + apply IHtys1... inversion H...
    + simpl. f_equal...
      apply IHtys1... inversion H...
Qed.


Lemma dropLabel_app3: forall tys1 tys1'  lb T1,
  uniq (tys1 ++ lb ~ T1 ++ tys1') ->
  dropLabel lb (tys1 ++ lb ~ T1  ++ tys1') =
  (dropLabel lb tys1) ++(dropLabel lb tys1').
Proof with auto.
  intros.
  induction tys1...
  - simpl. rewrite eq_dec_refl...
  - destruct a. simpl. destruct (a == lb).
    + apply IHtys1... inversion H...
    + simpl. f_equal...
      apply IHtys1... inversion H...
Qed.

Lemma dropLabel_notin: forall lb ls,
  lb `notin` dom ls ->
  dropLabel lb ls = ls.
Proof with auto.
  induction ls;intros...
  simpl. destruct a.
  destruct (a == lb)...
  { simpl in H. subst. exfalso. fsetdec. }
  { f_equal. rewrite IHls... }
Qed.

Lemma dropLabel_app4: forall tys1 tys1'  lb T1,
  uniq (tys1 ++ lb ~ T1 ++ tys1') ->
  dropLabel lb (tys1 ++ lb ~ T1  ++ tys1') =
  tys1 ++ tys1'.
Proof with auto.
  intros.
  induction tys1...
  - simpl. rewrite eq_dec_refl...
    inversion H;subst.
    rewrite dropLabel_notin...
  - destruct a. simpl. destruct (a == lb).
    + inversion H;subst. rewrite dom_app in H4.
      simpl in H4. fsetdec.
    + simpl. f_equal...
      apply IHtys1... inversion H...
Qed.

Lemma getLabel_get: forall lb tys1 tys2 T,
  uniq (tys1 ++ lb ~ T ++ tys2) ->
  getLabel lb (tys1 ++ lb ~ T ++ tys2) = Some T.
Proof with auto.
  intros.
  induction tys1...
  - simpl... rewrite eq_dec_refl...
  - simpl. destruct a.
    destruct (a == lb).
    + subst. inversion H;subst...
      rewrite dom_app in H4. simpl in H4. fsetdec.
    + apply IHtys1... inversion H...
Qed. 

Lemma getLabel_get2: forall lb l tys1 tys2 T,
  uniq (tys1 ++ l ~ T ++ tys2) -> l <> lb ->
  getLabel lb (tys1 ++ l ~ T ++ tys2) = getLabel lb (tys1 ++ tys2).
Proof with auto.
  intros.
  induction tys1...
  - simpl... destruct (l == lb)... exfalso...
  - simpl. destruct a.
    destruct (a == lb)...
    + apply IHtys1... inversion H...
Qed. 


Lemma sub_rcd_get: forall t1 t2 im cm evs E,
  Sub im cm evs E ( t1) ( t2) ->
  forall lb T1 T2,
  getLabel_typ lb t1 = Some T1 ->
  getLabel_typ lb t2 = Some T2 ->
  exists cm', (exists evs', evs' [<=] evs /\ Sub im cm' evs' E T1 T2)
    /\ (cm = Eq -> cm' = Eq) /\ (cm' = Lt -> cm = Lt) .
Proof with auto.
  intros t1 t2 im cm evs E Hsub lb T1 T2 Hget1 Hget2.
  revert lb T1 T2 Hget1 Hget2.
  dependent induction Hsub;intros;
    try solve [inversion Hget1; inversion Hget2]...
  -
    assert (Hu1: uniq (tys1 ++ l ~ T1 ++ tys1')).
    { get_well_form. inversion H1;subst. apply uniq_insert_mid... }
    assert (Hu2: uniq (tys2 ++ l ~ T2 ++ tys2')).
    { get_well_form. inversion H2;subst. apply uniq_insert_mid... }

    destruct (l == lb).
    +
      subst.
      exists cm1. split.
      2:{ split...
      + intros. subst. destruct cm1...
        simpl in H. destruct cm2; inversion H.
        destruct (AtomSetImpl.is_empty evs2);inversion H1.
      + intros. subst. destruct cm2;inversion H...
        destruct (AtomSetImpl.is_empty evs2);inversion H1...
      } 
      exists evs1. split.
      { fsetdec. }
      { cbv [getLabel_typ] in Hget1, Hget2.
        rewrite getLabel_get in Hget2...
        rewrite getLabel_get in Hget1...
        inversion Hget2; inversion Hget1;subst...
      }
    +
      destruct IHHsub2 with (lb:=lb) (T1:=T0) (T2:=T3)
        as (cm' & (evs' & (Hevs' & H0)) & Hcm)...
      { cbv [getLabel_typ] in Hget1, Hget2.
        rewrite getLabel_get2 in Hget1... }
      { cbv [getLabel_typ] in Hget1, Hget2.
        rewrite getLabel_get2 in Hget2... }
      exists cm'. split.
      2:{ split;intros.
        + subst. destruct cm'... destruct Hcm as [Hcm1 Hcm2].
          specialize (Hcm2 eq_refl). subst.
          destruct cm1; inversion H.
          destruct (AtomSetImpl.is_empty evs1);inversion H2.
        + subst. destruct cm... destruct Hcm as [Hcm1 Hcm2].
          specialize (Hcm2 eq_refl). subst.
          destruct cm1; inversion H.
          destruct (AtomSetImpl.is_empty evs1);inversion H2.
      }
      exists evs'.
      split... fsetdec.
  -
    destruct IHHsub with (lb:=lb) (T1:=T1) (T2:=T2)
      as (cm' & (evs'' & (Hevs'' & H0)) & Hcm)...
    exists cm'. split... exists evs''...
    split... fsetdec.
Qed.

Lemma dropLabel_ntop: forall A lb,
  A <> typ_top ->
  dropLabel_typ lb A <> typ_top.
Proof with auto.
  intros.
  induction A...
  - simpl. intros C. inversion C.
  - simpl. intros C. inversion C.
  - simpl. intros C. inversion C.
Qed.

Lemma dropLabel_WFS: forall E A lb,
  WFS E A ->
  WFS E (dropLabel_typ lb A).
Proof with auto.
  intros.
  induction H...
  - simpl. apply WFS_fvar with (im:=im)...
  - simpl. constructor...
  - simpl. apply WFS_rec with (L:=L) (im:=im)...
    intros.
    rewrite open_tt_dropLabel_comm...
  - simpl. apply WFS_rcd...
    { apply dropLabel_uniq... }
    { intros.
      apply dropLabel_binds in H2.
      apply H0 with (i:=i)...
     }
Qed.



Lemma sub_rcd_remove: forall t1 t2 lb im cm evs E,
  Sub im cm evs E ( t1) ( t2) ->
  exists cm', (exists evs', evs' [<=] evs /\ Sub im cm' evs' E ( (dropLabel_typ lb t1))
    ((dropLabel_typ lb t2)))
    /\ (cm = Eq -> cm' = Eq) /\ (cm' = Lt -> cm = Lt) .
Proof with eauto.
  intros.
  (* pose proof Sub_typePairR _ _ _ _ _ _ H. *)
  (* dependent induction H0;simpl... *)
  intros.  
  dependent induction H;
    try solve [simpl; eexists; split;[|auto]; eexists; auto]...
  - exists Eq. split...
    exists emp. split... reflexivity.
  - exists Eq. split...
    exists emp. split... reflexivity.
  - exists Lt. split...
    exists emp. split... { reflexivity. }
    { pose proof dropLabel_ntop _ lb H1.
      apply Sa_top_lt...
      apply dropLabel_WFS... }
  - exists Eq. split...
    exists emp. split... { reflexivity. }
    simpl. constructor...
  - exists Eq. split...
    exists {{ X }}. split... { reflexivity. }
    constructor...
  -
  
    destruct IHSub1 as (cm1' & (evs1' & Hevs1' & IHSub1) & Hc1 & Hc2).
    destruct IHSub2 as (cm2' & (evs2' & Hevs2' & IHSub2) & Hc3 & Hc4).
    destruct (compose_cm cm1' cm2' evs1' evs2') eqn:Ec.
    { exists c. repeat split...
      +  exists (evs1' `union` evs2' ). split. { fsetdec. } 
        apply Sa_arrow with (cm1:=cm1') (cm2:=cm2')...
      + intros. destruct cm1, cm2, cm1', cm2', cm, c;
          try solve [inversion H1];
          try solve [inversion Ec]...
        { simpl in H1. destruct (AtomSetImpl.is_empty evs2);inversion H1. }
        { simpl in H1. destruct (AtomSetImpl.is_empty evs1);inversion H1. }
      + intros. destruct cm1, cm2, cm1', cm2', cm, c;
          try solve [inversion H1];
          try solve [inversion Ec]...
        { simpl in H1. destruct (AtomSetImpl.is_empty evs2);inversion H1. }
        { simpl in H1. destruct (AtomSetImpl.is_empty evs1);inversion H1. }
    }
    { destruct cm1', cm2';inversion Ec.
      + destruct (AtomSetImpl.is_empty evs2') eqn:Eempty;try solve [inversion H3].
        apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
        destruct Eempty as [X' Eempty].
        assert (exists im_x', binds X' (bind_sub im_x') E).
        { apply bind_ex_evs with (X:=X') in IHSub2... }
        destruct H2 as [im_x' H2].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub2 X' im_x' Eempty H2.
        exfalso. apply H4.
        apply posvar_dropLabel.
        apply soundness_posvar_simpl with (E:=E) (cm:=cm2) (evs:=evs2)...
        { 
          (* evs2 must be empty *)
          specialize (Hc2 eq_refl). subst.
          destruct cm2;inversion H1;subst...
          + apply sub_lt_then_emp in H0... rewrite H0. fsetdec.
          + destruct (AtomSetImpl.is_empty evs2) eqn:Eempty';inversion H6.
            apply is_empty_iff in Eempty'. fsetdec.
        }
      + destruct (AtomSetImpl.is_empty evs1') eqn:Eempty;try solve [inversion H3].
        apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
        destruct Eempty as [X' Eempty].
        assert (exists im_x', binds X' (bind_sub im_x') E).
        { apply bind_ex_evs with (X:=X') in IHSub1... }
        destruct H2 as [im_x' H2].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub1 X' im_x' Eempty H2.
        exfalso. apply H4.
        apply posvar_dropLabel.
        apply soundness_posvar_simpl with (E:=E) (cm:=cm1) (evs:=evs1)...
        { 
          (* evs1 must be empty *)
          specialize (Hc4 eq_refl). subst.
          destruct cm1;inversion H1;subst...
          + apply sub_lt_then_emp in H... rewrite H. fsetdec.
          + destruct (AtomSetImpl.is_empty evs1) eqn:Eempty';inversion H6.
            apply is_empty_iff in Eempty'. fsetdec.
        }
    }

  - 
    pick_fresh X. specialize_x_and_L X L.
    destruct H0 as (cm' & (evs' & (Hevs' & IHSub)) & Hc1 & Hc2).
    destruct cm'.
    +
      exists Lt. split...
      exists evs'. split. { fsetdec. }
      simpl.
      apply Sa_rec_lt with (L:=L \u {{X}} \u evs' \u dom E)... intros.
      replace evs' with (if AtomSetImpl.mem X evs' then AtomSetImpl.add X0 (remove X evs') else evs')...
      2:{ destruct (AtomSetImpl.mem X evs') eqn:Emem...
          apply mem_iff in Emem.
          apply sub_lt_then_emp in IHSub...
          exfalso. rewrite IHSub in Emem.
          fsetdec. }
      rewrite subst_tt_intro with (X:=X)...
      2:{ rewrite dropLabel_fv_tt... }
      rewrite subst_tt_intro with (X:=X) (T2:= (dropLabel_typ lb A2) ) ...
      2:{ rewrite dropLabel_fv_tt... }
      rewrite_alist (nil ++ X0 ~ bind_sub im ++ E).
      apply sub_replacing... 2:{ get_well_form...
        inversion H;subst... constructor... }
      rewrite !open_tt_dropLabel_comm...
    +
      exists Eq. split...


      exists evs'. split...
      simpl. apply Sa_rec_eq_notin with (L:=L \u {{ X }} \u dom E)...
      intros.
      replace evs' with (if AtomSetImpl.mem X evs' then AtomSetImpl.add X0 (remove X evs') else evs')...
      2:{ destruct (AtomSetImpl.mem X evs') eqn:Emem...
          apply mem_iff in Emem. rewrite Hevs' in Emem. exfalso... }
      rewrite subst_tt_intro with (X:=X)...
      2:{ rewrite dropLabel_fv_tt... }
      rewrite subst_tt_intro with (X:=X) (T2:= (dropLabel_typ lb A2) ) ...
      2:{ rewrite dropLabel_fv_tt... }
      add_nil.
      apply sub_replacing...
      2:{ get_well_form. inversion H... constructor... }
      rewrite !open_tt_dropLabel_comm...



  - pick_fresh X. specialize_x_and_L X L.
    destruct H0 as (cm' & (evs' & (Hevs' & IHSub)) & Hc1 & Hc2).
    destruct cm'.
    +
      specialize (Hc1 eq_refl). inversion Hc1.
    +
      exists Eq. split...

      exists evs'. split...
      simpl. apply Sa_rec_eq_notin with (L:=L \u {{ X }} \u dom E)...
      intros.
      replace evs' with (if AtomSetImpl.mem X evs' then AtomSetImpl.add X0 (remove X evs') else evs')...
      2:{ destruct (AtomSetImpl.mem X evs') eqn:Emem...
          apply mem_iff in Emem. rewrite Hevs' in Emem. exfalso... }
      rewrite subst_tt_intro with (X:=X)...
      2:{ rewrite dropLabel_fv_tt... }
      rewrite subst_tt_intro with (X:=X) (T2:= (dropLabel_typ lb A2) ) ...
      2:{ rewrite dropLabel_fv_tt... }
      add_nil.
      apply sub_replacing...
      2:{ get_well_form. inversion H... constructor... }
      rewrite !open_tt_dropLabel_comm...


  - pick_fresh X. specialize_x_and_L X L.
    destruct H0 as (cm' & (evs' & (Hevs' & IHSub)) & Hc1 & Hc2).
    destruct cm'.
    +
      specialize (Hc1 eq_refl). inversion Hc1.
    +
      exists Eq. split...
      destruct (AtomSetImpl.mem X evs') eqn:Ein.
      { exists (remove X evs' `union` fv_tt ((dropLabel_typ lb (typ_mu A1)))). split...
        { rewrite Hevs'. rewrite KeySetProperties.remove_add...
          rewrite dropLabel_fv_tt... simpl.
          fsetdec. }
        simpl. apply Sa_rec_eq_in with (L:=L \u {{ X }} \u dom E)...
        intros.
        replace (add X0 (remove X evs')) with (if AtomSetImpl.mem X evs' then AtomSetImpl.add X0 (remove X evs') else evs')...
        2:{ rewrite Ein... }
        rewrite subst_tt_intro with (X:=X)...
        2:{ rewrite dropLabel_fv_tt... }
        rewrite subst_tt_intro with (X:=X) (T2:= (dropLabel_typ lb A2) ) ...
        2:{ rewrite dropLabel_fv_tt... }
        add_nil.
        apply sub_replacing...
        2:{ get_well_form. inversion H... constructor... }
        rewrite !open_tt_dropLabel_comm...
      }
      { exists (evs'). split...
        { assert (evs' [<=] evs). { apply not_mem_iff in Ein. fsetdec. }
          rewrite H0. fsetdec. }
        simpl. apply Sa_rec_eq_notin with (L:=L \u {{ X }} \u dom E \u evs')...
        intros.
        replace (evs') with (if AtomSetImpl.mem X evs' then AtomSetImpl.add X0 (remove X evs') else evs')...
        2:{ rewrite Ein... }
        rewrite subst_tt_intro with (X:=X)...
        2:{ rewrite dropLabel_fv_tt... }
        rewrite subst_tt_intro with (X:=X) (T2:= (dropLabel_typ lb A2) ) ...
        2:{ rewrite dropLabel_fv_tt... }
        add_nil.
        apply sub_replacing...
        2:{ get_well_form. inversion H... constructor... }
        rewrite !open_tt_dropLabel_comm...
      }
      

  - exists Eq. split...
    exists emp. split. { reflexivity. }
    simpl...

  - destruct tys. { exfalso... }
    destruct p. destruct (a == lb).
    +
      destruct tys.
      { exists Eq. split... exists emp. split...
        { reflexivity. }
        simpl. rewrite e. rewrite eq_dec_refl.
        constructor... }
      { exists Lt. split... exists emp. split...
        { reflexivity. }
        apply Sa_rcd_lt...
        { simpl. destruct (a == lb)... destruct p.
          destruct (a0 == lb)...
          { exfalso. subst. inversion H0;subst. simpl in H7.
            fsetdec. }
          { intros C. inversion C. }
        }
        { destruct p. inversion H0;subst.
          inversion H5;subst.
          simpl. rewrite eq_dec_refl.
          destruct (a0 == lb)...
          { apply dropLabel_uniq...  }
          { constructor... apply dropLabel_uniq...
            rewrite dropLabel_dom... }
        }
        { intros. apply H2 with (l:=l)...
          apply dropLabel_binds in H3... }
      }
    + exists Lt. split... exists emp. split...
      { reflexivity. }
      apply Sa_rcd_lt...
      { simpl. destruct (a == lb)...
        intros C. inversion C. }
      { apply dropLabel_uniq... }
      { intros. apply H2 with (l:=l)...
        apply dropLabel_binds in H3... }

  - destruct (l == lb).
    {
      subst. destruct IHSub2 as (cm2' & (evs2' & ( Hevs2' & IHSub2)) & Hc1 & Hc2).
      exists cm2'. split...
      2:{ destruct cm, cm2'...
          { specialize (Hc2 eq_refl). subst.
            destruct cm1; inversion H1.
            simpl in H1. destruct (AtomSetImpl.is_empty evs1);inversion H1. }
      }

      assert (Hu1 : uniq (tys1 ++ lb ~ T1 ++ tys1')).
      { get_well_form. inversion H11... }
      assert (Hu2 : uniq (tys2 ++ lb ~ T2 ++ tys2')).
      { get_well_form. inversion H12... }
      exists evs2'. split. { fsetdec. }
      cbv [dropLabel_typ].
      rewrite !dropLabel_app3...
      cbv [dropLabel_typ] in IHSub2.
      rewrite !dropLabel_app2 in IHSub2...
    }

    destruct IHSub1 as (cm1' & (evs1' & (Hevs1' & IHSub1)) & Hc1 & Hc2).
    destruct IHSub2 as (cm2' & (evs2' & (Hevs2' & IHSub2)) & Hc3 & Hc4).
    destruct (compose_cm cm1 cm2' evs1 evs2') eqn:Ec.
    {
      exists c. split.
      2:{
        (* cmp ok *)
        destruct cm, c...
        { exfalso. destruct cm1; inversion H1.
          { destruct cm2; inversion H1.
            destruct (AtomSetImpl.is_empty evs2);inversion H3. }
          { destruct cm2'; inversion Ec.
            specialize (Hc4 eq_refl). subst...
            rewrite H3 in H4. inversion H4.
          }
        }
      }
      exists (evs1 `union` evs2'). split. { fsetdec. }
      cbv [dropLabel_typ].
      assert (Hu1 : uniq (tys1 ++ l ~ T1 ++ tys1')).
      { get_well_form. inversion H8... }
      assert (Hu2 : uniq (tys2 ++ l ~ T2 ++ tys2')).
      { get_well_form. inversion H9... }
      rewrite !dropLabel_app...
      { apply Sa_rcd_cons with (cm1 := cm1) (cm2 := cm2')...
        + rewrite !dom_app. rewrite !dropLabel_dom...
        + rewrite !dom_app. rewrite !dropLabel_dom...
        + rewrite <- !dropLabel_app2...
      }
    }
    {
      exfalso.
      destruct cm1, cm2';inversion Ec.
      +
        destruct (AtomSetImpl.is_empty evs2') eqn:Eempty;
          try solve [inversion H3].
        apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
        destruct Eempty as [X' Eempty].
        assert (exists im_x', binds X' (bind_sub im_x') E).
        { apply bind_ex_evs with (X:=X') in IHSub2... }
        destruct H2 as [im_x' H2].
        pose proof posvar_false_simpl _ _ _ _ _ _ IHSub2 X' im_x' Eempty H2.
        exfalso. apply H4.
        apply posvar_dropLabel.
        apply soundness_posvar_simpl with (E:=E) (cm:=cm2) (evs:=evs2)...
        { 
          (* evs2 must be empty *)
          destruct cm2;inversion H1;subst...
          + apply sub_lt_then_emp in H0... rewrite H0. fsetdec.
          + destruct (AtomSetImpl.is_empty evs2) eqn:Eempty';inversion H6.
            apply is_empty_iff in Eempty'. fsetdec.
        }
      +
        destruct (AtomSetImpl.is_empty evs1) eqn:Eempty;
          try solve [inversion H3].
        specialize (Hc4 eq_refl). subst. simpl in H1.
        rewrite Eempty in H1. inversion H1.
        
    }
  - destruct (IHSub) as (cm' & (evs'' & Hevs' & IHSub') & Hcomp).
    exists cm'. split... exists evs''... split...
    rewrite <- H0...
Qed.

Theorem Sub_rcd_inversion: forall E im cm evs ls1a ls1b ls2a ls2b l T1 T2,
  Sub im cm evs E 
    (typ_rcd (ls1a ++ l ~ T1 ++ ls1b))
    (typ_rcd (ls2a ++ l ~ T2 ++ ls2b)) ->
  exists cm1 cm2 evs1 evs2,
    Sub im cm1 evs1 E T1 T2 /\
    Sub im cm2 evs2 E (typ_rcd (ls1a ++ ls1b)) (typ_rcd (ls2a ++ ls2b)) /\
    compose_cm cm1 cm2 evs1 evs2 = Some cm /\ evs1 `union` evs2 [<=] evs.
Proof with auto.
  intros.
  pose proof sub_rcd_remove _ _ l _ _ _ _ H.
  destruct H0 as (cm' & (evs' & (Hevs' & H0)) & Hc1 & Hc2).
  cbv [dropLabel_typ] in H0.
  rewrite !dropLabel_app4 in H0...
  pose proof sub_rcd_get _ _ _ _ _ _ H l T1 T2.
  destruct H1 as (cm'' & (evs'' & (Hevs'' & H1)) & Hc3 & Hc4).
  { cbv [getLabel_typ]. rewrite getLabel_get...
    get_well_form. inversion H3... }
  { cbv [getLabel_typ]. rewrite getLabel_get...
    get_well_form. inversion H4... }
  exists cm'', cm', evs'', evs'.
  split... split... split.
  { destruct cm.
    + destruct cm', cm''...
      * simpl. apply sub_lt_then_emp in H...
        destruct (AtomSetImpl.is_empty evs'') eqn:Eempty...
        apply is_not_empty_iff in Eempty. exfalso.
        apply Eempty. rewrite H in Hevs''. fsetdec.
      * simpl. apply sub_lt_then_emp in H...
        destruct (AtomSetImpl.is_empty evs') eqn:Eempty...
        apply is_not_empty_iff in Eempty. exfalso.
        apply Eempty. rewrite H in Hevs'. fsetdec.
      * 
        assert (Hu: uniq ((ls1a ++ l ~ T1 ++ ls1b))).
        { get_well_form. inversion H6... }
        apply Msub_refl_inv in H0.
        apply Msub_refl_inv in H1.
        apply Msub_lt_not_eq in H.
        exfalso. apply H.
        apply eqv_rcd...
        { inversion H0;subst...
          rewrite !dom_app in *.
          simpl. fsetdec. }
        intros. analyze_binds_uniq H2. 
        { inversion H0;subst. apply H7 with (i:=i) (T1:=T0) (T2:=T3)...
          analyze_binds H3... }
        { analyze_binds H3...
          { apply binds_In in BindsTac.
            inversion H0;subst.  exfalso.
            specialize (H6 l). destruct H6.
            rewrite dom_app in *.
            assert (l `in` dom (ls1a++ls1b))...
            rewrite dom_app in H6. fsetdec. }
          { apply binds_In in BindsTac0.
            inversion H0;subst.  exfalso.
            specialize (H6 l). destruct H6.
            rewrite dom_app in *.
            assert (l `in` dom (ls1a++ls1b))...
            rewrite dom_app in H6. fsetdec. }
        }
        { inversion H0;subst. apply H8 with (i:=i) (T1:=T0) (T2:=T3)...
          analyze_binds H3... }
    + specialize (Hc1 eq_refl). specialize (Hc3 eq_refl). subst.
      simpl...
  }
  {
    fsetdec.
  }
  { get_well_form. inversion H4... }
  { get_well_form. inversion H3... }
Qed.
