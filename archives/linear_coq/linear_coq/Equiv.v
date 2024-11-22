Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export LinearRule.


Inductive binding : Set :=
  | bind_sub : binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).
Notation empty := (@nil (atom * binding)).



Inductive WFS : env -> typ -> Prop :=
| WFS_top : forall E, WFS E typ_top
| WFS_nat : forall E, WFS E typ_nat
| WFS_fvar : forall X E ,
    binds X (bind_sub) E ->
    WFS E (typ_fvar X)
| WFS_arrow : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_arrow A B)
| WFS_rec : forall L E A,
    (* (forall X , X \notin L -> forall im, 
        WFS (X ~ bind_sub im ++ E) (open_tt A (typ_rcd X (open_tt A X)))) -> *)
      (forall  X , X \notin L -> 
        WFS (X ~ bind_sub ++ E) (open_tt A X)) ->
      WFS E (typ_mu A).


Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) ,
      wf_env E ->
      X \notin dom E ->
      wf_env (X ~ bind_sub ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      WFS E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).


Inductive sub_amber2: env -> typ -> typ -> Prop :=
| sam2_nat: forall E,
    wf_env E ->
    sub_amber2 E typ_nat typ_nat
| sam2_top: forall E A,
    WFS E A ->
    wf_env E ->
    sub_amber2 E A typ_top
| sam2_fvar: forall E X,
    binds X (bind_sub) E ->
    wf_env E ->
    sub_amber2 E (typ_fvar X) (typ_fvar X)
| sam2_arrow: forall E A1 A2 B1 B2,
    sub_amber2 E B1 A1 ->
    sub_amber2 E A2 B2 ->
    sub_amber2 E (typ_arrow A1 A2) (typ_arrow B1 B2)
| sam2_rec: forall E A B L,
    (forall X , X \notin L -> 
                sub_amber2 (X ~ bind_sub ++ E) (open_tt A X) (open_tt B X)) ->
    (forall X , X \notin L ->
                posvar Pos X (typ_mu A) (typ_mu B)) ->
    sub_amber2 E (typ_mu A) (typ_mu B)
.

#[export]
Hint Constructors sub_amber2 WFS wf_env : core.

Lemma sub_amber2_regular: forall E A B,
  sub_amber2 E A B -> wf_env E /\ WFS E A /\ WFS E B.
Proof with auto.
  intros.
  induction H...
  - destruct_hypos...
  - repeat split...
    + pick_fresh X. specialize_x_and_L X L.
      destruct_hypos. inversion H0...
    + apply WFS_rec with (L:=L)...
      intros. apply H0...
    + apply WFS_rec with (L:=L)...
      intros. apply H0...
Qed.

Lemma WFS_type: forall E A,
  WFS E A -> type A.
Proof with auto.
  intros.
  induction H...
  - apply type_mu with (L:=L)...
Qed.


Definition drop_im b :=
  match b with
  | Rules.bind_sub _ => bind_sub
  | Rules.bind_typ t => bind_typ t
  end.

Definition drop_im_env := map drop_im.

Lemma binds_drop: forall E X b,
  binds X b E -> binds X (drop_im b) (drop_im_env E).
Proof with auto.
  intros.
  induction E...
  simpl in H. destruct a. inversion H;subst.
  - inversion H0;subst.
    left...
  - simpl. right. apply IHE...
Qed.

Lemma WFS_drop_sound: forall E A,
  Rules.WFS E A -> WFS (drop_im_env E) A.
Proof with auto.
  intros.
  induction H...
  - apply WFS_fvar.
    apply binds_drop in H...
  - apply WFS_rec with (L:=L)...
Qed.



Lemma drop_wf_env_sound: forall E,
  Rules.wf_env E -> wf_env (drop_im_env E).
Proof with auto.
  intros.
  induction H...
  - simpl. constructor... unfold drop_im_env.
    rewrite dom_map...
  - simpl. constructor...
    2:{  unfold drop_im_env. rewrite dom_map... }
    apply WFS_drop_sound...
Qed.


Theorem pos_esa_sound: forall im cm evs E A B,
  Sub im cm evs E A B ->
  sub_amber2 (map drop_im E) A B.
Proof with eauto using drop_wf_env_sound, WFS_drop_sound.
  intros.
  induction H...
  -
    apply sam2_fvar...
    apply binds_drop in H0...
  -
    apply sam2_fvar...
    apply binds_drop in H0...
  -
    apply sam2_rec with (L:=L \u evs \u dom E)...
    { intros. apply H0... }
    { intros. apply pos_rec with (L:=L \u evs).
      + intros. specialize_x_and_L Y L.
        apply soundness_posvar_fresh with (im':=Pos) (X:=X) in H...
      + intros. specialize_x_and_L Y L.
        apply soundness_posvar with (X:=Y) in H...
        apply H...
    }
  -
    apply sam2_rec with (L:=L \u evs \u dom E)...
    { intros. apply H0... }
    { intros. apply pos_rec with (L:=L \u evs).
      + intros. specialize_x_and_L Y L.
        apply soundness_posvar_fresh with (im':=Pos) (X:=X) in H...
      + intros. specialize_x_and_L Y L.
        apply soundness_posvar with (X:=Y) in H...
        apply H...
    }
  -
    assert (Sub im Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2))...
    apply Msub_eq_sem in H1. inversion H1. subst. 
    apply sam2_rec with (L:=L \u evs \u dom E \u fv_tt A2)...
    { intros. apply H0... }
    { intros. apply pos_rec_t with (L:=L \u evs)...
      intros. specialize_x_and_L Y L. get_type...
    }
Qed.

Inductive extend_env: env -> Rules.env -> Prop :=
| extend_nil: extend_env nil nil
| extend_sub: forall E1 E2 X im,
    extend_env E1 E2 ->
    extend_env (X ~ bind_sub ++ E1) ( X ~ Rules.bind_sub im ++ E2).

#[export]
Hint Constructors extend_env : core.



Lemma extend_env_dom: forall E E',
  extend_env E E' -> dom E [=] dom E'.
Proof with auto.
  intros.
  induction H...
  simpl. { reflexivity. }
  simpl. fsetdec.
Qed.

Lemma extend_wf_env: forall E E',
  extend_env E E' -> wf_env E -> Rules.wf_env E'.
Proof with eauto.
  intros.
  induction H...
  - inversion H0;subst...
    constructor...
    rewrite <- (extend_env_dom _ _ H)...
Qed.

Lemma extend_env_binds:
  forall E E' X b,
    extend_env E E' ->
    binds X b E ->
    exists im, binds X (Rules.bind_sub im) E'.
Proof with auto.
  intros. generalize dependent X.
  generalize dependent b.
  induction H;intros...
  - inversion H0.
  - analyze_binds H0.
    + exists im...
    + apply IHextend_env in BindsTac.
      destruct BindsTac...
      exists x...
Qed.
    

Lemma WFS_extend: forall E E' A,
  WFS E A -> extend_env E E' ->
  Rules.WFS E' A.
Proof with auto.
  intros. generalize dependent E'.
  induction H;intros...
  - apply extend_env_binds with (E':=E') in H;try eassumption.
    destruct H. eauto.
  - apply Rules.WFS_rec with (L:=L) (im:=Pos)...
Qed.

Lemma uniq_from_wf_env: forall E,
  wf_env E -> uniq E.
Proof with auto.
  intros.
  induction H...
Qed.




Theorem pos_esa_complete: forall E A B,
    sub_amber2 E A B ->
    forall im E',
    well_bind_env im E' A B ->
    extend_env E E' ->
    exists cm evs, Sub im cm evs E' A B.
Proof with eauto using extend_wf_env.
  intros. 
  generalize dependent E'.
  generalize dependent im.
  induction H;intros...
  -
    destruct (decide_typ A typ_top)...
    + subst...
    + exists Lt, emp...
      apply Sa_top_lt...
      apply WFS_extend with (E:=E)...
  -
    apply extend_env_binds with (E':=E') in H...
    destruct H as [im' ?].
    destruct im, im'...
    (* apply well_bind_env_fvar_x in H1. *)
  -
    destruct IHsub_amber2_1 with (E':=E') (im:=flip_im im)
      as [cm1 [evs1 Hsub1]]...
    { hnf. hnf in H1. intros.
      apply H1 in H3. inversion H3;subst.
      destruct im, im_x;simpl in *...
    }
    destruct IHsub_amber2_2 with (E':=E') (im:=im)
      as [cm2 [evs2 Hsub2]]...
    { hnf. hnf in H1. intros.
      apply H1 in H3. inversion H3;subst.
      destruct im, im_x;simpl in *...
    }
    destruct ((compose_cm cm1 cm2 evs1 evs2)) eqn:Ecomp.
    { exists c, (evs1 `union` evs2)... } 
    (* if result is None *)
    destruct cm1, cm2;inversion Ecomp;subst.
    + destruct (AtomSetImpl.is_empty evs2) eqn:Eempty;
        try solve [inversion H4]...
      apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
      destruct Eempty as [X' Eempty].
      assert (exists im_x', binds X' (Rules.bind_sub im_x') E').
      { apply bind_ex_evs with (X:=X') in Hsub2... }
      destruct H3 as [im_x' H3].
      pose proof posvar_false_simpl _ _ _ _ _ _ Hsub2 _ _ Eempty H3.
      pose proof H1 _ _ H3. inversion H6;subst.
      exfalso...
    + destruct (AtomSetImpl.is_empty evs1) eqn:Eempty;
        try solve [inversion H4]...
      apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
      destruct Eempty as [X' Eempty].
      assert (exists im_x', binds X' (Rules.bind_sub im_x') E').
      { apply bind_ex_evs with (X:=X') in Hsub1... }
      destruct H3 as [im_x' H3].
      pose proof posvar_false_simpl _ _ _ _ _ _ Hsub1 _ _ Eempty H3.
      pose proof H1 _ _ H3. inversion H6;subst.
      exfalso. apply H5.
      destruct im, im_x';simpl in *...
  -
    assert (Hasub: sub_amber2 E (typ_mu A) (typ_mu B))...
    pick_fresh X. specialize_x_and_L X L.
    inversion H1;subst.
    +
      (* posvar *)
      destruct H0 with (im:=im) (E':=X ~ Rules.bind_sub im ++ E') 
        as [cm' [evs' Hsub]]...
      { hnf. intros.
        analyze_binds_uniq H4. 
        { simpl. constructor...
          apply Variance.uniq_from_wf_env.
          apply extend_wf_env with (E:=E)...
          apply sub_amber2_regular in H.
          destruct_hypos. inversion H;subst...
        }
        + inversion BindsTacVal;subst.
          rewrite xor_prop_refl.
          pick_fresh Z. specialize_x_and_L Z (L0 \u {{X}}).
          rewrite subst_tt_intro with (X:=Z) (T2:=A)...
          rewrite subst_tt_intro with (X:=Z) (T2:=B)...
          apply pos_rename_1...
          solve_notin.
        + apply H2 in BindsTac. inversion BindsTac;subst.
          * pick_fresh Z. specialize_x_and_L Z (L1 \u {{X0}}).
            rewrite subst_tt_intro with (X:=Z) (T2:=A)...
            rewrite subst_tt_intro with (X:=Z) (T2:=B)...
            apply pos_rename_fix...
          * pick_fresh Z. specialize_x_and_L Z (L1 \u {{X0}}).
            apply posvar_self_notin...
            { apply sub_amber2_regular in H. destruct_hypos.
              apply WFS_type with (E:=(X ~ bind_sub ++ E))...
            }
            { solve_notin. }
      }
      destruct cm'.
      * exists Lt, evs'.
        apply Sa_rec_lt with (L:=L \u {{X}} \u fv_tt A \u fv_tt B\u dom E).
        intros.
        rewrite_alist (nil ++ (X ~ Rules.bind_sub im ++ E')) in Hsub.
        apply sub_replacing with (Y:=X0) in Hsub...
        2:{ eapply extend_wf_env with (E:=X0~bind_sub++E)...
            { simpl. constructor... }
            apply sub_amber2_regular in H. destruct_hypos...
            inversion H;subst. constructor...
        }
        rewrite <- subst_tt_intro in Hsub...
        rewrite <- subst_tt_intro in Hsub...
        destruct (AtomSetImpl.mem X evs') eqn:Emem...
        { apply mem_iff in Emem.
          pose proof posvar_false_simpl _ _ _ _ _ _ Hsub X0 im.
          exfalso. apply H5... rewrite xor_prop_refl.
          inversion H1;subst.
          { pick_fresh Z. specialize_x_and_L Z (L1 \u {{X}}).
            rewrite subst_tt_intro with (X:=Z) (T2:=A)...
            rewrite subst_tt_intro with (X:=Z) (T2:=B)...
            apply pos_rename_1...
            solve_notin. }
          { apply Msub_lt_not_eq in Hsub. exfalso... }
        }
      *
        exists Eq.
        apply Msub_eq_sem in Hsub.
        apply open_tt_fresh_eq_inv in Hsub...
        subst. 
        apply sub_amber2_regular in Hasub. destruct_hypos.
        apply Msub_refl...
        { apply posvar_regular in H1. destruct_hypos... }
        { apply WFS_extend with (E:=E)... }
        
    +
      (* self *)
      exists Eq.
      apply sub_amber2_regular in Hasub. destruct_hypos.
      apply Msub_refl.
      { apply extend_wf_env with (E:=E)... }
      { apply posvar_regular in H1. destruct_hypos... }
      { apply WFS_extend with (E:=E)... }
Qed.


Theorem pos_esa_complete_final: forall A B,
    sub_amber2 nil A B ->
    exists cm evs, Sub Pos cm evs nil A B.
Proof with eauto.
  intros.
  apply pos_esa_complete with (E:=nil) (im:=Pos) (E':=nil) in H...
  { hnf. intros. inversion H0. }
Qed.