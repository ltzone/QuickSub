Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export LinearRule.


Lemma wf_env_strengthening: forall E1 E2 X im,
  wf_env (E1 ++ X ~ bind_sub im ++ E2) ->
  wf_env (E1 ++ E2).
Proof with auto.
  intros.
  induction E1...
  - inversion H;subst...
  - inversion H;subst...
    + destruct im;simpl in *... constructor... constructor...
    + simpl. constructor... admit.
Admitted.

Lemma mode_choose_refl:
forall {A : Type} (im : IsoMode) (C D : A),
mode_choose im im C D = C.
Proof with auto.
  destruct im...
Qed.


Theorem linear_subst_lt: forall E1 X im_x E2 im cm evs A B C D,
  Sub im cm evs (E1 ++ X ~ bind_sub im_x ++ E2) A B ->
  X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2) \u evs ->
  Sub im_x Lt emp E2 (mode_choose im im_x C D) (mode_choose im im_x D C ) ->
  exists cm' evs', 
    Sub im cm' evs' (E1 ++ E2) (subst_tt X (mode_choose im im_x C D) A) (subst_tt X (mode_choose im im_x D C) B).
Proof with auto.
  intros. generalize dependent C.
  generalize dependent D.
  dependent induction H;intros;simpl in H0,H1; try solve [exfalso;fsetdec]...

  -
    admit.
    
  -
    admit.
    
  -
    admit.

  -
    simpl. destruct (X0 == X).
    +
      subst X0. analyze_binds_uniq H0...
      inversion BindsTacVal;subst...
      exists Lt, emp... rewrite !mode_choose_refl in *...
      admit.
    +
      exists Eq, emp. constructor... admit. analyze_binds_uniq H0...

  - 
    simpl. destruct (X0 == X).
    +
      subst X0. analyze_binds_uniq H0...
    +
      exists Eq, {{ X0 }}. apply Sa_fvar_neg... admit. analyze_binds_uniq H0...
  
  -
    




  -
    assert (X = X0) by fsetdec.
    subst X0. analyze_binds_uniq H0...
    inversion BindsTacVal;subst... simpl.
    rewrite eq_dec_refl. apply wf_env_strengthening in H. 
      rewrite_alist (nil ++ E1 ++ E2).
      eapply sub_weakening;try eassumption...
  -
    simpl in H2. simpl in H3.
    apply union_iff in H2, H3.
    destruct H2, H3...
    +

    epose proof (IHSub1 E1 X im_x E2 JMeq_refl _ _ C D).
    Unshelve. all: try fsetdec.
    