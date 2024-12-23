Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Transitivity.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  WFS E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  WFS E U.
Proof with auto.
  induction 1; intros J; analyze_binds J...
  + apply IHwf_env in BindsTac.
    add_nil.
    apply wfs_weakening...
  + injection BindsTacVal; intros; subst...
    add_nil.
    apply wfs_weakening...
  + add_nil.
    apply wfs_weakening...
Qed.

Lemma wf_typ_strengthening : forall E F x U T,
 WFS (F ++ x ~ bind_typ U ++ E) T ->
 WFS (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  + analyze_binds H...
  + apply WFS_rec with (L:=L) (im:=im).
    intros.
    rewrite_alist (([(X, bind_sub im)] ++ F) ++ E).
    apply H0...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.




Lemma wfs_open_type2: forall A G,
    WFS G (typ_mu A) -> WFS G (open_tt A (typ_mu A)).
Proof with auto.
  intros.
  dependent destruction H.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  rewrite_alist (nil ++ E).
  apply subst_tt_wfs2 with (im:=im)...
  { simpl.
    apply WFS_rec with (L:=L) (im:=im)... }
  { simpl...
    specialize_x_and_L X L... }
Qed.


Lemma Tlookup_sem: forall i T Ti, Tlookup i T = Some Ti -> binds i Ti T.
Proof with auto.
  intros.
  generalize dependent i.
  induction T;intros;simpl in *...
  -
    inversion H...
  -
    destruct a. destruct (a == i);subst...
    inversion H;subst...
Qed.



Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ WFS E T.
Proof with auto.
  intros.
  induction H...
  -
    repeat split...
    apply wf_typ_from_binds_typ with (x:=x)...
  -
    pick fresh Y.
    assert (Y \notin L) by auto.
    apply H0 in H1.
    destruct H1.
    split.
    { dependent destruction H1... }
    destruct H2.
    split...
    { apply lc_abs with (L:=L)...
      intros.
      apply H0...
      dependent destruction H1...
      apply wfs_type in H2... }
    { constructor...
      dependent destruction H1...
      rewrite_alist (nil ++ G).
      apply wf_typ_strengthening with (x:=Y) (U:=T1)... }
  -
    destruct IHtyping1...
    destruct H2.
    dependent destruction H3.
    destruct IHtyping2.
    destruct H4.
    repeat split...
  -
    destruct IHtyping.
    destruct H2.
    split...
    split...
    apply lc_fold...
    apply wfs_type with (E:=G)...
  -
    destruct IHtyping.
    destruct H1.
    split...
    split...
    apply lc_unfold...
    apply wfs_type with (E:=G)...
    apply wfs_open_type2...
  -
    destruct_hypos.
    split...
    split...
    inversion H3;subst...
    apply H7 with (i:=i)...
    apply Tlookup_sem in H0...
  -
    repeat split...
    + constructor. intros.
      pose proof binds_In _ _ _ _ H5.
      rewrite H2 in H6.
      apply binds_In_inv in H6.
      destruct H6 as [Ti ?].
      apply H4 with (ei:=x) in H6... destruct_hypos...
    + constructor...
      intros. 
      pose proof binds_In _ _ _ _ H5.
      rewrite <- H2 in H6.
      apply binds_In_inv in H6.
      destruct H6 as [ei ?].
      apply H4 with (Ti:=T') in H6... destruct_hypos...
    
  -
    destruct IHtyping.
    destruct H2.
    apply sub_regular in H0.
    repeat split...
    apply H0...
Qed.    
    
Lemma typing_weakening: forall E1 E2 E3 e T,
    typing (E1 ++ E3) e T ->
    wf_env (E1 ++ E2 ++ E3) ->
    typing (E1 ++ E2 ++ E3) e T.
Proof with simpl_env; eauto using wf_typ_from_wf_env_typ.
  intros.

  remember (E1 ++ E3) as Ht.
  generalize dependent E1.
  induction H;intros;subst...
  -
    apply typing_abs with (L:=L \u dom E1 \u dom E2 \u dom E3).
    intros.
    rewrite_alist (([(x, bind_typ T1)] ++ E1) ++ E2 ++ E3).
    apply H0...
    rewrite_alist ([(x, bind_typ T1)] ++ E1 ++ E2 ++ E3).
    constructor...
    assert (x \notin L) by auto.
    apply H in H3.
    apply typing_regular  in H3.
    destruct H3.
    dependent destruction H3.
    apply wfs_weakening...
  -
    apply typing_fold...
    apply wfs_weakening...
  -
    apply typing_sub with (S:=S) (evs:=evs) (cm:=cm).
    apply IHtyping...
    apply sub_weakening...
Qed.


Lemma strengthening_wfs_typ: forall E1 E2 S X T,
    WFS (E1 ++ X ~ bind_typ S ++ E2) T->
    WFS (E1 ++ E2) T.
Proof with auto.
  intros.
  dependent induction H...
  -
    analyze_binds H...
    { apply WFS_fvar with (im:=im)... }
    { apply WFS_fvar with (im:=im)... }
  -
    constructor...
    apply IHWFS1 with (X0:=X) (S0:=S)...
    apply IHWFS2 with (X0:=X) (S0:=S)...
  -
    apply WFS_rec with (L:=L \u {{X}}) (im:=im).
    intros.
    rewrite_alist (([(X0, bind_sub im)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (S0:=S)...
  -
    constructor...
    intros.
    apply H1 with (i:=i) (X0:=X) (S0:=S)...
Qed.    

Lemma strengthening_sub_typ: forall im cm evs E1 E2 A B X T,
    Sub im cm evs (E1 ++ X ~ bind_typ T ++ E2) A B ->
    wf_env  (E1 ++ E2 ) ->
    Sub im cm evs (E1 ++ E2) A B.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    apply strengthening_wfs_typ with (X:=X) (S:=T) ...
  -
    constructor...
    analyze_binds H0...
  -
    constructor...
    analyze_binds H0...
  -
    apply Sa_arrow with (cm1:=cm1) (cm2:=cm2)...
    apply IHSub1 with (X0:=X) (T0:=T)...
    apply IHSub2 with (X0:=X) (T0:=T)...
  -
    apply Sa_rec_lt with (L:=L \u {{X}} \u dom (E1 ++ E2)).
    intros.
    rewrite_alist (([(X0, bind_sub im)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (T0:=T)...
    constructor...
  -
    apply Sa_rec_eq_notin with (L:=L \u {{X}} \u dom (E1 ++ E2)).
    intros.
    rewrite_alist (([(X0, bind_sub im)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (T0:=T)...
    constructor...
  -
    apply Sa_rec_eq_in with (L:=L \u {{X}} \u dom (E1 ++ E2)).
    intros.
    rewrite_alist (([(X0, bind_sub im)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (T0:=T)...
    constructor...
  -
    apply Sa_rcd_lt...
    intros. apply H2 in H4.
    apply wf_typ_strengthening in H4...
  -
    apply Sa_rcd_cons with (cm1:=cm1) (cm2:=cm2)...
    + apply IHSub1 with (X0:=X) (T0:=T)...
    + apply IHSub2 with (X0:=X) (T0:=T)...
  -
    rewrite <- H0.
    apply IHSub with (X0:=X) (T0:=T)...
Qed.

Lemma binds_subst_ee_ex: forall i ei x u es,
  binds i ei (map (subst_ee x u) es) ->
  exists e, ei = subst_ee x u e /\ binds i e es.
Proof with auto.
  intros.
  induction es...
  - inversion H.
  - destruct a. simpl in H.
    analyze_binds H...
    + exists e...
    + destruct IHes as [? [? ?]]...
      exists x0...
Qed.


Lemma typing_through_subst_ee : forall F U E x T e u,
  typing (F ++ x ~ bind_typ U ++ E) e T ->
  typing E u U ->
  typing (F ++ E) (subst_ee x u e) T.
Proof with eauto.
  intros.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction H;intros;subst;simpl in *...
  -
    constructor...
    apply wf_env_strengthening in H...
  -
    destruct (x0==x)...
    + subst...
      analyze_binds_uniq H1...
      injection BindsTacVal; intros; subst.
      rewrite_alist (nil ++ F ++ E).
      apply typing_weakening...
      simpl.
      apply wf_env_strengthening in H...
    +
      analyze_binds H1...
      constructor...
      apply wf_env_strengthening in H...
      constructor...
      apply wf_env_strengthening in H...
  -
    apply typing_abs with (L:=L \u {{x}})...
    intros.
    rewrite subst_ee_open_ee_var...
    rewrite_alist (([(x0, bind_typ T1)] ++ F) ++ E).
    apply H1...
    apply typing_regular in H0...
    apply H0.
  -
    apply typing_fold...
    rewrite_alist (WFS (F ++ (x ~ bind_typ U) ++ E) (typ_mu A)) in H1.
    apply wf_typ_strengthening in H1...
  -
    apply typing_rcd_cons...
    + apply wf_env_strengthening in H...
    + rewrite dom_map...
    + intros.
      destruct (binds_subst_ee_ex _ _ _ _ _ H7)
        as [ei' [? ?]].
      subst. apply H5 with (i:=i)...
  -
    apply typing_sub with (S:=S) (evs:=evs) (cm:=cm)...
    rewrite_alist (F ++ (x ~ bind_typ U) ++ E) in H1.
    apply typing_regular in H.
    destruct H.    
    apply strengthening_sub_typ in H1...
    apply wf_env_strengthening with (x:=x) (T:=U)...
Qed.

(* still need to fix a direction of pos? *)

Lemma typing_inv_abs : forall cm evs E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2, Sub Pos cm evs E T (typ_arrow U1 U2) ->
     (exists cm2 evs2, Sub Neg cm2 evs2 E U1 S1)
  /\ exists S2, exists L, exists cm' evs', forall x, x `notin` L ->
     typing (x ~ bind_typ S1 ++ E) (open_ee e1 x) S2 /\ Sub Pos cm' evs' E S2 U2.
Proof with auto.
  intros cm evs E S1 e1 T Typ. revert cm evs.
  dependent induction Typ;intros...
  -
    clear H0. dependent induction H1.
    + split...
      { exists cm1, evs1...  }
      { exists T2. exists L. exists cm2, evs2... }
    + destruct (IHSub S1 T2 H U1 U2)...
      (* split. apply H2. apply H3. *)
  -
    assert (type T). { get_type... }
    pose proof trans_aux2 T H1 _ _ _ _ _ _ _ _ H H0.
    destruct H2 as [evs' [Hevs' H2]].
    (* assert (Sub G S (typ_arrow U1 U2)). *)
    (* apply Transitivity with (B:=T)... *)
    assert (typing G (exp_abs S1 e1) (typ_arrow U1 U2)).
    apply typing_sub with (S:=S) (evs:=evs') (cm:=seq_cm cm cm0)...
    destruct (IHTyp S1 e1 eq_refl (seq_cm cm cm0) evs' U1 U2)...
Qed.


Lemma typing_inv_fold: forall S T v,
    typing nil (exp_fold T v) S ->
    forall U cm evs, Sub Pos cm evs nil S (typ_mu U) ->
    (exists T' cm evs, typing nil v (open_tt T' (typ_mu T')) /\ Sub Pos cm evs nil (open_tt T' (typ_mu T')) (open_tt U (typ_mu U))).
Proof with auto.
  intros.
  generalize dependent U.
  dependent induction H;intros...
  -
    destruct cm.
    { pose proof H1. exists A, Lt, evs...
      split...
      apply sub_lt_then_emp in H2... rewrite H2. apply unfolding_lemma with (evs:=evs)... }
    { pose proof H1. apply Msub_refl_inv in H2.
      inversion H2;subst. 
      apply Msub_refl_equiv with (E:=empty) (im:=Pos) in H2...
      2:{ apply sub_regular in H1. destruct_hypos... }
      destruct H2 as [evs' ?].
      apply unfolding_lemma_eq in H2.
      destruct H2 as [evs'' ?].
      exists A, Eq, evs''...
    }
  -
    specialize (IHtyping T v).
    assert (exp_fold T v = exp_fold T v) by auto.
    assert (type T0). { get_type... }
    pose proof trans_aux2 _ H3 _ _ _ _ _ _ _ _ H0 H1.
    destruct_hypos...
    apply IHtyping with (U:=U) (cm:=(seq_cm cm cm0)) (evs:=x) in H2...
Qed.

Lemma typing_inv_rcd: forall S vs,
  typing nil (exp_rcd vs) S ->
  forall U cm evs, Sub Pos cm evs nil S (typ_rcd U) ->
  (forall i ei ti, binds i ei vs -> binds i ti U -> typing nil ei ti).
Proof with auto.
  intros.
  generalize dependent U.
  generalize dependent i.
  generalize dependent ei.
  generalize dependent ti.
  dependent induction H;intros...
  - pose proof sub_typ_label_incl  H6.
    pose proof binds_In _ _ _ _ H7.
    rewrite H8 in H9.
    apply binds_In_inv in H9.
    destruct H9 as [ti' ?].
    destruct (binds_split _ _ _ _ H9) as [tys1 [tys2 ?]].
    destruct (binds_split _ _ _ _ H7) as [us1 [us2 ?]].
    subst.
    apply Sub_rcd_inversion_complete in H6.
    destruct H6 as (cm1' & cm2' & evs1 & evs2 & ? & ? & ? & ? ).
    apply typing_sub with (S:=ti') (evs:=evs1) (cm:=cm1')...
    apply H3 with (i0:=i)...
  - specialize (IHtyping vs).
    assert (type T). { get_type... }
    pose proof trans_aux2 _ H4 _ _ _ _ _ _ _ _ H0 H2.
    destruct_hypos...
    apply IHtyping with (ti:=ti) (ei:=ei) (i:=i) in H6 ...
Qed.



Definition flip_bind (b:binding) : binding :=
  match b with
  | bind_typ T => bind_typ T
  | bind_sub im => bind_sub (flip_im im)
  end.

Lemma flip_bind_binds: forall E x b,
    binds x b E ->
    binds x (flip_bind b) (map flip_bind E).
Proof with auto.
  intros.
  induction E...
Qed.

Lemma flip_bind_WFS: forall E T,
    WFS E T ->
    WFS (map flip_bind E) T.
Proof with auto.
  intros.
  induction H...
  - apply WFS_fvar with (im:=flip_im im).
    apply flip_bind_binds in H...
  - apply WFS_rec with (L:=L) (im:=flip_im im)...
Qed.

Lemma flip_bind_wf_env: forall E,
    wf_env E ->
    wf_env (map flip_bind E).
Proof with auto.
  intros.
  induction H...
  + simpl.
    constructor...
  + simpl.
    constructor...
    apply flip_bind_WFS...
Qed.



Lemma Sub_flip_eq: forall im cm evs E S T,
    Sub im cm evs E S T ->
    Sub (flip_im im) cm evs (map flip_bind E) S T.
Proof with auto using flip_bind_wf_env, flip_bind_WFS.
  intros.
  dependent induction H...
  - 
    apply Sa_fvar_pos...
    apply flip_bind_binds in H0...
  -
    apply Sa_fvar_neg...
    apply flip_bind_binds in H0...
  -
    apply Sa_arrow with (cm1:=cm1) (cm2:=cm2)...
  -
    apply Sa_rec_lt with (L:=L) (im:=flip_im im)...
  -
    apply Sa_rec_eq_notin with (L:=L) (im:=flip_im im)...
  -
    apply Sa_rec_eq_in with (L:=L) (im:=flip_im im)...
  -
    apply Sa_rcd_lt...
    induction tys;intros.
    + inversion H3.
    + destruct a. inversion H3;subst.
      { inversion H4;subst.
        apply flip_bind_WFS. eapply H2...
      }
      {
        inversion H0;subst.
        eapply IHtys with (l:=l)...
        { destruct tys... intros C. inversion C. }
        intros. eapply H2 with (l:=l0)...
      }
  -
    apply Sa_rcd_cons with (cm1:=cm1) (cm2:=cm2)...
  -
    rewrite <- H0...
Qed.



Lemma tlookup_sem: forall i T Ti, tlookup i T = Some Ti -> binds i Ti T.
Proof with auto.
  intros.
  generalize dependent i.
  induction T;intros;simpl in *...
  -
    inversion H...
  -
    destruct a. destruct (a == i);subst...
    inversion H;subst...
Qed.

Lemma Tlookup_sem_inv: forall i T Ti, 
  uniq T ->
  binds i Ti T -> Tlookup i T = Some Ti.
Proof with auto.
  intros.
  generalize dependent i.
  induction T;intros;simpl in *...
  -
    inversion H0...
  -
    destruct a. analyze_binds_uniq H0.
    +  rewrite eq_dec_refl...
    + simpl in H1. destruct (a == i). { subst. fsetdec. }
      apply IHT... inversion H...
Qed.



Lemma preservation : forall e e' T,
    typing nil e T ->
    step e e' ->
    typing nil e' T.
Proof with auto.
  intros.
  generalize dependent e'.
  dependent induction H;intros;try solve [dependent destruction H1;auto|inversion H0]...
  -
    dependent destruction H1...
    +
      dependent destruction H.
      pick fresh Y.
      rewrite subst_ee_intro with (x:=Y)...
      rewrite_alist (empty ++ empty).
      apply typing_through_subst_ee with (U:=T1)...
      apply H...
      apply typing_inv_abs with (U1:=T1) (U2:=T2) (cm:=cm) (evs:=evs) in H...
      destruct H. destruct H as [cm2 [evs2 ?]].
      destruct H4  as [S2 [L [cm' [evs' ?]]]].
      pick fresh Y.
      rewrite subst_ee_intro with (x:=Y)...
      rewrite_alist (nil ++ empty).
      apply typing_through_subst_ee with (U:=T)...
      { specialize_x_and_L Y L.
        destruct H4.
        apply typing_sub with (S:=S2) (evs:=evs') (cm:=cm')...
        { apply sub_weakening...
          apply typing_regular in H4. destruct_hypos... }
      }
      { apply typing_sub with (S:=T1) (evs:=evs2) (cm:=cm2)...
        apply Sub_flip_eq in H... }
    +
      apply typing_app with (T1:=T1)...
    +
      apply typing_app with (T1:=T1)...
  -
    dependent destruction H0...
    dependent destruction H...
    apply typing_inv_fold with (U:=T) (cm:=cm) (evs:=evs)  in H...
    destruct H as [T' [cm' [evs' ?]]]. destruct_hypos.
    apply typing_sub with (S:=open_tt T' (typ_mu T')) (evs:=evs') (cm:=cm')...
  -
    apply Tlookup_sem in H0.
    dependent destruction H1...
    +
      pose proof Msub_refl empty Pos (typ_rcd T).
      destruct H3 as [evs' ?]...
      { apply typing_regular in H. destruct_hypos.
        get_type... }
      { apply typing_regular in H. destruct_hypos... }
      pose proof typing_inv_rcd _ _ H T _ _ H3.
      apply tlookup_sem in H2.
      apply H4 with (i:=i)...
    +
      apply typing_proj with (T:=T)...
      apply Tlookup_sem_inv... 
      { apply typing_regular in H. destruct_hypos. inversion H3... }
  -
    inversion H5;subst.
    apply typing_rcd_cons...
    + apply uniq_insert_mid...
      { apply uniq_remove_mid with (F:=l~e1)... }
      { apply fresh_mid_head in H0... }
      { apply fresh_mid_tail in H0... }
    + rewrite !dom_app in *. simpl in *. fsetdec.
    + intros.
      analyze_binds H9.
      * apply H3 with (i:=i)...
      * apply H4 with (i:=l) (ei:=e1)...
      * apply H3 with (i:=i)...
  -
    apply typing_sub with (S:=S) (cm:=cm) (evs:=evs)...
Qed.

Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  typing empty e (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_arrow U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  dependent induction H; subst; eauto.
Qed.

Lemma canonical_form_rcd: forall e T,
  value e ->
  typing empty e (typ_rcd T) ->
  exists vs, e = exp_rcd vs /\ dom T [<=] dom vs /\
      forall i ei, binds i ei vs -> value ei.
Proof with auto.
  intros e T Val Typ.
  dependent induction Typ;try solve [inversion Val]...
  + inversion Val;subst...
    exists es. repeat split... 
    { rewrite H2. reflexivity. }
  + 
    pose proof sub_rcd_canonical _ _ _ _ _ _ H.
    destruct_hypos.
    subst.
    destruct (IHTyp x)... destruct_hypos.
    exists x0. repeat split...
    apply sub_typ_label_incl in H. fsetdec.
Qed.
    
Lemma canonical_form_fold : forall e U,
  value e ->
  typing empty e (typ_mu U) ->
  exists V, exists e1, exists cm evs, (Sub Pos evs cm empty (typ_mu V) (typ_mu U) /\ value e1 /\ e = exp_fold (typ_mu V) e1).
Proof with auto.
  intros e U Val Typ.
  remember empty as E.
  remember (typ_mu U) as T.
  assert (WFS E T).
  {
    apply typing_regular in Typ.
    destruct Typ.
    destruct H0... }
  revert U HeqT HeqE.
  induction Typ; intros U EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  -
    dependent destruction Val.
    exists A...
    exists e...
    destruct (Msub_refl empty Pos (typ_mu A))... exists x, Eq.
    repeat split...
  -
    inversion H; subst; eauto.
    dependent induction H0.
    + 
      apply IHTyp with (U:=A1) in Val... 2:{ apply typing_regular in Typ. destruct_hypos... }
      destruct_hypos... exists x, x0.
      assert (Sub Pos Lt evs empty (typ_mu A1) (typ_mu U)). { apply Sa_rec_lt with (L:=L)... }
      assert (type (typ_mu A1)) by (get_type;auto).
      pose proof trans_aux2 _ H7 _ _ _ _ _ _ _ _ H2 H6.
      destruct_hypos. exists x3, (seq_cm x2 Lt)...
    + apply IHTyp with (U:=A1) in Val... 2:{ apply typing_regular in Typ. destruct_hypos... }
      destruct_hypos... exists x, x0.
      assert (Sub Pos Eq evs empty (typ_mu A1) (typ_mu U)). { apply Sa_rec_eq_notin with (L:=L)... }
      assert (type (typ_mu A1)) by (get_type;auto).
      pose proof trans_aux2 _ H7 _ _ _ _ _ _ _ _ H2 H6.
      destruct_hypos. exists x3, (seq_cm x2 Eq)...
    + apply IHTyp with (U:=A1) in Val... 2:{ apply typing_regular in Typ. destruct_hypos... }
      destruct_hypos... exists x, x0.
      assert (Sub Pos Eq (evs \u fv_tt A1) empty (typ_mu A1) (typ_mu U)). { apply Sa_rec_eq_in with (L:=L)... }
      assert (type (typ_mu A1)) by (get_type;auto).
      pose proof trans_aux2 _ H7 _ _ _ _ _ _ _ _ H2 H6.
      destruct_hypos. exists x3, (seq_cm x2 Eq)...
    + apply IHSub with (L:=L) (im:=im) ...
Qed.

Lemma tlookup_sem_inv: forall i T Ti, 
  uniq T ->
  binds i Ti T -> tlookup i T = Some Ti.
Proof with auto.
  intros.
  induction T.
  - inversion H0.
  - destruct a. analyze_binds_uniq H0.
    + simpl. rewrite eq_dec_refl...
    + simpl. simpl in H1. destruct (a == i)... { fsetdec. }
      apply IHT... inversion H...
Qed.

Lemma typing_rcd_uniq: forall E e T,
    typing E (exp_rcd e) T ->
    uniq e.
Proof with auto.
  intros.
  dependent induction H...
Qed.


Lemma dom_add_drop': forall {A B:Type} a (t1:A)(t2:B) l1 l2,
  uniq (a ~ t1 ++ l1) ->
  uniq (a ~ t2 ++ l2) ->
  add a (dom l1) [=] add a (dom l2) ->
  dom l1 [=] dom l2.
Proof with auto.
  intros.
  inversion H;inversion H0;subst.
  assert (remove a (add a (dom l1)) [=] remove a (add a (dom l2))).
  { rewrite H1... reflexivity. }
  rewrite KeySetProperties.remove_add in H2...
  rewrite KeySetProperties.remove_add in H2...
Qed.



Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', step e e'.
Proof with eauto.
  intros.
  dependent induction H...
  -
    inversion H0...
  -
    left.
    constructor.
    pick fresh Y.
    assert (Y \notin L) by auto.
    apply H in H1...
    apply typing_regular in H1.
    destruct H1.
    destruct H2.
    apply lc_abs with (L:=L).
    intros.
    apply H in H4.
    apply typing_regular in H4.
    apply H4.
    apply wf_typ_from_wf_env_typ in H1.
    apply wfs_type with (E:=empty)...
  -
    right.
    assert (empty ~= empty) by auto.
    apply IHtyping1 in H1.
    destruct H1...
    assert (empty ~= empty) by auto.
    apply IHtyping2 in H2...
    destruct H2...
    apply canonical_form_abs with (U1:=T1) (U2:=T2) in H1...
    destruct H1.
    destruct H1.
    exists (open_ee x0 e2).
    subst.
    apply step_beta...
    apply typing_regular in H.
    apply H.
    destruct H2.
    exists (exp_app e1 x).
    apply step_app2...
    destruct H1.
    exists (exp_app x e2).
    apply step_app1...
    apply typing_regular in H0.
    apply H0.
  -
    assert (empty ~= empty) by auto.
    apply IHtyping in H1.
    destruct H1.
    left.
    constructor...
    apply wfs_type in H0...
    right.
    destruct H1.
    exists (exp_fold (typ_mu A) x).
    constructor...
    apply typing_regular in H.
    destruct H.
    destruct H2.
    apply wfs_type in H0...
  -
    assert (empty ~= empty) by auto.
    apply IHtyping in H0.
    right.
    destruct H0...
    +
      apply canonical_form_fold with (U:=T) in H0...
      destruct_hypos.
      exists x0...
      rewrite H2.
      apply step_fld...
      apply sub_regular in H0.
      apply wfs_type with (E:=empty)...
      apply H0.
      apply typing_regular in H.
      apply wfs_type with (E:=empty)...
      apply H.
    +
      destruct H0.
      exists (exp_unfold (typ_mu T) x).
      apply step_unfold...
      apply typing_regular in H...
      apply wfs_type with (E:=empty)...
      apply H.
  -
    destruct IHtyping...
    +
      pose proof canonical_form_rcd _ _ H1 H.
      destruct H2 as [vs [? [? ?]]].
      subst.
      destruct (Msub_refl empty Pos (typ_rcd T)) as [evs ?]...
      { apply typing_regular in H. destruct_hypos... get_type... }
      { apply typing_regular in H. destruct_hypos... }
      pose proof typing_inv_rcd _ _ H T _ _ H2.
      apply Tlookup_sem in H0.
      apply binds_In in H0. rewrite H3 in H0.
      apply binds_In_inv in H0. destruct H0.
      right. exists x. constructor...
      apply tlookup_sem_inv...
      { apply typing_rcd_uniq in H... }
    +
      right.
      destruct H1.
      exists (exp_rcd_proj x i).
      apply step_proj...
  -
    generalize dependent tys.
    induction es;intros.
    + left. constructor... intros. inversion H5.
    + destruct a as [l e0]. assert (l `in` dom tys).
      { rewrite <- H2. simpl... }
      apply binds_In_inv in H5. destruct H5 as [T0 ?].
      destruct (H4 _ e0 _ H5)...
      2:{ destruct H6 as [e0' ?].
          right. exists (exp_rcd ((l,e0')::es)).
          rewrite_alist (nil ++ l ~ e0 ++ es).
          rewrite_alist (nil ++ l ~ e0' ++ es).
          apply step_rcd_head...
      }
      inversion H0;subst.
      apply binds_split in H5.
      destruct H5 as [tys1 [tys2 ?]]. subst.
      destruct (IHes H9) with (tys := tys2 ++ tys1)...
      { eapply dom_add_drop' with (a:=l) (t1:=e0) (t2:=T0)...
        + apply uniq_reorder_2...
        + simpl in *. rewrite dom_app in *.
          simpl in *. clear - H2. fsetdec.
      }
      * left. inversion H5;subst.
        constructor. intros. inversion H7;subst...
        inversion H10;subst...
      * right. destruct H5 as [es' ?].
        inversion H5;subst.
        exists (exp_rcd ((l~e0 ++ es1) ++ l0 ~ e2 ++ es2)).
        rewrite_alist ((l~e0 ++es1) ++ l0~e1 ++es2).
        constructor...
        constructor...
Qed.