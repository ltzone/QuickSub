Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Variance.


Inductive equiv : typ -> typ -> Prop :=
| eqv_nat : equiv typ_nat typ_nat
| eqv_top : equiv typ_top typ_top
| eqv_var : forall X,
    equiv (typ_fvar X) (typ_fvar X)
| eqv_arrow : forall A1 A2 B1 B2,
    equiv A1 B1 ->
    equiv A2 B2 ->
    equiv (typ_arrow A1 A2) (typ_arrow B1 B2)
| eqv_mu : forall A B L,
    (forall X, X \notin L ->
               equiv (open_tt A X) (open_tt B X)) ->
    equiv (typ_mu A) (typ_mu B)
| eqv_rcd : forall l1 l2,
    dom l1 [=] dom l2 ->
    (forall i T1 T2, binds i T1 l1 -> 
                binds i T2 l2 ->
                equiv T1 T2) ->
    equiv (typ_rcd l1 ) (typ_rcd l2)
.




Inductive posvar: IsoMode -> atom -> typ -> typ -> Prop :=
| pos_nat: forall X m,
    posvar m X typ_nat typ_nat
| pos_top: forall X A m,
    type A ->
    posvar m X A typ_top
| pos_top_flip: forall X A m,
    type A ->
    posvar m X typ_top A
| pos_fvar_x: forall X,
    posvar Pos X (typ_fvar X) (typ_fvar X)
| pos_fvar_y: forall X Y m,
    X <> Y ->
    posvar m X (typ_fvar Y) (typ_fvar Y)
| pos_arrow: forall X m A1 A2 B1 B2,
    posvar (flip_im m) X B1 A1 ->
    posvar m X A2 B2 ->
    posvar m X (typ_arrow A1 A2) (typ_arrow B1 B2)
| pos_rec: forall X m A B L,
    (forall Y, Y \notin L \u {{X}} ->
               posvar m X (open_tt A Y) (open_tt B Y)) ->
     (forall Y, Y \notin L \u {{X}} ->
               posvar Pos Y (open_tt A Y) (open_tt B Y)) -> 
    posvar m X (typ_mu A) (typ_mu B)
| pos_rec_t : forall A B X m L,
    X \notin fv_tt A ->
    X \notin fv_tt B ->
    (forall Y, Y \notin L \u {{X}} -> type (open_tt A Y)) ->
    (forall Y, Y \notin L \u {{X}} -> type (open_tt B Y)) ->
    equiv (typ_mu A) (typ_mu B) ->
    posvar m X (typ_mu A) (typ_mu B)
| pos_rcd : forall X m l1 l2,
    type (typ_rcd l1) -> type (typ_rcd l2) ->
    (* to include all fields *)
    (forall l T1 T2, binds l T1 l1 -> 
                binds l T2 l2 ->
                posvar m X T1 T2) ->
                (* TODO: check if enough *)
    posvar m X (typ_rcd l1) (typ_rcd l2)
.
#[global] Hint Constructors posvar equiv  : core.




Lemma equiv_refl: forall E A,
    WFS E A ->
    equiv A A.
Proof with auto.
  intros. induction H...
  -
    apply eqv_mu with (L:=L)...
  -
    apply eqv_rcd. reflexivity.
    intros.
    pose proof binds_unique _ _ _ _ _ H2 H3 H.
    subst. apply H1 in H2...
Qed.

Lemma equiv_symm: forall A B,
    equiv A B ->
    equiv B A.
Proof with auto.
  intros. induction H...
  -
    apply eqv_mu with (L:=L)...
  -
    apply eqv_rcd. symmetry...
    intros.
    apply H1 with (i:=i)...
Qed.

Lemma equiv_trans: forall A B C,
    equiv A B ->
    equiv B C ->
    equiv A C.
Proof with auto.
  intros.
  generalize dependent C.
  induction H;intros...
  -
    inversion H1;subst...
  -
    inversion H1;subst...
    apply eqv_mu with (L:=L \u L0).
    intros. specialize_x_and_L X L.
    specialize_x_and_L X L0.
    apply H0...
  -
    inversion H2;subst...
    apply eqv_rcd...
    { rewrite H... }
    intros.
    assert (exists T, binds i T l2).
    { apply binds_In in H3. rewrite H in H3.
      apply binds_In_inv in H3... }
    destruct_hypos.
    apply H1 with (i:=i) (T2:=x)...
    apply H5 with (i:=i)...
Qed.

Lemma dom_add_drop: forall {A:Type} a (t1 t2:A) l1 l2,
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

Lemma equiv_fv_tt: forall E A B,
   WFS E A -> WFS E B ->
    equiv A B ->
    fv_tt A [=] fv_tt B.
Proof with auto.
  intros E A B typA typB.
  intros. revert E typA typB. induction H;intros; try solve [simpl;reflexivity]...
  - simpl. inversion typA; inversion typB;subst.
    rewrite (IHequiv1 E)... rewrite (IHequiv2 E)... fsetdec.
  - simpl. inversion typA.
    inversion typB. subst. pick_fresh X. specialize_x_and_L X L.
    specialize_x_and_L X  L0. specialize_x_and_L X  L1.
    rewrite_alist (nil ++ X ~ bind_sub im0 ++ E) in H6.
    apply WFS_im_inv with (im2:=im) in H6.
    specialize (H0 (X ~ bind_sub im ++ E)).
    apply (fv_tt_open_tt_eq ) in H0...

  - generalize dependent l2.
    induction l1;intros...
    +
      destruct l2...
      { destruct p. simpl in H. specialize (H a). fsetdec. }
    +
      destruct a as [lb1 T1].
      simpl in H.
      assert (lb1 `in` dom l2).
      { rewrite <- H... }
      apply binds_In_inv in H2. destruct H2 as [T2 ?].
      apply binds_split in H2. destruct H2 as [l2a [l2b ?]].
      subst. cbn [fv_tt].
      rewrite !List.map_app.
      rewrite fold_union_app3.
      simpl. rewrite (H1 lb1 T1 T2)...
      2:{ inversion typA;subst. apply H5 with (i:=lb1)... }
      2:{ inversion typB;subst. apply H5 with (i:=lb1)... }
      rewrite (IHl1) with  (l2:= l2b ++ l2a)...
      { simpl. rewrite List.map_app. rewrite fold_right_union_app.
        reflexivity. }
      { inversion typA;subst. apply WFS_rcd...
        { inversion H3... } intros...
        apply H5 with (i:=i)... }
      { rewrite dom_app in H.
        simpl in H. 
        rewrite KeySetProperties.union_sym in H.
        rewrite KeySetProperties.union_add in H.
        rewrite KeySetProperties.union_sym in H.
        rewrite <- dom_app in H. 
        apply dom_add_drop with (t1:=T1) (t2:=T2) in H...
        { inversion typA... }
        { inversion typB;subst. constructor.
          + rewrite cons_app_one in H3. apply uniq_remove_mid in H3...
          + rewrite dom_app. apply notin_union_3.
            { apply fresh_mid_head in H3... }
            { apply fresh_mid_tail in H3... }
        }
      }
      { intros. apply H0 with (i:=i)... }
      { intros. apply H1 with (i:=i) (E:=E0)... }
      { inversion typB;subst. apply WFS_rcd...
        { rewrite cons_app_one in H3. apply uniq_remove_mid in H3... }
        intros.
        apply H5 with (i:=i)... analyze_binds H2. }
Qed.

(* Instance typ_equiv_refl : Equivalence equiv := {
  Equivalence_Reflexive := equiv_refl;
  Equivalence_Symmetric := equiv_symm;
  Equivalence_Transitive := equiv_trans
}. *)

Lemma Msub_refl_inv: forall E im A B evs,
  Sub im Eq evs E A B -> equiv A B.
Proof with auto.
  intros. dependent induction H...
  - destruct cm1, cm2; try solve [ simpl in H1;
    destruct (AtomSetImpl.is_empty evs2);
    destruct (AtomSetImpl.is_empty evs1);inversion H1].
    specialize (IHSub1 eq_refl).
    specialize (IHSub2 eq_refl).
    constructor... apply equiv_symm...
  - apply eqv_mu with (L:=L). intros.
    apply H0 with (X:=X)...
  - 
    apply eqv_mu with (L:=L). intros.
    apply H0 with (X:=X)...
  -
    apply eqv_rcd. reflexivity. intros. inversion H0.
  -
    destruct cm1, cm2; try solve [ simpl in H1;
    destruct (AtomSetImpl.is_empty evs2);
    destruct (AtomSetImpl.is_empty evs1);inversion H1].
    specialize (IHSub1 eq_refl).
    specialize (IHSub2 eq_refl).
    inversion IHSub2;subst.
    apply eqv_rcd.
    +
      rewrite !dom_app. rewrite !dom_app in H4. clear - H4. fsetdec.
    +
      assert (Hu1: uniq (tys1 ++ tys1')).
      { apply sub_regular in H0. destruct_hypos.
        inversion H2;subst... }
      assert (Hu2: uniq (tys2 ++ tys2')).
      { apply sub_regular in H0. destruct_hypos.
        inversion H3;subst... }
      intros. analyze_binds_uniq H2.
      * apply H5 with (i:=i)...
        analyze_binds_uniq H3...
      * analyze_binds_uniq H3...
      * apply H5 with (i:=i)...
        analyze_binds_uniq H3...
Qed.


Lemma rename_env_open: forall A X Y,
    X <> Y ->
    X `notin` fv_tt (open_tt A Y) ->
    X \notin fv_tt A.
Proof with eauto.
  unfold open_tt.
  intros A.
  generalize 0.
  induction A using typ_rec';intros;simpl in *...
Qed. 


Lemma posvar_regular: forall m X A B,
    posvar m X A B ->
    type A /\ type B.
Proof with auto.
  intros.
  induction H...
  -
    destruct IHposvar1.
    destruct IHposvar2...
  -
    split.
    apply type_mu with (L:=L \u {{X}})...
    intros.
    eapply H0...
    apply type_mu with (L:=L \u {{X}})...
    intros.
    eapply H0...
  -
    split.
    apply type_mu with (L:=L \u {{X}})...
    apply type_mu with (L:=L \u {{X}})...
Qed.

Lemma equiv_rename_fix: forall A B Y (Z:atom),
  equiv A B ->
  equiv (subst_tt Y Z A) (subst_tt Y Z B).
Proof with auto.
  intros.
  induction H...
  -
    simpl in *...
    destruct (X==Y)...
  -
    simpl in *...
  -
    simpl in *...
    apply eqv_mu with (L:=L \u  {{ Y }})...
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
  -
    simpl in *...
    apply eqv_rcd...
    { rewrite !dom_map... }
    intros.
    apply binds_map_3 in H3.
    apply binds_map_3 in H2.
    destruct_hypos. subst.
    apply H1 with (i:=i)...
Qed.


Lemma pos_rename_fix : forall X Y Z A B m,
    posvar m X A B ->
    X \notin {{Y}} \u {{Z}} ->
    posvar m X (subst_tt Y Z A) (subst_tt Y Z B).
Proof with auto.
  intros.
  induction H...
  -
    simpl in *...
    destruct (X==Y)...
    constructor...
    apply subst_tt_type...
    constructor...
    apply subst_tt_type...
  -
    simpl in *.
    constructor...
    apply subst_tt_type...
  -
    simpl.
    destruct (X==Y)...
  -
    simpl in *...
    destruct (Y0==Y)...
  -
    simpl in *...
  -
    simpl in *...
    apply pos_rec with (L:=L \u {{Y}} \u {{X}} \u {{Z}}).
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
  -
    simpl in *.
    apply pos_rec_t with (L:=L \u {{X}} \u {{Y}}).
    { apply notin_fv_subst... }
    { apply notin_fv_subst... }
    {
      intros.
      rewrite subst_tt_open_tt_var...
      apply subst_tt_type... }
    {
      intros.
      rewrite subst_tt_open_tt_var...
      apply subst_tt_type... }
    apply equiv_rename_fix with (Y:=Y) (Z:=Z) in H4...
    
  -
    simpl in *.
    apply pos_rcd...
    { apply subst_tt_type with (Z:=Y) (P:=Z) in H... }
    { apply subst_tt_type with (Z:=Y) (P:=Z) in H1... }
    intros.
    apply binds_map_3 in H4.
    apply binds_map_3 in H5.
    destruct_hypos. subst.
    apply H3 with (l:=l)...
Qed.

Lemma fv_tt_rcd_field: forall l lb t,
  binds lb t l ->
  fv_tt t [<=] fv_tt (typ_rcd l).
Proof with auto.
  intros. induction l...
  - inversion H.
  - destruct a. analyze_binds H.
    + simpl. fsetdec.
    + simpl. rewrite IHl... fsetdec...
Qed.


  
Lemma pos_rename_1: forall X m A B Y,
    posvar m X A B ->
    Y \notin {{X}} \u fv_tt A \u fv_tt B ->
    posvar m Y (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  induction H;intros...
  -
    constructor...
    apply subst_tt_type...
  -
    constructor...
    apply subst_tt_type...
  -
    simpl in *...
    destruct (X==X)...
  -
    simpl in *...
    destruct (Y==X)...
  -
    simpl in *...
  -
    simpl in *...
    apply pos_rec with (L:=L \u {{X}} \u {{Y}} \u fv_tt A \u fv_tt B).
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    apply H0...
    apply notin_union...
    split...
    apply notin_union...
    split...
    apply notin_fv_tt_open_aux... 
    apply notin_fv_tt_open_aux...
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    pick fresh Y1.
    assert (Y1 `notin` union L (singleton X) ) by auto.
    assert (Y0 `notin` union (singleton Y1) (union (fv_tt (open_tt A Y1)) (fv_tt (open_tt B Y1)))).
    {
      apply notin_union.
      split...
      apply notin_union.
      split;apply notin_fv_tt_open_aux...
    }    
    specialize (H2 _ H5 _ H6).
    rewrite <- subst_tt_intro in H2...
    rewrite <- subst_tt_intro in H2...
    apply pos_rename_fix...
  -
    simpl in *.
    apply pos_rec_t with (L:=L \u {{X}} \u {{Y}}).
    { rewrite <- subst_tt_fresh... }
    { rewrite <- subst_tt_fresh... }
    { intros.
      rewrite subst_tt_open_tt_var...
      apply subst_tt_type... }
    { intros.
      rewrite subst_tt_open_tt_var...
      apply subst_tt_type... }
    apply equiv_rename_fix with (Y:=X) (Z:=Y) in H3...
  -
    simpl. apply pos_rcd...
    { apply subst_tt_type with (Z:=X) (P:=Y) in H... }
    { apply subst_tt_type with (Z:=X) (P:=Y) in H0... }
    intros.
    apply binds_map_3 in H4.
    apply binds_map_3 in H5.
    destruct_hypos. subst.
    apply H2 with (l:=l)...
    { apply fv_tt_rcd_field in H7.
      apply fv_tt_rcd_field in H6.
      fsetdec. }
Qed.

Lemma pos_rename_2: forall X m A B Y,
    posvar m X A B ->
    Y \notin {{X}} \u fv_tt A \u fv_tt B ->
    posvar m X (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  induction H;intros...
  -
    constructor...
    apply subst_tt_type...
  -
    constructor...
    apply subst_tt_type...
  -
    simpl in *...
    destruct (X==X)...
  -
    simpl in *...
    destruct (Y==X)...
  -
    simpl in *...
  -
    simpl in *...
    apply pos_rec with (L:=L \u {{X}} \u {{Y}} \u fv_tt A \u fv_tt B).
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    apply H0...
    apply notin_union...
    split...
    apply notin_union...
    split...
    apply notin_fv_tt_open_aux... 
    apply notin_fv_tt_open_aux...
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    pick fresh Y1.
    assert (Y1 `notin` union L (singleton X) ) by auto.
    assert (Y0 `notin` union (singleton Y1) (union (fv_tt (open_tt A Y1)) (fv_tt (open_tt B Y1)))).
    {
      apply notin_union.
      split...
      apply notin_union.
      split;apply notin_fv_tt_open_aux...
    }    
    specialize (H2 _ H5 _ H6).
    rewrite <- subst_tt_intro in H2...
    rewrite <- subst_tt_intro in H2...
    apply pos_rename_fix...
  -
    simpl in *.
    apply pos_rec_t with (L:=L \u {{X}} \u {{Y}}).
    { rewrite <- subst_tt_fresh... }
    { rewrite <- subst_tt_fresh... }
    { intros.
      rewrite subst_tt_open_tt_var...
      apply subst_tt_type... }
    { intros.
      rewrite subst_tt_open_tt_var...
      apply subst_tt_type... }
    apply equiv_rename_fix with (Y:=X) (Z:=Y) in H3...
  -
    simpl. apply pos_rcd...
    { apply subst_tt_type with (Z:=X) (P:=Y) in H... }
    { apply subst_tt_type with (Z:=X) (P:=Y) in H0... }
    intros.
    apply binds_map_3 in H4.
    apply binds_map_3 in H5.
    destruct_hypos. subst.
    apply H2 with (l:=l)...
    { apply fv_tt_rcd_field in H7.
      apply fv_tt_rcd_field in H6.
      fsetdec. }
Qed.


(* PosVar related to Linear rules *)



Theorem soundness_posvar: forall E im cm evs A B,
  Sub im cm evs E A B -> forall X, X `notin` evs -> 
    (binds X (bind_sub im) E ->  posvar Pos X A B) /\
    (binds X (bind_sub (flip_im im)) E ->  posvar Neg X A B).
Proof with auto.
  intros. generalize dependent X.
  induction H;intros...
  - split;intros. 
    + constructor. apply WFS_type in H0...
    + constructor. apply WFS_type in H0...
  - split;intros.
    + destruct (X == X0).
      2:{ apply pos_fvar_y... }
      subst. apply pos_fvar_x.
    + destruct (X == X0).
      2:{ apply pos_fvar_y... }
      subst. apply uniq_from_wf_env in H.
      pose proof binds_unique _ _ _ _ _ H0 H2 H.
      inversion H3. destruct im;inversion H5.
  - destruct IHSub1 with (X:=X)... destruct IHSub2 with (X:=X)...
    split;intros.
    + constructor... apply H4. destruct im...
    + constructor...
  - 
    (* rec lt *)
    split;intros.
    + apply pos_rec with (L:=L \u evs)...
      * intros. specialize_x_and_L Y L... destruct H0 with (X:=X)...
      * intros. specialize_x_and_L Y L... destruct H0 with (X:=Y)...
    + apply pos_rec with (L:=L \u evs)...
      * intros. specialize_x_and_L Y L... destruct H0 with (X:=X)...
      * intros. specialize_x_and_L Y L... destruct H0 with (X:=Y)...
  - 
    (* rec eq notin *)
    split;intros.
    + apply pos_rec with (L:=L \u evs)...
      * intros. specialize_x_and_L Y L... destruct H0 with (X:=X)...
      * intros. specialize_x_and_L Y L... destruct H0 with (X:=Y)...
    + apply pos_rec with (L:=L \u evs)...
      * intros. specialize_x_and_L Y L... destruct H0 with (X:=X)...
      * intros. specialize_x_and_L Y L... destruct H0 with (X:=Y)...
  -
    assert (Hsub: Sub im Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_eq_in with (L:=L)... }
    (* rec eq in *)

    assert (equiv (typ_mu A1) (typ_mu A2)).
    { apply Msub_refl_inv in Hsub... }
    split;intros.
    + apply pos_rec_t with (L:=L)...
      { apply equiv_fv_tt with (E:=E) in H2. simpl in H2. rewrite <- H2...
        { get_well_form...  }
        { get_well_form...  } }
      { intros. specialize_x_and_L Y L. apply sub_regular in H. destruct_hypos. apply WFS_type in H5... }
      { intros. specialize_x_and_L Y L. apply sub_regular in H. destruct_hypos. apply WFS_type in H6... }
    + apply pos_rec_t with (L:=L)...
      { apply equiv_fv_tt with (E:=E) in H2. simpl in H2. rewrite <- H2...
        { get_well_form... } { get_well_form... }
      }   
      { intros. specialize_x_and_L Y L. apply sub_regular in H. destruct_hypos. apply WFS_type in H5... }
      { intros. specialize_x_and_L Y L. apply sub_regular in H. destruct_hypos. apply WFS_type in H6... }
  -
    (* rcd nil *)
    split;intros.
    + apply pos_rcd...
      { apply type_rcd. intros. inversion H2. }
      { apply type_rcd. intros. inversion H2. }
      intros. inversion H2.
    + apply pos_rcd...
      { apply type_rcd. intros. inversion H2. }
      { apply type_rcd. intros. inversion H2. }
      intros. inversion H2.
  -
    (* rcd nil + cons *)
    split;intros.
    + apply pos_rcd...
      { apply type_rcd. intros. apply WFS_type with (E:=E). apply H2 with (l:=i)... }
      { apply type_rcd. intros. inversion H5. }
      intros. inversion H6.
    + apply pos_rcd...
      { apply type_rcd. intros. apply WFS_type with (E:=E). apply H2 with (l:=i)... }
      { apply type_rcd. intros. inversion H5. }
      intros. inversion H6.
  -
    (* rcd cons + cons *)
    destruct IHSub1 with (X:=X)... destruct IHSub2 with (X:=X)...
    split;intros.
    + constructor...
      { get_type. inversion H8;subst.
        apply type_rcd. intros...
        analyze_binds H12...
        apply H13 with (i:=i)...
        apply H13 with (i:=i)... }
      { get_type. inversion H9;subst.
        apply type_rcd. intros...
        analyze_binds H12...
        apply H13 with (i:=i)...
        apply H13 with (i:=i)... }
      intros. 
      assert (Hu1: uniq (tys1 ++ tys1')).
      { apply sub_regular in H0. destruct_hypos.
        inversion H10;subst... }
      assert (Hu2: uniq (tys2 ++ tys2')).
      { apply sub_regular in H0. destruct_hypos.
        inversion H11;subst... }
      specialize (H3 H7). specialize (H5 H7).
      inversion H5;subst.
      analyze_binds_uniq H8.
      *
        apply H16 with (l:=l0)...
        analyze_binds_uniq H9.
      *
        analyze_binds_uniq H9.
      *
        apply H16 with (l:=l0)...
        analyze_binds_uniq H9.
    +
      constructor...
      { get_type. inversion H8;subst.
        apply type_rcd. intros...
        analyze_binds H12...
        apply H13 with (i:=i)...
        apply H13 with (i:=i)... }
      { get_type. inversion H9;subst.
        apply type_rcd. intros...
        analyze_binds H12...
        apply H13 with (i:=i)...
        apply H13 with (i:=i)... }
      intros. 
      assert (Hu1: uniq (tys1 ++ tys1')).
      { apply sub_regular in H0. destruct_hypos.
        inversion H10;subst... }
      assert (Hu2: uniq (tys2 ++ tys2')).
      { apply sub_regular in H0. destruct_hypos.
        inversion H11;subst... }
      specialize (H4 H7). specialize (H6 H7).
      inversion H6;subst.
      analyze_binds_uniq H8.
      *
        apply H16 with (l:=l0)...
        analyze_binds_uniq H9.
      *
        analyze_binds_uniq H9.
      *
        apply H16 with (l:=l0)...
        analyze_binds_uniq H9.
  - apply IHSub... rewrite H0...
Qed.



Theorem soundness_posvar_fresh: forall E im im' cm evs A B,
  Sub im cm evs E A B -> forall X, X `notin` evs \u dom E -> 
    posvar im' X A B.
Proof with auto.
  intros. generalize dependent X. generalize dependent im'.
  induction H;intros...
  - constructor. apply WFS_type in H0...
  - constructor. apply binds_In in H0. intros C. subst...
  - 
    (* rec lt *)
    apply pos_rec with (L:=L \u evs)...
    * intros. specialize_x_and_L Y L...
      apply soundness_posvar with (X:=Y) in H...
      destruct H...
  - 
    (* rec eq notin *)
    apply pos_rec with (L:=L \u evs)...
    * intros. specialize_x_and_L Y L...
      apply soundness_posvar with (X:=Y) in H...
      destruct H...
  -
    (* rec eq in *)
    assert (Hsub: Sub im Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_eq_in with (L:=L)... }
    assert (equiv (typ_mu A1) (typ_mu A2)).
    { apply Msub_refl_inv in Hsub... }
    apply pos_rec_t with (L:=L)...
    { apply equiv_fv_tt with (E:=E) in H2. simpl in H2. rewrite <- H2...
      { get_well_form... } { get_well_form... } }
    { intros. specialize_x_and_L Y L. apply sub_regular in H. destruct_hypos. apply WFS_type in H4... }
    { intros. specialize_x_and_L Y L. apply sub_regular in H. destruct_hypos. apply WFS_type in H5... }
  -
    (* rcd nil *)
    apply pos_rcd...
    { apply type_rcd. intros. inversion H1. }
    { apply type_rcd. intros. inversion H1. }
    intros. inversion H1.
  -
    (* rcd nil + cons *)
    apply pos_rcd...
    { apply type_rcd. intros. apply WFS_type with (E:=E). apply H2 with (l:=i)... }
    { apply type_rcd. intros. inversion H4. }
    intros. inversion H5.
  -
    (* rcd cons + cons *)
    apply pos_rcd...
    { get_type. inversion H3;subst.
      apply type_rcd. intros...
      analyze_binds H7...
      apply H8 with (i:=i)...
      apply H8 with (i:=i)... }
    { get_type. inversion H4;subst.
      apply type_rcd. intros...
      analyze_binds H7...
      apply H8 with (i:=i)...
      apply H8 with (i:=i)... }
    intros.
    assert (Hu1: uniq (tys1 ++ tys1')).
    { apply sub_regular in H0. destruct_hypos.
      inversion H5;subst... }
    assert (Hu2: uniq (tys2 ++ tys2')).
    { apply sub_regular in H0. destruct_hypos.
      inversion H6;subst... }
    specialize (IHSub1 im'). specialize (IHSub2 im').
    specialize_x_and_L X (union evs1 (dom E)).
    specialize_x_and_L X (union evs2 (dom E)).
    inversion IHSub2;subst.
    analyze_binds_uniq H3.
    *
      apply H11 with (l:=l0)...
      analyze_binds_uniq H4.
    *
      analyze_binds_uniq H4.
    *
      apply H11 with (l:=l0)...
      analyze_binds_uniq H4.
  -
    apply IHSub... rewrite H0...
Qed.

Lemma add_union_inj: forall l s1 s2,
  add l s1 [=] add l s2 ->
  l `notin` s1 ->
  l `notin` s2 ->
  s1 [=] s2.
Proof with auto.
  intros. fsetdec.
Qed.


Lemma Msub_lt_not_eq: forall im evs E A B,
  Sub im Lt evs E A B -> ~ equiv A B.
Proof with auto.
  intros. dependent induction H...
  - intros C. inversion C...
  - destruct cm1.
    { intros C. inversion C;subst. apply IHSub1... apply equiv_symm... }
    destruct cm2.
    { intros C. inversion C;subst. apply IHSub2... }
    simpl in H1. inversion H1.
  - intros C. inversion C;subst.
    pick_fresh X. specialize_x_and_L X L.
    specialize_x_and_L X L0.
    apply H0... 
  - intros C. inversion C;subst...
    simpl. destruct tys...
    { hnf in H5. destruct p. specialize (H5 a). clear - H5. simpl in H5. destruct H5. fsetdec. }
  - destruct cm1.
    { intros C. inversion C;subst. apply IHSub1...
      apply H5 with (i:=l)... }
    destruct cm2.
    { intros C. inversion C;subst. apply IHSub2...
      apply eqv_rcd... 
      { rewrite !dom_app in H4, Hl1, Hl2. rewrite !dom_app.
        simpl in H4. rewrite dom_app in H4. simpl in H4.
        clear - H4 Hl1 Hl2. rewrite KeySetProperties.union_sym in H4.
        rewrite KeySetProperties.union_add in H4.
        rewrite (KeySetProperties.union_sym (dom tys2)) in H4.
        rewrite KeySetProperties.union_add in H4.
        apply add_union_inj in H4...
        rewrite KeySetProperties.union_sym in H4.
        rewrite (KeySetProperties.union_sym (dom tys2')) in H4...
      }
      intros. apply H5 with (i:=i)...
      { analyze_binds H2... }
      { analyze_binds H3... }
    }
    simpl in H1. inversion H1.
Qed.


Theorem posvar_false: forall E im cm evs A B,
  Sub im cm evs E A B ->  forall X, X `in` evs -> 
    (binds X (bind_sub im) E ->  ~ posvar Pos X A B) /\
    (binds X (bind_sub (flip_im im)) E ->  ~ posvar Neg X A B).
    (* ~ posvar (mode_of im) X A B. *)
Proof with auto.
  intros. generalize dependent X.
  induction H;intros...
  (* if induction on H, then for var case we cannot get IH for evs1 evs2 *)
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - assert (X0 = X) by fsetdec. subst. split;intros.
    + apply uniq_from_wf_env in H.
      pose proof binds_unique _ _ _ _ _ H0 H2 H.
      destruct im; inversion H3.
    + intros C. inversion C;subst...
  - apply union_iff in H2.
    destruct H2.
    + specialize (IHSub1 _ H2).
      destruct IHSub1. split;intros.
      * intros C. inversion C;subst. apply H4... destruct im...
      * intros C. inversion C;subst. apply H3...
    + specialize (IHSub2 _ H2).
      destruct IHSub2. split;intros.
      * intros C. inversion C;subst. apply H3...
      * intros C. inversion C;subst. apply H4...
  -
    (* rec lt *)
    split;intros.
    + intros C. inversion C;subst.
      { (* rec posvar *)
        pick_fresh Y. specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
        specialize (H0 X H1).
        destruct H0... apply H0... }
      { (* rec self *)
        inversion H11;subst.
        pick_fresh Y. specialize_x_and_L Y L1.
        specialize_x_and_L Y L.
        apply Msub_lt_not_eq in H...
      }
    + intros C. inversion C;subst.
      { (* rec posvar *)
        pick_fresh Y. specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
        specialize (H0 X H1).
        destruct H0... apply H3... }
      { (* rec self *)
        inversion H11;subst.
        pick_fresh Y. specialize_x_and_L Y L.
        specialize_x_and_L Y L1.
        apply Msub_lt_not_eq in H...
      }
  -
    (* rec eq notin *)
    split;intros.
    + intros C. inversion C;subst.
      { (* rec posvar *)
        pick_fresh Y. specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
        destruct H0 with (X:=X)... apply H3... }
      { (* rec self *)
        pick_fresh Y. specialize_x_and_L Y L.
        apply sub_evs_fv in H. destruct_hypos.
        apply H in H1. apply in_open1 in H1. simpl in H1. destruct H1... fsetdec. }
    + intros C. inversion C;subst.    
      { (* rec posvar *)
        pick_fresh Y. specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
        destruct H0 with (X:=X)... apply H4... }
      { (* rec self *)
        pick_fresh Y. specialize_x_and_L Y L.
        apply sub_evs_fv in H. destruct_hypos.
        apply H in H1. apply in_open1 in H1. simpl in H1. destruct H1... fsetdec. }
  -
    split;intros.
    + intros C. inversion C;subst.
      { (* rec posvar *)
        pick_fresh Y.
        apply union_iff in H1. destruct H1.
        + specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
          destruct H0 with (X:=X)... apply H3...
        + specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
          destruct H0 with (X:=Y)... (* <--- key of the proof *)
          apply H3... }
      { (* rec self *)
        apply union_iff in H1. destruct H1. 2:{ fsetdec. }
        pick_fresh Y. specialize_x_and_L Y L.
        apply sub_evs_fv in H. destruct_hypos.
        apply (@KeySetProperties.subset_add_2 evs evs Y) in H1;try reflexivity.
        apply H in H1. apply in_open1 in H1. simpl in H1. destruct H1... fsetdec. }
    + intros C. inversion C;subst.    
      { (* rec posvar *)
        pick_fresh Y.
        apply union_iff in H1. destruct H1.
        + specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
          destruct H0 with (X:=X)... apply H4...
        + specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
          destruct H0 with (X:=Y)... (* <--- key of the proof *)
          apply H3... }
      { (* rec self *)
        apply union_iff in H1. destruct H1. 2:{ fsetdec. }
        pick_fresh Y. specialize_x_and_L Y L.
        apply sub_evs_fv in H. destruct_hypos.
        apply (@KeySetProperties.subset_add_2 evs evs Y) in H1;try reflexivity.
        apply H in H1. apply in_open1 in H1. simpl in H1. destruct H1... fsetdec. }
  -
    (* rcd nil *)
    fsetdec.
  -
    (* rcd cons + nil *)
    fsetdec.
  -
    (* rcd cons + cons *)
    apply union_iff in H2.
    destruct H2.
    + specialize (IHSub1 _ H2).
      destruct IHSub1. split;intros.
      * intros C. inversion C;subst. apply H3...
        apply H12 with (l0:=l)...
      * intros C. inversion C;subst. apply H4...
        apply H12 with (l0:=l)...
    + specialize (IHSub2 _ H2).
      destruct IHSub2. split;intros.
      * intros C. inversion C;subst. apply H3...
        apply pos_rcd. 
        { inversion H8;subst.
          apply type_rcd. intros.
          apply H7 with (i:=i)...
          analyze_binds H6... }
        { inversion H11;subst.
          apply type_rcd. intros.
          apply H7 with (i:=i)...
          analyze_binds H6... }
        intros. 
        apply H12 with (l0:=l0)...
        { analyze_binds H6. } { analyze_binds H7. }
      * intros C. inversion C;subst. apply H4...
        apply pos_rcd.
        { inversion H8;subst.
          apply type_rcd. intros.
          apply H7 with (i:=i)...
          analyze_binds H6... }
        { inversion H11;subst.
          apply type_rcd. intros.
          apply H7 with (i:=i)...
          analyze_binds H6... }
        intros. 
        apply H12 with (l0:=l0)...
        { analyze_binds H6. } { analyze_binds H7. }
  -
    rewrite <- H0 in H1...
Qed.

