Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Record.


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


(* prove twice the inclusion? *)
Lemma sub_eq_evs_aux: forall  B1 B2,
    (* typePairR A B -> *)
    equiv B1 B2 ->
    (forall im cm1 cm2 evs1 evs2 E A, 
        Sub im cm1 evs1 E A B1 -> 
        Sub im cm2 evs2 E A B2 ->
        evs1 [<=] evs2 /\ cm1 = cm2) /\
    (forall im cm1 cm2 evs1 evs2 E A, 
        Sub im cm1 evs1 E B1 A -> 
        Sub im cm2 evs2 E B2 A ->
        evs1 [<=] evs2 /\ cm1 = cm2)
        .
Proof with auto.
  intros. induction H;intros...
  +
    split;intros.
    {
      dependent induction H0.
      - dependent induction H...
        + split... reflexivity.
        + rewrite <- H0. apply IHSub...
      - rewrite <- H1. apply IHSub...
    }
    {
      dependent induction H0.
      - dependent induction H...
        + split... reflexivity.
        + rewrite <- H0. apply IHSub...
      - dependent induction H...
        + split... reflexivity.
        + rewrite <- H0. apply IHSub...
      - rewrite <- H1. apply IHSub...
    }
  +
    split;intros.
    {
      dependent induction H0.
      - dependent induction H...
        + split... reflexivity.
        + exfalso...
        + rewrite <- H0. apply IHSub...
      - dependent induction H...
        + exfalso...
        + split... reflexivity.
        + rewrite <- H0. apply IHSub...
      - rewrite <- H1. apply IHSub...
    }
    {
      dependent induction H0.
      - dependent induction H...
        + split... reflexivity.
        + exfalso...
        + rewrite <- H0. apply IHSub...
      - exfalso...
      - rewrite <- H1. apply IHSub...
    }
  +
    split;intros.
    {
      dependent induction H0.
      *
        dependent induction H...
        - split... reflexivity.
        - exfalso...
          apply uniq_from_wf_env in H.
          pose proof binds_unique _ _ _ _ _ H2 H0 H.
          destruct im;inversion H3.
        - rewrite <- H2. apply (IHSub X)...
      *
        dependent induction H...
        - exfalso...
          apply uniq_from_wf_env in H.
          pose proof binds_unique _ _ _ _ _ H2 H0 H.
          destruct im;inversion H3.
        - split... reflexivity.
        - rewrite <- H2. apply (IHSub X)...
      *
        rewrite <- H1. apply (IHSub X)...
    }
    {
      dependent induction H0.
      *
        dependent induction H...
        - split... reflexivity.
        - rewrite <- H3. apply (IHSub H2 X)...
      *
        dependent induction H...
        - split... reflexivity.
        - exfalso...
          apply uniq_from_wf_env in H.
          pose proof binds_unique _ _ _ _ _ H2 H0 H.
          destruct im;inversion H3.
        - rewrite <- H2. apply (IHSub X)...
      *
        dependent induction H...
        - exfalso...
          apply uniq_from_wf_env in H.
          pose proof binds_unique _ _ _ _ _ H2 H0 H.
          destruct im;inversion H3.
        - split... reflexivity.
        - rewrite <- H2. apply (IHSub X)...
      *
        rewrite <- H1. apply (IHSub X)...
    }
  +
    split;intros.
    {
      dependent induction H1...
      - 
        clear IHSub1. clear IHSub2.
        dependent induction H2...
        * 
          clear IHSub1. clear IHSub2.
          destruct IHequiv1 as [IHequiv1a IHequiv1b].
          destruct IHequiv2 as [IHequiv2a IHequiv2b].
          pose proof IHequiv1b _ _ _ _ _ _ _ H1_ H2_.
          pose proof IHequiv2a _ _ _ _ _ _ _ H1_0 H2_0.
          destruct H3. destruct H4. rewrite H3, H4. split. { fsetdec. }
          subst.
          destruct cm2, cm3; simpl in H1, H2.
            { inversion H1. inversion H2... }
            { destruct (AtomSetImpl.is_empty evs3) eqn:Eevs3;inversion H2.
              destruct (AtomSetImpl.is_empty evs0) eqn:Eevs0;inversion H1...
            }
            { destruct (AtomSetImpl.is_empty evs2) eqn:Eevs2;inversion H2.
              destruct (AtomSetImpl.is_empty evs1) eqn:Eevs1;inversion H1...
            }
            { inversion H1. inversion H2... }
        * rewrite <- H3. apply (IHSub B1 B2 A0 A3)...
      - rewrite <- H2. apply (IHSub A1 A2)...
    }
    {
      dependent induction H1...
      -
        dependent induction H4...
        + split... reflexivity.
        + rewrite <- H5.
          apply (IHSub B1 B2)...
      - 
        clear IHSub1. clear IHSub2.
        dependent induction H2...
        * 
          clear IHSub1. clear IHSub2.
          destruct IHequiv1 as [IHequiv1a IHequiv1b].
          destruct IHequiv2 as [IHequiv2a IHequiv2b].
          pose proof IHequiv1a _ _ _ _ _ _ _ H1_ H2_.
          pose proof IHequiv2b _ _ _ _ _ _ _ H1_0 H2_0.
          destruct H3. destruct H4. rewrite H3, H4. split. { fsetdec. }
          subst.
          destruct cm2, cm3; simpl in H1, H2.
            { inversion H1. inversion H2... }
            { destruct (AtomSetImpl.is_empty evs3) eqn:Eevs3;inversion H2.
              destruct (AtomSetImpl.is_empty evs0) eqn:Eevs0;inversion H1...
            }
            { destruct (AtomSetImpl.is_empty evs2) eqn:Eevs2;inversion H2.
              destruct (AtomSetImpl.is_empty evs1) eqn:Eevs1;inversion H1...
            }
            { inversion H1. inversion H2... }
        * rewrite <- H3. apply (IHSub B1 B2 B0 B3)...
      - rewrite <- H2. apply (IHSub A1 A2)...
    }
  + 
    split;intros.
    {
      dependent induction H1...
      -
        dependent induction H3.
        *
          pick_fresh X. specialize_x_and_L X L.
          destruct H0 as [IHa IHb].
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          pose proof IHa _ _ _ _ _ _ _ H1 H3...
        *
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          apply Msub_refl_inv in H3.
          apply Msub_lt_not_eq in H1.
          exfalso. apply H1.
          apply equiv_trans with (B:= open_tt B X)...
          apply equiv_symm...
        * 
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          apply Msub_refl_inv in H3.
          apply Msub_lt_not_eq in H1.
          exfalso. apply H1.
          apply equiv_trans with (B:= open_tt B X)...
          apply equiv_symm...
        *
          rewrite <- H4. apply (IHSub B A1)...
          { intros. rewrite H4. apply (H2 X H5 A0)...
            rewrite <- H4... }
      -
        dependent induction H3.
        *
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          apply Msub_refl_inv in H1.
          apply Msub_lt_not_eq in H3.
          exfalso. apply H3.
          apply equiv_trans with (B:= open_tt A X)...
        *
          pick_fresh X. specialize_x_and_L X L.
          destruct H0 as [IHa IHb].
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          pose proof IHa _ _ _ _ _ _ _ H1 H3...
        * 
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          destruct H0 as [IHa IHb].
          pose proof IHa _ _ _ _ _ _ _ H1 H3... destruct_hypos.
          assert (remove X evs [<=] remove X (add X evs0)). 
          { rewrite H0. reflexivity. }
          rewrite AtomSetProperties.remove_equal in H6 at 1...
          rewrite AtomSetProperties.remove_add in H6...
          split... fsetdec.
        *
          rewrite <- H4. apply (IHSub B A1)...
          { intros. rewrite H4. apply (H2 X H5 A0)...
            rewrite <- H4... }
      -
        dependent induction H3.
        *
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          apply Msub_lt_not_eq in H3.
          apply Msub_refl_inv in H1.
          exfalso. apply H3.
          apply equiv_trans with (B:= open_tt A X)...
        * 
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          destruct H0 as [IHa IHb].
          pose proof IHa _ _ _ _ _ _ _ H1 H3... destruct_hypos.
          exfalso. specialize (H0 X).
          assert (X `in` evs0)... clear - Fr H6. fsetdec.
        *
          pick_fresh X. specialize_x_and_L X L.
          destruct H0 as [IHa IHb].
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          pose proof IHa _ _ _ _ _ _ _ H1 H3. destruct_hypos.
          assert (remove X (add X evs) [<=] remove X (add X evs0))... { rewrite H0. reflexivity. }
          rewrite !AtomSetProperties.remove_add in H6... split... clear - H6. fsetdec.
        *
          rewrite <- H4. apply (IHSub B A1)...
          { intros. rewrite H4. apply (H2 X H5 A0)...
            rewrite <- H4... }
      -
        rewrite <- H2. apply (IHSub A)...
    }
    {
      dependent induction H1...
      -
        dependent induction H4...
        + split... reflexivity.
        + rewrite <- H5.
          apply (IHSub B)...
      -
        dependent induction H3.
        *
          pick_fresh X. specialize_x_and_L X L.
          destruct H0 as [IHa IHb].
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          pose proof IHb _ _ _ _ _ _ _ H1 H3...
        *
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          apply Msub_refl_inv in H3.
          apply Msub_lt_not_eq in H1.
          exfalso. apply H1.
          apply equiv_trans with (B:= open_tt B X)...
        * 
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          apply Msub_refl_inv in H3.
          apply Msub_lt_not_eq in H1.
          exfalso. apply H1.
          apply equiv_trans with (B:= open_tt B X)...
        *
          rewrite <- H4. apply (IHSub B A2)...
          { intros. rewrite H4. apply (H2 X H5 A0)...
            rewrite <- H4... }
      -
        dependent induction H3.
        *
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          apply Msub_refl_inv in H1.
          apply Msub_lt_not_eq in H3.
          exfalso. apply H3.
          apply equiv_trans with (B:= open_tt A X)...
          apply equiv_symm...
        *
          pick_fresh X. specialize_x_and_L X L.
          destruct H0 as [IHa IHb].
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          pose proof IHb _ _ _ _ _ _ _ H1 H3...
        * 
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          destruct H0 as [IHa IHb].
          pose proof IHb _ _ _ _ _ _ _ H1 H3... destruct_hypos.
          assert (remove X evs [<=] remove X (add X evs0)). 
          { rewrite H0. reflexivity. }
          rewrite AtomSetProperties.remove_equal in H6 at 1...
          rewrite AtomSetProperties.remove_add in H6...
          split... fsetdec.
        *
          rewrite <- H4. apply (IHSub B A2)...
          { intros. rewrite H4. apply (H2 X H5 A0)...
            rewrite <- H4... }
      -
        dependent induction H3.
        *
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          apply Msub_lt_not_eq in H3.
          apply Msub_refl_inv in H1.
          exfalso. apply H3.
          apply equiv_trans with (B:= open_tt A X)...
          apply equiv_symm...
        * 
          pick_fresh X. specialize_x_and_L X L.
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          destruct H0 as [IHa IHb].
          pose proof IHb _ _ _ _ _ _ _ H1 H3... destruct_hypos.
          exfalso. specialize (H0 X).
          assert (X `in` evs0)... clear - Fr H6. fsetdec.
        *
          assert (Heqv:equiv (typ_mu A) (typ_mu B))...
          { apply eqv_mu with (L:=L)... }
          assert (Hsub1: Sub im Eq (evs `union` fv_tt A) E (typ_mu A) (typ_mu A2))...
          { apply Sa_rec_eq_in with (L:=L0)... }
          assert (Hsub2: Sub im Eq (evs0 `union` fv_tt B) E (typ_mu B) (typ_mu A2))...
          { apply Sa_rec_eq_in with (L:=L1)... }
          apply equiv_fv_tt with (E:=E) in Heqv.
          2:{ get_well_form... }
          2:{ get_well_form... } simpl in Heqv.
          pick_fresh X. specialize_x_and_L X L.
          destruct H0 as [IHa IHb].
          specialize_x_and_L X L1.
          specialize_x_and_L X L0.
          pose proof IHb _ _ _ _ _ _ _ H1 H3. destruct_hypos.
          assert (remove X (add X evs) [<=] remove X (add X evs0))... { rewrite H0. reflexivity. }
          rewrite !AtomSetProperties.remove_add in H6...
          rewrite Heqv. split...
          clear - H6. fsetdec.
        *
          rewrite <- H4. apply (IHSub B A2)...
          { intros. rewrite H4. apply (H2 X H5 A0)...
            rewrite <- H4... }
      -
        rewrite <- H2. apply (IHSub A)...
    }
  +
  split; intros.
  { revert H3. revert H H0 H1. revert l2 evs2 cm2.
    dependent induction H2;intros...
    + dependent induction H3...
      * split... reflexivity.
      * exfalso...
      * exfalso. apply app_cons_not_nil in x...
      * rewrite <- H4. apply (IHSub l2)...
    + dependent induction H6...
      * exfalso...
      * split... reflexivity.
      * rewrite dom_app in H3. simpl in H3.
        exfalso. clear - H3.
        specialize (H3 l)... fsetdec.
      * rewrite <- H7. apply (IHSub) with (tys0 := tys) (l3:=l2)...
    +
      assert (binds l T2 (tys2 ++ (l, T2) :: tys2'))...
      apply binds_In in H4. rewrite H0 in H4.
      apply binds_In_inv in H4. destruct H4 as [T2' ?].
      apply binds_split in H4. destruct H4 as (tys3' & tys3 & ?). subst.
      assert (Hu: uniq (tys3 ++ l ~ T2' ++ tys3')).
      { get_well_form. inversion H5... }
      apply Sub_rcd_inversion in H3.
      destruct H3 as (cm1' & cm2' & evs1' & evs2' & Hs1 & Hs2 & Hcm' & Hevs').
      destruct (H2 l T2 T2') as [H2a H2b]... 
      destruct H2a with (evs1 := evs1) (cm1 := cm1) (A := T1) (cm2:=cm1') (evs2:=evs1') (im:=im) (E:=E)... subst.

      destruct (IHSub2 (tys2 ++ tys2') eq_refl (tys3 ++ tys3') evs2' cm2')...
      { clear - H0 Hu Hl1 Hl2.
        rewrite !dom_app in *. simpl in H0.
        rewrite !KeySetProperties.union_add in H0.
        rewrite (KeySetProperties.union_sym (dom tys2)) in H0.
        rewrite (KeySetProperties.union_sym (dom tys3)) in H0.
        rewrite !KeySetProperties.union_add in H0.
        assert (
          remove l (add l (union (dom tys2') (dom tys2)))
        [=] remove l (add l (union (union Metatheory.empty (dom tys3')) (dom tys3)))
        ). { rewrite H0. reflexivity. }
        rewrite !AtomSetProperties.remove_add in H...
        { rewrite (KeySetProperties.union_sym (dom tys2')) in H.
          rewrite H. rewrite KeySetProperties.union_assoc.
          rewrite (KeySetProperties.union_sym (dom tys3)).
          intro r. split;intros...
          + apply union_iff in H1. destruct H1...
            apply empty_iff in H1. exfalso...
        }
        { apply notin_union_3;[apply notin_union_3|].
          + intros C. apply empty_iff in C...
          + apply fresh_mid_tail in Hu...
          + apply fresh_mid_head in Hu...
        }
      }
      { intros. apply H1 with (i:=i) (T1:=T0) (T3:=T3)... analyze_binds H4. }
      { intros. destruct (H2 i T0 T3)... analyze_binds H4. }
      { split.
        + rewrite H3, H4...
        + subst. clear IHSub1 IHSub2 H2 H1. destruct cm1', cm2'; simpl in H, Hcm'.
          { inversion H. inversion Hcm'... }
          { destruct (AtomSetImpl.is_empty evs2') eqn:Eevs2';inversion Hcm'.
            destruct (AtomSetImpl.is_empty evs2) eqn:Eevs2;inversion H...
          }
          { destruct (AtomSetImpl.is_empty evs1') eqn:Eevs1';inversion Hcm'.
            destruct (AtomSetImpl.is_empty evs1) eqn:Eevs1;inversion H...
          }
          { inversion H. inversion Hcm'... }
      }
    +
      rewrite <- H. apply (IHSub l1 eq_refl l2 evs2 cm2)...
  }
  { revert H3. revert H H0 H1. revert l2 evs2 cm2.
    dependent induction H2;intros...
    + dependent induction H5...
      * split... reflexivity.
      * rewrite <- H6. apply IHSub with (l3:=l2)...
    + dependent induction H3...
      * split... reflexivity.
      * exfalso. destruct l2...
        destruct p. simpl in H0. specialize (H0 a).
        fsetdec.
      * exfalso. apply app_cons_not_nil in x...
      * rewrite <- H4. apply (IHSub l2)...
    + dependent induction H6...
      * exfalso... destruct l1...
        destruct p. simpl in H3. specialize (H3 a).
        fsetdec.
      * split... reflexivity.
      * apply app_cons_not_nil in x. exfalso...
      * rewrite <- H7. apply (IHSub) with  (l3:=l2)...
    +
      assert (binds l T2 (tys2 ++ (l, T2) :: tys2'))...
      pose proof sub_typ_label_incl H3 as Hincl.
      apply binds_In in H4. rewrite Hincl in H4.
      apply binds_In_inv in H4. destruct H4 as [T2' ?].
      apply binds_split in H4. destruct H4 as (tys3' & tys3 & ?). subst.
      assert (Hu: uniq (tys3 ++ l ~ T2' ++ tys3')).
      { get_well_form. inversion H4... }
      apply Sub_rcd_inversion in H3.
      destruct H3 as (cm1' & cm2' & evs1' & evs2' & Hs1 & Hs2 & Hcm' & Hevs').
      destruct (H2 l T1 T2') as [H2a H2b]... 
      destruct H2b with (evs1 := evs1) (cm1 := cm1) (A := T2) (cm2:=cm1') (evs2:=evs1') (im:=im) (E:=E)... subst.

      destruct (IHSub2 (tys1 ++ tys1') eq_refl (tys3 ++ tys3') evs2' cm2')...
      { clear - H0 Hu Hl1 Hl2.
        rewrite !dom_app in *. simpl in H0.
        rewrite !KeySetProperties.union_add in H0.
        rewrite (KeySetProperties.union_sym (dom tys1)) in H0.
        rewrite (KeySetProperties.union_sym (dom tys3)) in H0.
        rewrite !KeySetProperties.union_add in H0.
        assert (
          remove l (add l (union (dom tys1') (dom tys1)))
        [=] remove l (add l (union (union Metatheory.empty (dom tys3')) (dom tys3)))
        ). { rewrite H0. reflexivity. }
        rewrite !AtomSetProperties.remove_add in H...
        { rewrite (KeySetProperties.union_sym (dom tys1')) in H.
          rewrite H. rewrite KeySetProperties.union_assoc.
          rewrite (KeySetProperties.union_sym (dom tys3)).
          intro r. split;intros...
          + apply union_iff in H1. destruct H1...
            apply empty_iff in H1. exfalso...
        }
        { apply notin_union_3;[apply notin_union_3|].
          + intros C. apply empty_iff in C...
          + apply fresh_mid_tail in Hu...
          + apply fresh_mid_head in Hu...
        }
      }
      { intros. apply H1 with (i:=i) (T2:=T0) (T3:=T3)... analyze_binds H4. }
      { intros. destruct (H2 i T0 T3)... analyze_binds H4. }
      { split.
        + rewrite H3, H4...
        + subst. clear IHSub1 IHSub2 H2 H1. destruct cm1', cm2'; simpl in H, Hcm'.
          { inversion H. inversion Hcm'... }
          { destruct (AtomSetImpl.is_empty evs2') eqn:Eevs2';inversion Hcm'.
            destruct (AtomSetImpl.is_empty evs2) eqn:Eevs2;inversion H...
          }
          { destruct (AtomSetImpl.is_empty evs1') eqn:Eevs1';inversion Hcm'.
            destruct (AtomSetImpl.is_empty evs1) eqn:Eevs1;inversion H...
          }
          { inversion H. inversion Hcm'... }
      }
    +
      rewrite <- H. apply (IHSub l1 eq_refl l2 evs2 cm2)...
  }
Qed.


Lemma sub_eq_evs: forall im cm1 cm2 evs1 evs2 E A B1 B2,
    equiv B1 B2 ->
    Sub im cm1 evs1 E A B1 -> 
    Sub im cm2 evs2 E A B2 ->
    evs1 [=] evs2 /\ cm1 = cm2.
Proof with auto.
  intros.
  pose proof (equiv_symm _ _ H) as H'.
  pose proof sub_eq_evs_aux B1 B2 H.
  pose proof sub_eq_evs_aux B2 B1 H'.
  destruct H2 as [H2a H2b], H3 as [ H3a H3b].
  pose proof H2a _ _ _ _ _ _ _ H0 H1.
  pose proof H3a _ _ _ _ _ _ _ H1 H0.
  destruct_hypos... split... fsetdec.
Qed.


(* prove twice the inclusion? *)
Lemma sub_eq_evs': forall im cm1 cm2 evs1 evs2 E A B1 B2,
    equiv B1 B2 ->
    Sub im cm1 evs1 E B1 A -> 
    Sub im cm2 evs2 E B2 A ->
    evs1 [=] evs2 /\ cm1 = cm2.
Proof with auto.
    intros.
    pose proof (equiv_symm _ _ H) as H'.
    pose proof sub_eq_evs_aux B1 B2 H.
    pose proof sub_eq_evs_aux B2 B1 H'.
    destruct H2 as [H2a H2b], H3 as [ H3a H3b].
    pose proof H2b _ _ _ _ _ _ _ H0 H1.
    pose proof H3b _ _ _ _ _ _ _ H1 H0.
    destruct_hypos... split... fsetdec.
Qed.

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


Theorem Sub_rcd_inversion_complete: 
  forall E im cm evs ls1a ls1b ls2a ls2b l T1 T2,
  Sub im cm evs E 
    (typ_rcd (ls1a ++ l ~ T1 ++ ls1b))
    (typ_rcd (ls2a ++ l ~ T2 ++ ls2b)) ->
  exists cm1 cm2 evs1 evs2,
    Sub im cm1 evs1 E T1 T2 /\
    Sub im cm2 evs2 E (typ_rcd (ls1a ++ ls1b)) (typ_rcd (ls2a ++ ls2b)) /\
    compose_cm cm1 cm2 evs1 evs2 = Some cm /\ evs1 `union` evs2 [=] evs.
Proof with auto.
  intros.
  assert (Hu1: uniq ((ls1a ++ l ~ T1 ++ ls1b))).
  { get_well_form. inversion H0... }
  assert (Hu2: uniq ((ls2a ++ l ~ T2 ++ ls2b))).
  { get_well_form. inversion H1... }
  pose proof sub_rcd_remove _ _ l _ _ _ _ H.
  destruct H0 as (cm' & (evs' & (Hevs' & H0)) & Hc1 & Hc2).
  cbv [dropLabel_typ] in H0.
  rewrite !dropLabel_app4 in H0...
  pose proof sub_rcd_get _ _ _ _ _ _ H l T1 T2.
  destruct H1 as (cm'' & (evs'' & (Hevs'' & H1)) & Hc3 & Hc4).
  { cbv [getLabel_typ]. rewrite getLabel_get... }
  { cbv [getLabel_typ]. rewrite getLabel_get... }
  exists cm'', cm', evs'', evs'.
  split... split...
  destruct (compose_cm cm'' cm' evs'' evs') eqn:Ecomp.
  {
    assert (Sub im c (evs'' `union` evs') E
      (typ_rcd (ls1a ++ l ~ T1 ++ ls1b))
      (typ_rcd (ls2a ++ l ~ T2 ++ ls2b))
    ).
    { apply Sa_rcd_cons with (cm1:=cm'') (cm2:=cm')...
      { rewrite dom_app. apply notin_union_3.
        + apply fresh_mid_head in Hu1...
        + apply fresh_mid_tail in Hu1...
      }
      { rewrite dom_app. apply notin_union_3.
        + apply fresh_mid_head in Hu2...
        + apply fresh_mid_tail in Hu2...
      }
    }
    (* assert (wf_env E). { get_well_form... }  *)
    assert (WFS E ((typ_rcd (ls2a ++ l ~ T2 ++ ls2b)))).
    { get_well_form... }
    pose proof equiv_refl _ _ H3.
    pose proof sub_eq_evs _ _ _ _ _ _ _ _ _ H4 H2 H.
    destruct_hypos;subst. split...
  }
  exfalso.
  destruct cm', cm''...
  * inversion Ecomp...
  * inversion Ecomp...
    apply sub_lt_then_emp in H...
    destruct (AtomSetImpl.is_empty evs'') eqn:Eempty;
      try solve [inversion H3]...
    apply is_not_empty_iff in Eempty. exfalso.
    apply Eempty. rewrite H in Hevs''. fsetdec.
  * simpl in Ecomp. apply sub_lt_then_emp in H...
    destruct (AtomSetImpl.is_empty evs') eqn:Eempty;
      try solve [inversion Ecomp]...
    apply is_not_empty_iff in Eempty. exfalso.
    apply Eempty. rewrite H in Hevs'. fsetdec.
  * 
    inversion Ecomp...
Qed.


Ltac destruct_evs :=
  match goal with
  | [ H: (if AtomSetImpl.is_empty ?evs then _ else _) = _ |- _ ] =>
      let Hl := fresh evs in
      destruct (AtomSetImpl.is_empty evs) eqn: Hl; try solve [inversion H]
  end.


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
      pose proof H4 as H4'.
      apply Msub_refl_inv in H4.
      apply equiv_fv_tt with (E:=E) in H4...
      { rewrite H4 in H5. fsetdec. }
      { get_well_form... }
      { get_well_form... }
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
      pose proof H4 as H4'.
      apply Msub_refl_inv in H4.
      apply equiv_fv_tt with (E:=E) in H4.
      { rewrite H4 in H5.
        fsetdec. }
      { get_well_form... }
      { get_well_form... }


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
      pose proof Esub as Esub'.
      apply sub_evs_fv in H4. destruct_hypos.
      apply Msub_refl_inv in Esub.
      apply equiv_fv_tt with (E:=E) in Esub.
      { rewrite Esub in H4. fsetdec. }
      { get_well_form... }
      { get_well_form... }

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
    assert (l0 `in` dom tys').
    { apply sub_typ_label_incl in H2.
      rewrite <- H2. rewrite dom_app. simpl... }
    apply binds_In_inv in H3.
    destruct H3 as [T1' ?].
    apply binds_split in H3.
    destruct H3 as (tys0 & tys0' & ?). subst.
    pose proof Sub_rcd_inversion_complete _ _ _ _ _ _ _ _ _ _ _ H2.
    destruct H3 as (cm1' & cm2' & evs1' & evs2' & Hsub1 & Hsub2 & Hcomp & Hevs').
    destruct IHSub2 with (l:=tys1 ++ tys1') (evs1 := evs2') (cm1 := cm2')
      (A:= typ_rcd (tys0' ++ tys0)) as ( evsg1 & G1a & G1b) ...
    { intros. apply H with (i:=i) (T:=T)... analyze_binds H3.  }
    { intros. apply H0 with (i:=i) (T:=T)... analyze_binds H3.  }
    { get_well_form... }
    destruct H0 with (i:=l0) (T:=T1) (E:=E) (im:=im)
      (cm1:=cm1') (cm2:=cm1) (A:=T1') (C:=T2)
      (evs1:=evs1') (evs2:=evs1) as (evsg2 & G2a & G2b )...
    exists (evsg2 `union` evsg1).
    split... { fsetdec. }

    assert (
      compose_cm (seq_cm cm1' cm1) (seq_cm cm2' cm2)
        evsg2 evsg1 = Some (seq_cm cm0 cm)).
    { 

    clear IHSub1 IHSub2 H H0.

    destruct cm1', cm1, cm2', cm2, cm0, cm; simpl in *;auto;
    try solve 
    [ destruct (AtomSetImpl.is_empty evs2');inversion Hcomp|
      destruct (AtomSetImpl.is_empty evs1');inversion Hcomp|
      destruct (AtomSetImpl.is_empty evs2);inversion H1|
      destruct (AtomSetImpl.is_empty evs1);inversion H1
      ]...
    + 
      repeat destruct_evs.
      assert (AtomSetImpl.is_empty evsg1 = true). 
      { apply is_empty_iff. apply is_empty_iff in evs2'0.
        apply is_empty_iff in evs3. fsetdec. }
      rewrite H...
    +
      repeat destruct_evs.
      apply is_empty_iff in evs2'0.
      destruct (AtomSetImpl.is_empty evsg1) eqn:Eevsg1...
      apply Msub_refl_inv in H2_0.
      pose proof sub_eq_evs _ _ _ _ _ _ _ _ _ H2_0 Hsub2 G1b.
      destruct_hypos.
      apply is_not_empty_iff in Eevsg1. exfalso.
      rewrite H in *. congruence.


    +
      repeat destruct_evs.
      apply is_empty_iff in evs3. 
      destruct (AtomSetImpl.is_empty evsg1) eqn:Eevsg1...
      apply Msub_refl_inv in Hsub2.
      pose proof sub_eq_evs' _ _ _ _ _ _ _ _ _ Hsub2 G1b H2_0.
      destruct_hypos.
      apply is_not_empty_iff in Eevsg1. exfalso.
      rewrite H in *. congruence.

    +
      repeat destruct_evs.
      apply is_empty_iff in evs1'0. 
      destruct (AtomSetImpl.is_empty evsg2) eqn:Eevsg2...
      apply Msub_refl_inv in H2_.
      pose proof sub_eq_evs _ _ _ _ _ _ _ _ _ H2_ Hsub1 G2b.
      destruct_hypos.  
      apply is_not_empty_iff in Eevsg2. exfalso.
      rewrite H in *. congruence.
    + 
      repeat destruct_evs.
      apply is_empty_iff in evs1'0. 
      destruct (AtomSetImpl.is_empty evsg2) eqn:Eevs2'...
      apply Msub_refl_inv in H2_.
      pose proof sub_eq_evs _ _ _ _ _ _ _ _ _ H2_ Hsub1 G2b.
      destruct_hypos.  
      apply is_not_empty_iff in Eevs2'. exfalso.
      rewrite H in *. congruence.
    +
      destruct_evs.
      apply is_empty_iff in evs3.
      destruct (AtomSetImpl.is_empty evsg2) eqn:Eevs1'...
      apply Msub_refl_inv in Hsub1.
      (* apply Msub_eq_sem in H2_. rewrite H2_ in *.  require syntactic equal *)
      pose proof sub_eq_evs' _ _ _ _ _ _ _ _ _  Hsub1 G2b H2_.
      destruct_hypos.  
      apply is_not_empty_iff in Eevs1'. exfalso.
      rewrite H in *. congruence.

    }
    apply Sa_rcd_cons with (cm1:= seq_cm cm1' cm1)
      (cm2:= seq_cm cm2' cm2)...
    { inversion Hwf;subst.
      rewrite dom_app. apply notin_union_3.
      + apply fresh_mid_head in H5...
      + apply fresh_mid_tail in H5...
    }

  *
    destruct IHSub with (l0:=l) (evs1:=evs1) (cm1:=cm1) (A:=A) as [evs1' [? ?]]...
    { exists evs1';split... fsetdec. }
Qed.