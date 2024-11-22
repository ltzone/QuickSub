Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import PositiveBase.


Module M.

Inductive IsoMode := Neg | Pos.

Inductive CmpMode := Lt | Eq.

Locate typ.

Inductive binding : Set :=
  | bind_sub : IsoMode -> binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).
Definition emp := Metatheory.empty.
Notation empty := (@nil (atom * binding)).


Inductive WFS : env -> typ -> Prop :=
| WFS_top : forall E, WFS E typ_top
| WFS_nat : forall E, WFS E typ_nat
| WFS_fvar : forall X E im,
    binds X (bind_sub im) E ->
    WFS E (typ_fvar X)
| WFS_arrow : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_arrow A B)
| WFS_rec : forall L E A im,
    (* (forall X , X \notin L -> forall im, 
        WFS (X ~ bind_sub im ++ E) (open_tt A (typ_rcd X (open_tt A X)))) -> *)
      (forall  X , X \notin L -> 
        WFS (X ~ bind_sub im ++ E) (open_tt A X)) ->
      WFS E (typ_mu A).


Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) im,
      wf_env E ->
      X \notin dom E ->
      wf_env (X ~ bind_sub im ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      WFS E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).

Definition flip_im (im : IsoMode) : IsoMode :=
  match im with
    | Neg => Pos
    | Pos => Neg
  end.

Definition compose_cm (cm1 cm2 : CmpMode) (evs1 evs2 : atoms ) : option (CmpMode) :=
  match cm1, cm2 with
    | Lt, Lt => Some Lt
    | Eq, Lt => if AtomSetImpl.is_empty evs1 then Some Lt else None
    | Lt, Eq => if AtomSetImpl.is_empty evs2 then Some Lt else None
    | Eq, Eq => Some Eq
  end.


(*
IsoMode := + | -
E [IsoMode] |- T1 [CmpMode] T2
*)
Inductive Sub : IsoMode -> CmpMode -> atoms -> env -> typ -> typ -> Prop :=
(* 
|- E
----------------
E [_]|- nat <:= nat 
*)
| Sa_nat: forall E im,
    wf_env E ->
    Sub im Eq emp E typ_nat typ_nat
(*
|- E
----------------
E [=] |- top <:= top
*)
| Sa_top_eq: forall E im,
    wf_env E ->
    Sub im Eq emp E typ_top typ_top  
(*
TODO: is != top necessary?, if we are going to interpret <: as no greater than
|- E, A != top
----------------
E [<] |- A <:= top
*)
| Sa_top_lt: forall E im A,
    wf_env E -> WFS E A -> A <> typ_top ->
    Sub im Lt emp E A typ_top
| Sa_fvar_pos: forall E X im,
    wf_env E -> binds X (bind_sub im) E ->
    Sub im Eq emp E (typ_fvar X) (typ_fvar X)
| Sa_fvar_neg: forall E X im,
    wf_env E -> binds X (bind_sub (flip_im im)) E ->
    Sub im Eq (singleton X) E (typ_fvar X) (typ_fvar X)
| Sa_arrow: forall E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm im,
    Sub (flip_im im) cm1 evs1 E B1 A1 ->
    Sub im cm2 evs2 E A2 B2 ->
    compose_cm cm1 cm2 evs1 evs2 = Some cm ->
    Sub im cm (evs1 `union` evs2) E (typ_arrow A1 A2) (typ_arrow B1 B2)
| Sa_rec_lt: forall L A1 A2 evs E im,
    (forall X,  X \notin L -> 
        Sub im Lt evs (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
        (* implicitly indicates that X cannot be in the weak-positive set of  E,x |-  A1 <: A2 *)
    Sub im Lt evs E (typ_mu A1) (typ_mu A2)
| Sa_rec_eq_notin: forall L A1 A2 evs E im,
    (forall X,  X \notin L -> 
        Sub im Eq evs (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
    Sub im Eq evs E (typ_mu A1) (typ_mu A2)
(* | Sa_rec_eq_in: forall L A1 A2 evs E im,
    (forall X,  X \notin L -> 
      exists evs', (evs `union` {{X}}) [=] evs' /\
        Sub im Eq evs' (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
    Sub im Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2) *)
| Sa_rec_eq_in: forall L A1 A2 evs E im,
    (forall X,  X \notin L -> 
        Sub im Eq (add X evs) (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
    Sub im Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2)
| Sa_evs_proper: forall im cm evs evs' E A1 A2,
    Sub im cm evs E A1 A2 ->
    evs [=] evs' ->
    Sub im cm evs' E A1 A2
.

#[global] Hint Constructors Sub wf_env WFS : core.


(* 

mu a. Top -> (mu b. b -> a) is not subtype of mu a. a -> (mu b. b -> a)

*)
#[global]
Instance sub_m : Proper (eq ==> eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> eq ==> iff) Sub.
Proof with auto.
  intros.
  repeat (hnf; intros). split.
  + intros. subst. apply Sa_evs_proper with (evs:=x1)...
  + intros. subst. apply Sa_evs_proper with (evs:=y1)... symmetry...
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


Lemma open_tt_fresh_eq_inv: forall A B X,
  X `notin` fv_tt A ->
  X `notin` fv_tt B ->
  open_tt A X = open_tt B X ->
  A = B.
Proof with auto.
  unfold open_tt. generalize 0.
  intros. unfold open_tt in H1. generalize dependent B.
  generalize dependent n.
  induction A;intros...
  - induction B;inversion H1...
    destruct (n == n0);inversion H3.
  - induction B;inversion H1...
    destruct (n == n0);inversion H3.
  - simpl in H1.
    destruct (n0 == n).
    + induction B;inversion H1...
      { destruct (n0 == n1);inversion H1;subst...
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
Qed.


Lemma compose_cm_eq_inv: forall cm1 cm2 evs1 evs2,
  compose_cm cm1 cm2 evs1 evs2 = Some Eq ->
    cm1 = Eq /\ cm2 = Eq.
Proof with auto.
  intros.
  destruct cm1, cm2;inversion H...
  - destruct (AtomSetImpl.is_empty evs2);inversion H1...
  - destruct (AtomSetImpl.is_empty evs1);inversion H1...
Qed.


Theorem Msub_eq_sem: forall E im evs A B,
    Sub im Eq evs E A B -> A = B.
Proof with auto.
  intros.
  dependent induction H...
  - apply compose_cm_eq_inv in H1. destruct_hypos.
    rewrite IHSub1... rewrite IHSub2...
  - pick_fresh X. specialize_x_and_L X L.
    apply open_tt_fresh_eq_inv with (X:=X) in H0...
    subst...
  - pick_fresh X. specialize_x_and_L X L.
    apply open_tt_fresh_eq_inv with (X:=X) in H0...
    subst...
Qed.

Theorem sub_regular: forall E im evs A B,
  Sub im Eq evs E A B -> wf_env E /\ WFS E A /\ WFS E B.
Proof with auto.
  intros. induction H...
  - split... split... 
    apply WFS_fvar with (im:=im)...
    apply WFS_fvar with (im:=im)...
  - split... split...
    apply WFS_fvar with (im:=flip_im im)...
    apply WFS_fvar with (im:=flip_im im)...
  - destruct_hypos. split...
  - split;[|split].
    + pick_fresh X. specialize_x_and_L X L. destruct_hypos...
      inversion H0...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
  - split;[|split].
    + pick_fresh X. specialize_x_and_L X L. destruct_hypos...
      inversion H0...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
  -  split;[|split].
    + pick_fresh X. specialize_x_and_L X L. destruct_hypos...
      inversion H0...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
    + apply WFS_rec with (L:=L) (im:=im)... intros.
      specialize_x_and_L X L0. destruct_hypos...
Qed.

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

Lemma uniq_from_wf_env : forall E,
  wf_env E -> uniq E.
Proof with auto.
  intros. induction H...
Qed.

#[global]
Hint Resolve uniq_from_wf_env : core.

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

Lemma WFS_im_inv: forall E1 E2 X im1 im2 A,
    WFS (E1 ++ X ~ bind_sub im1 ++ E2) A ->
    WFS (E1 ++ X ~ bind_sub im2 ++ E2) A.
Proof with auto.
  intros. generalize dependent im2. dependent induction H;intros...
  - analyze_binds H.
    + apply WFS_fvar with (im:=im)...
    + apply WFS_fvar with (im:=im2)...
    + apply WFS_fvar with (im:=im)...
  - apply WFS_arrow. apply IHWFS1 with (im2:=im1)... apply IHWFS2 with (im2:=im1)...
  - apply WFS_rec with (L:=L) (im:=im)... intros.
    specialize_x_and_L X0 L. rewrite <- app_assoc. apply H0 with (im2:=im1)...
Qed.

Lemma WFS_type: forall E A,
    WFS E A -> type A.
Proof with auto.
  intros.
  induction H...
  - apply type_mu with (L:=L)...
Qed.

End M.


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : M.env => dom x) in
  constr:(A `union` B `union`  E \u C \u D \u F \u G).



Theorem Msub_refl: forall E im A,
    M.wf_env E -> type A -> M.WFS E A -> exists evs, M.Sub im M.Eq evs E A A.
Proof with auto.
  intros. generalize dependent im. generalize dependent E. induction H0;intros...
  - exists M.emp...
  - exists M.emp...
  - inversion H1;subst. destruct im, im0.
    + exists M.emp...
    + exists (singleton X)...
    + exists (singleton X)...
    + exists M.emp...
  - inversion H1;subst. destruct IHtype1 with (im:=M.flip_im im) (E:=E) as [evs1 ?], IHtype2 with (im:=im) (E:=E) as [evs2 ?]...
    exists (union evs1 evs2)...
    apply M.Sa_arrow with (cm1:=M.Eq) (cm2:=M.Eq)...
  - 
    inversion H2;subst.
    pick_fresh X. specialize_x_and_L X L. specialize_x_and_L X L0.
    (* need to decide whether X is in evs of (open_tt T X), so we need replacing_var lemma *)
    destruct H0 with (im:=im) (E:=X ~ M.bind_sub im ++ E) as [evs1 ?]...
    { rewrite_alist (nil ++ X ~ M.bind_sub im ++ E). apply M.WFS_im_inv with (im1:=im0)... }
    exists (if AtomSetImpl.mem X evs1 then (remove X evs1) \u fv_tt T else evs1)...
    destruct (AtomSetImpl.mem X evs1) eqn:Evs1.
    + apply mem_iff in Evs1.
      apply M.Sa_rec_eq_in with (L:=L \u {{X}} \u evs1 \u dom E).
      intros.
      rewrite_alist (nil ++ (X0 ~ M.bind_sub im) ++ E).
      replace (add X0 (remove X evs1)) with 
      (if AtomSetImpl.mem X evs1 then add X0 (remove X evs1) else evs1)...
      2:{ destruct (AtomSetImpl.mem X evs1) eqn:Evs2;
          repeat match goal with 
          | [ H: AtomSetImpl.mem _ _ = true |- _ ] => apply mem_iff in H 
          | [ H: AtomSetImpl.mem _ _ = false |- _ ] => apply not_mem_iff in H end;
          try solve [exfalso;auto];
          try fsetdec. }
      rewrite_alist (nil ++ (X0 ~ M.bind_sub im) ++ E).
      apply M.sub_replacing_var... constructor...
    + apply not_mem_iff in Evs1.
      apply M.Sa_rec_eq_notin with (L:=L \u {{X}} \u evs1 \u dom E).
      intros.
      rewrite_alist (nil ++ (X0 ~ M.bind_sub im) ++ E).
      replace (evs1) with 
      (if AtomSetImpl.mem X evs1 then add X0 (remove X evs1) else evs1)...
      2:{ destruct (AtomSetImpl.mem X evs1) eqn:Evs2;
          repeat match goal with 
          | [ H: AtomSetImpl.mem _ _ = true |- _ ] => apply mem_iff in H 
          | [ H: AtomSetImpl.mem _ _ = false |- _ ] => apply not_mem_iff in H end;
          try solve [exfalso;auto];
          try fsetdec. }
      apply M.sub_replacing_var... constructor...
Qed.

Definition drop_mode (b: M.binding) : binding := match b with
| M.bind_sub _ => bind_sub
| M.bind_typ t => bind_typ t
end.

Definition env_of (E: M.env) := map drop_mode E.

Lemma binds_M_to_binds: forall im X E,
  binds X (M.bind_sub im) E ->
  binds X (bind_sub) (env_of E).
Proof with auto.
  intros.
  induction E...
  { destruct a. inversion H;subst;simpl in *...
      inversion H0;subst... }
Qed.

Theorem WFS_M_WFA: forall E A, M.WFS E A -> WFA (env_of E) A.
Proof with auto.
  intros. induction H;simpl in *...
  - apply WFA_fvar. apply binds_M_to_binds in H...
  - apply WFA_rec with (L:=L)...
Qed.

Lemma env_of_wf_env: forall E, M.wf_env E -> wf_env (env_of E).
Proof with auto.
  intros. induction H;simpl in *...
  - constructor... unfold env_of. rewrite dom_map...
  - constructor... { apply WFS_M_WFA in H0. apply soundness_wfa in H0... }
    unfold env_of. rewrite dom_map...
Qed.

#[global]
Hint Resolve env_of_wf_env WFS_M_WFA soundness_wfa M.WFS_type : core.


Lemma open_tt_fresh_eq_inv: forall A B X,
  X `notin` fv_tt A ->
  X `notin` fv_tt B ->
  open_tt A X = open_tt B X ->
  A = B.
Proof with auto.
  unfold open_tt. generalize 0.
  intros. unfold open_tt in H1. generalize dependent B.
  generalize dependent n.
  induction A;intros...
  - induction B;inversion H1...
    destruct (n == n0);inversion H3.
  - induction B;inversion H1...
    destruct (n == n0);inversion H3.
  - simpl in H1.
    destruct (n0 == n).
    + induction B;inversion H1...
      { destruct (n0 == n1);inversion H1;subst...
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
Qed.


Theorem Msub_refl_inv: forall E im A B evs,
    M.Sub im M.Eq evs E A B -> A = B.
Proof with auto.
  intros. dependent induction H...
  - destruct cm1, cm2; try solve [ simpl in H1;
      destruct (AtomSetImpl.is_empty evs2);
      destruct (AtomSetImpl.is_empty evs1);inversion H1].
    specialize (IHSub1 eq_refl).
    specialize (IHSub2 eq_refl). subst...
  - pick_fresh X. specialize_x_and_L X L.
    specialize (H0 eq_refl). apply open_tt_fresh_eq_inv in H0... subst...
  - pick_fresh X. specialize_x_and_L X L.
    specialize (H0 eq_refl). apply open_tt_fresh_eq_inv in H0... subst...
Qed.


Definition mode_of (im: M.IsoMode) : Mode := match im with
| M.Pos => Pos | M.Neg => Neg end.

Lemma mode_of_flip: forall im, mode_of (M.flip_im im) = flip (mode_of im).
Proof. destruct im;auto. Qed.


Theorem soundness_posvar: forall E im cm evs A B,
  M.Sub im cm evs E A B -> forall X, X `notin` evs -> 
    (binds X (M.bind_sub im) E ->  posvar Pos X A B) /\
    (binds X (M.bind_sub (M.flip_im im)) E ->  posvar Neg X A B).
Proof with auto.
  intros. generalize dependent X.
  induction H;intros...
  - split;intros. 
    + constructor. apply M.WFS_type in H0...
    + constructor. apply M.WFS_type in H0...
  - split;intros.
    + destruct (X == X0).
      2:{ apply pos_fvar_y... }
      subst. apply pos_fvar_x.
    + destruct (X == X0).
      2:{ apply pos_fvar_y... }
      subst. apply M.uniq_from_wf_env in H.
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
    (* rec eq in *)
    assert (typ_mu A1 = typ_mu A2).
    { assert (M.Sub im M.Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2))...
      { apply M.Sa_rec_eq_in with (L:=L)... }
      apply Msub_refl_inv in H2... }
    rewrite <- H2. split;intros.
    + apply pos_rec_t with (L:=L)...
      { intros. specialize_x_and_L Y L. apply M.sub_regular in H. destruct_hypos. apply M.WFS_type in H5... }
    + apply pos_rec_t with (L:=L)...
      { intros. specialize_x_and_L Y L. apply M.sub_regular in H. destruct_hypos. apply M.WFS_type in H5... }
  -
    rewrite <- H0 in H1...
Qed.


Theorem soundness_posvar_fresh: forall E im im' cm evs A B,
  M.Sub im cm evs E A B -> forall X, X `notin` evs \u dom E -> 
    posvar im' X A B.
Proof with auto.
  intros. generalize dependent X. generalize dependent im'.
  induction H;intros...
  - constructor. apply M.WFS_type in H0...
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
    assert (typ_mu A1 = typ_mu A2).
    { assert (M.Sub im M.Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2))...
      { apply M.Sa_rec_eq_in with (L:=L)... }
      apply Msub_refl_inv in H2... }
    rewrite <- H2. apply pos_rec_t with (L:=L)...
    { intros. specialize_x_and_L Y L. apply M.sub_regular in H. destruct_hypos. apply M.WFS_type in H4... }
  -
    rewrite <- H0 in H1...
Qed.



Theorem soundness: forall E im cm evs A B,
  M.Sub im cm evs E A B -> sub_amber2 (env_of E) A B.
Proof with auto.
  intros. induction H;intros...
  - apply binds_M_to_binds in H0...
  - apply binds_M_to_binds in H0...
  - 
    (* rec lt *)
    apply sam2_rec with (L:=L \u evs \u dom E)...
    + intros. specialize_x_and_L X L...
    + intros.
      apply pos_rec with (L:=L \u dom E \u evs)...
      * intros. specialize_x_and_L Y L...
        apply soundness_posvar_fresh with (X:=X) (im':=Pos) in H...
      * intros. specialize_x_and_L Y L...
        apply soundness_posvar with (X:=Y) in H...
        destruct H...
  -
    (* rec eq notin *)
    apply sam2_rec with (L:=L \u evs \u dom E)...
    + intros. specialize_x_and_L X L...
    + intros.
      apply pos_rec with (L:=L \u dom E \u evs)...
      * intros. specialize_x_and_L Y L...
        apply soundness_posvar_fresh with (X:=X) (im':=Pos) in H...
      * intros. specialize_x_and_L Y L...
        apply soundness_posvar with (X:=Y) in H...
        destruct H...
  -
    (* rec eq in *)
    apply sam2_rec with (L:=L \u evs \u dom E \u fv_tt A1)...
    + intros. specialize_x_and_L X L...
    + intros.
      assert (typ_mu A1 = typ_mu A2).
      { assert (M.Sub im M.Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2))...
        { apply M.Sa_rec_eq_in with (L:=L)... }
        apply Msub_refl_inv in H2... } rewrite <- H2.
      apply pos_rec_t with (L:=L \u dom E \u evs \u fv_tt A1)...
      { intros. specialize_x_and_L Y L. apply M.sub_regular in H. destruct_hypos. apply M.WFS_type in H4... }
Qed.

Lemma Msub_lt_not_eq: forall im evs E A B,
  M.Sub im M.Lt evs E A B -> A <> B.
Proof with auto.
  intros. dependent induction H...
  - destruct cm1.
    { intros C. inversion C;subst. apply IHSub1... }
    destruct cm2.
    { intros C. inversion C;subst. apply IHSub2... }
    simpl in H1. inversion H1.
  - pick_fresh X. specialize_x_and_L X L.
    intros C. inversion C;subst.
    apply H0...
Qed.


Theorem posvar_false: forall E im cm evs A B,
  M.Sub im cm evs E A B ->  forall X, X `in` evs -> 
    (binds X (M.bind_sub im) E ->  ~ posvar Pos X A B) /\
    (binds X (M.bind_sub (M.flip_im im)) E ->  ~ posvar Neg X A B).
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
    + apply M.uniq_from_wf_env in H.
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
        pick_fresh Y. specialize_x_and_L Y L.
        apply Msub_lt_not_eq in H...
      }
    + intros C. inversion C;subst.
      { (* rec posvar *)
        pick_fresh Y. specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
        specialize (H0 X H1).
        destruct H0... apply H3... }
      { (* rec self *)
        pick_fresh Y. specialize_x_and_L Y L.
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
        apply M.sub_evs_fv in H. destruct_hypos.
        apply H in H1. apply in_open1 in H1. simpl in H1. destruct H1... fsetdec. }
    + intros C. inversion C;subst.    
      { (* rec posvar *)
        pick_fresh Y. specialize_x_and_L Y L. specialize_x_and_L Y (union L0 (singleton X)).
        destruct H0 with (X:=X)... apply H4... }
      { (* rec self *)
        pick_fresh Y. specialize_x_and_L Y L.
        apply M.sub_evs_fv in H. destruct_hypos.
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
        apply M.sub_evs_fv in H. destruct_hypos.
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
        apply M.sub_evs_fv in H. destruct_hypos.
        apply (@KeySetProperties.subset_add_2 evs evs Y) in H1;try reflexivity.
        apply H in H1. apply in_open1 in H1. simpl in H1. destruct H1... fsetdec. }
  -
    rewrite <- H0 in H1...
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


Inductive is_Menv : M.env -> env -> Prop :=
  | is_Menv_nil: is_Menv nil nil
  | is_Menv_sub_pos: forall E' E X,
      is_Menv E' E ->
      is_Menv ((X, M.bind_sub M.Pos) :: E') ((X, bind_sub) :: E)
  | is_Menv_sub_neg: forall E' E X,
      is_Menv E' E ->
      is_Menv ((X, M.bind_sub M.Neg) :: E') ((X, bind_sub) :: E)
  | is_Menv_typ: forall E' E X T,
      is_Menv E' E ->
      is_Menv ((X, M.bind_typ T) :: E') ((X, bind_typ T) :: E).

(* 

cannot make useof posvar_false if expressed as exists



Theorem completeness: forall E A B,
  (* is_Menv E E' -> *)
  sub_amber2 (env_of E) A B -> forall im,
  (exists evs cm, M.Sub im cm evs E A B /\ 
  (forall X, X \in evs ->
     (binds X (M.bind_sub ( im)) E -> ~ posvar Pos  X A B) /\
     (binds X (M.bind_sub ( (M.flip_im im))) E -> ~ posvar Neg X A B))).
Proof with auto.
  intros. dependent induction H...
  - exists M.emp, M.Eq. split... apply M.Sa_nat... admit. intros. fsetdec.
  - admit.
  - assert (binds X (M.bind_sub im) E \/ binds X (M.bind_sub (M.flip_im im)) E).
    { admit. }
    destruct H1.
    + exists M.emp, M.Eq. split... apply M.Sa_fvar_pos... admit. intros. fsetdec.
    + exists {{ X }}, M.Eq. split... apply M.Sa_fvar_neg... admit. intros. assert (X0 = X) by fsetdec. subst...
      split.
      * intros. admit.
      * intros. intros C. inversion C...
      (* * intros. assert (im = M.Pos) by admit. subst. intros C. inversion C... *)
  -
    destruct IHsub_amber2_1 with (im:=M.flip_im im) (E0:=E) as [evs1 [cm1 [IH1 IH1']]]...
    destruct cm1.
    + destruct IHsub_amber2_2 with (im:=im) (E0:=E) as [evs2 [cm2 [IH2 IH2']]]...
      destruct cm2.
      * (* lt + lt *)
        exists (union evs1 evs2), M.Lt. split.
        { apply M.Sa_arrow with (cm1:=M.Lt) (cm2:=M.Lt)... }
        { intros. apply union_iff in H1. destruct H1.
          - apply IH1' in H1... destruct H1... split;intros;intros C;inversion C;subst...
            { apply H2... destruct im... }
            { apply H1... }
          - apply IH2' in H1... destruct H1... split;intros;intros C;inversion C;subst...
            { apply H1... }
            { apply H2... }
        }
      * (* lt + eq *)
        destruct (AtomSetImpl.is_empty evs2) eqn:Eempty.
        2:{ (* evs2 cannot be empty *)
            apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
            destruct Eempty as [X Eempty].
            pose proof posvar_false _ _ _ _ _ _ IH2 X Eempty.
            destruct H1.
            apply IH2' in Eempty. destruct Eempty as [IH2'1 IH2'2].

    + 
    destruct IHsub_amber2_2 with (im:=im) (E0:=E) as [evs2 [cm2 [IH2 IH2']]]...
    exists (union evs1 evs2), (M.compose_cm cm1 cm2). split.
    + apply M.Sa_and... admit. admit.
    + intros. apply union_iff in H1. destruct H1.
      * apply IH1' in H1... destruct H1...
      * apply IH2' in H1... destruct H1...
  
 *)

Lemma is_Menv_case: forall E0 E X im,
is_Menv E0 E -> 
binds X bind_sub E ->
(binds X (M.bind_sub im) E0 \/ binds X (M.bind_sub (M.flip_im im)) E0).
Proof with auto.
  intros.
  induction H...
  - analyze_binds H0.
    + destruct im...
    + destruct IHis_Menv...
  - analyze_binds H0.
    + destruct im...
    + destruct IHis_Menv...
  - analyze_binds H0.
    destruct IHis_Menv...
Qed.


Lemma is_Menv_dom: forall E E',
    is_Menv E E' -> dom E [=] dom E'.
Proof with auto.
  intros. induction H...
  - simpl. reflexivity.
  - simpl. rewrite IHis_Menv... reflexivity.
  - simpl. rewrite IHis_Menv... reflexivity.
  - simpl. rewrite IHis_Menv... reflexivity.
Qed.

Lemma is_Menv_binds: forall E E' X im,
    is_Menv E E' -> binds X (M.bind_sub im) E -> binds X bind_sub E'.
Proof with auto.
  intros. induction H...
  - inversion H0;subst... inversion H1;subst...
  - inversion H0;subst... inversion H1;subst...
  - inversion H0;subst... inversion H1;subst...
Qed.

Lemma MWFS_WF: forall E E' A,
  is_Menv E E' ->
  M.WFS E A -> WF E' A.
Proof with auto.
  intros. generalize dependent E'. induction H0;intros...
  - apply is_Menv_binds with (E':=E') in H...
  - apply WF_rec with (L:=L \u fv_tt A)...
    + intros. specialize_x_and_L X L.
      apply H0... destruct im; constructor...
    + intros. specialize_x_and_L X L.
      rewrite subst_tt_intro with (X:=X)...
      apply subst_tt_wf;apply H0;destruct im;constructor...
Qed.


Lemma is_Menv_binds2: forall E E' X,
    is_Menv E E' -> binds X bind_sub E' -> 
    exists im, binds X (M.bind_sub im) E.
Proof with auto.
  intros. induction H...
  - inversion H0...
  - analyze_binds H0.
    { exists M.Pos... }
    { destruct IHis_Menv... exists x... }
  - analyze_binds H0.
    { exists M.Neg... }
    { destruct IHis_Menv... exists x... }
  - analyze_binds H0.
    { destruct IHis_Menv... exists x... }
Qed.

Lemma MWF_WFS: forall E E' A,
  is_Menv E E' ->
  WF E' A -> M.WFS E A.
Proof with auto.
  intros. generalize dependent E. induction H0;intros...
  - destruct (is_Menv_binds2 _ _ _ H0 H)...
    apply M.WFS_fvar with (im:=x)...
  - apply M.WFS_rec with (L:=L \u fv_tt A) (im:=M.Pos) ...
    + intros. apply H0... constructor...
Qed.



Lemma Menv_wf_env: forall E E',
    is_Menv E E' ->
    M.wf_env E -> wf_env E'.
Proof with auto.
  intros.
  induction H;intros...
  - inversion H0;subst. constructor...
    rewrite <- is_Menv_dom with (E:=E')...
  - inversion H0;subst. constructor...
    rewrite <- is_Menv_dom with (E:=E')...
  - inversion H0;subst. constructor...
    { apply soundness_wf. apply MWFS_WF with (E:=E')... }
    { rewrite <- is_Menv_dom with (E:=E')... }
Qed.



Lemma is_Menv_wf_env: forall E0 E,
is_Menv E0 E -> wf_env E -> M.wf_env E0.
Proof with auto.
  intros.
  induction H...
  - inversion H0;subst. constructor...
    rewrite is_Menv_dom with (E:=E')...
  - inversion H0;subst. constructor...
    rewrite is_Menv_dom with (E:=E')...
  - inversion H0;subst. constructor...
    { apply completeness_wf in H5. apply MWF_WFS with (E':=E)... }
    { rewrite is_Menv_dom with (E:=E')... }
Qed.

#[global] Hint Resolve is_Menv_wf_env : core.

Lemma WFA_binds: forall E A X,
  X `in` fv_tt A -> WF E A -> binds X bind_sub E.
Proof with auto.
  intros. induction H0;simpl in *;try solve [fsetdec]...
  - assert (X = X0) by fsetdec. subst...
  - apply union_iff in H. destruct H...
  - pick_fresh Y. specialize_x_and_L Y L.
    destruct H1...
    { apply in_open... }
    inversion H1;subst... exfalso...
Qed.

Lemma uniq_from_wf_env: forall E,
    wf_env E -> uniq E.
Proof with auto.
  intros. induction H...
Qed.

Lemma is_Menv_uniq:
  forall E E', is_Menv E E' -> uniq E' -> uniq E.
Proof with auto.
  intros.
  induction H...
  - inversion H0;subst. constructor...
    rewrite is_Menv_dom with (E:=E')...
  - inversion H0;subst. constructor...
    rewrite is_Menv_dom with (E:=E')...
  - inversion H0;subst. constructor...
    rewrite is_Menv_dom with (E:=E')...
Qed.

Theorem completeness: forall E' E A B,
  is_Menv E E' ->
  wk_sub E' A B -> forall im,
  (forall X, 
     (binds X (M.bind_sub ( im)) E -> posvar Pos  X A B) /\
     (binds X (M.bind_sub ( (M.flip_im im))) E -> posvar Neg X A B)) ->
  (exists evs, M.Sub im M.Lt evs E A B) \/ (exists evs, M.Sub im M.Eq evs E A B).
Proof with auto.
  intros. generalize dependent E.
  dependent induction H0;intros...
  - right. exists M.emp... apply M.Sa_nat...
    apply is_Menv_wf_env with (E:=E)...
  - destruct (decide_typ A typ_top).
    + subst. right. exists M.emp... apply M.Sa_top_eq...
      apply is_Menv_wf_env with (E:=E)...
    + left. exists M.emp... apply M.Sa_top_lt...
      apply is_Menv_wf_env with (E:=E)...
      apply MWF_WFS with (E':=E)...
  - right.
    assert (binds X (M.bind_sub im) E0 \/ binds X (M.bind_sub (M.flip_im im)) E0).
    { apply is_Menv_case with (E:=E)... }
    destruct H3.
    + exists M.emp. apply M.Sa_fvar_pos...
      eapply is_Menv_wf_env;eassumption.
    + exists {{ X }}. apply M.Sa_fvar_neg...
      eapply is_Menv_wf_env;eassumption.
  
  - destruct (IHwk_sub1) with (im:=M.flip_im im) (E0:=E0) as [[evs1 IH1]|[evs1 IH1]]...
    { intros. specialize (H1 X). destruct H1. split;intros.
      + apply H1 in H2. inversion H2;subst...
      + destruct im; apply H0 in H2;inversion H2;subst... }
    + destruct (IHwk_sub2) with (im:=im) (E0:=E0) as [[evs2 IH2]|[evs2 IH2]]...
      { intros. specialize (H1 X). destruct H1. split;intros.
        + apply H0 in H2. inversion H2;subst...
        + destruct im; apply H1 in H2;inversion H2;subst... }
      * left. exists (evs1 `union` evs2). apply M.Sa_arrow with (cm1:=M.Lt) (cm2:=M.Lt)...
      * destruct (AtomSetImpl.is_empty evs2) eqn:Eempty.
        2:{ apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
            destruct Eempty as [X Eempty].
            pose proof posvar_false _ _ _ _ _ _ IH2 X Eempty.
            destruct H0.
            assert (binds X (M.bind_sub im) E0 \/ binds X (M.bind_sub (M.flip_im im)) E0).
            { apply is_Menv_case with (E:=E)...
              destruct (M.sub_evs_fv _ _ _ _ _ IH2).
              rewrite H3 in Eempty.
              apply wk_sub_to_sam2 in H0_0.
              apply suba2_regular in H0_0.
              destruct_hypos. apply WFA_binds with (A:=A2)...
            }
            destruct H3.
            { destruct H1 with (X:=X)... specialize (H4 H3). inversion H4;subst. exfalso. apply H0... }
            { destruct H1 with (X:=X)... specialize (H5 H3). inversion H5;subst. exfalso. apply H2... }
        }
        left. exists (evs1 `union` evs2).
        apply M.Sa_arrow with (cm1:=M.Lt) (cm2:=M.Eq)... simpl. rewrite Eempty...
    + destruct (AtomSetImpl.is_empty evs1) eqn:Eempty.
      2:{ apply is_not_empty_iff in Eempty. apply not_empty_has in Eempty.
          destruct Eempty as [X Eempty].
          pose proof posvar_false _ _ _ _ _ _ IH1 X Eempty.
          destruct H0.
          assert (binds X (M.bind_sub im) E0 \/ binds X (M.bind_sub (M.flip_im im)) E0).
          { apply is_Menv_case with (E:=E)...
            destruct (M.sub_evs_fv _ _ _ _ _ IH1).
            rewrite H3 in Eempty.
            apply wk_sub_to_sam2 in H0_.
            apply suba2_regular in H0_.
            destruct_hypos. apply WFA_binds with (A:=B1)... }
          destruct H3.
          { destruct H1 with (X:=X)... specialize (H4 H3). inversion H4;subst. exfalso. apply H2... destruct im... }
          { destruct H1 with (X:=X)... specialize (H5 H3). inversion H5;subst. exfalso. apply H0... }
      }
      destruct (IHwk_sub2) with (im:=im) (E0:=E0) as [[evs2 IH2]|[evs2 IH2]]...
      { intros. specialize (H1 X). destruct H1. split;intros.
        + apply H0 in H2. inversion H2;subst...
        + destruct im; apply H1 in H2;inversion H2;subst... }
      * 
        left. exists (evs1 `union` evs2).
        apply M.Sa_arrow with (cm1:=M.Eq) (cm2:=M.Lt)... simpl. rewrite Eempty...
      *
        (* destruct (AtomSetImpl.is_empty evs2) eqn:Eempty2.
        2:{ apply is_not_empty_iff in Eempty2. apply not_empty_has in Eempty2.
            destruct Eempty2 as [X Eempty2].
            pose proof posvar_false _ _ _ _ _ _ IH2 X Eempty2.
            destruct H0.
            assert (binds X (M.bind_sub im) E0 \/ binds X (M.bind_sub (M.flip_im im)) E0).
            { admit. }
            destruct H3.
            { destruct H1 with (X:=X)... specialize (H4 H3). inversion H4;subst. exfalso. apply H0... }
            { destruct H1 with (X:=X)... specialize (H5 H3). inversion H5;subst. exfalso. apply H2... }
        } *)
        right. exists (evs1 `union` evs2).
        apply M.Sa_arrow with (cm1:=M.Eq) (cm2:=M.Eq)...

(* another discovery:
  it should also be safe to postpone the equality variable check?
*)


  -
    pick_fresh X.
    specialize_x_and_L X L.
    assert (Hwfe: M.wf_env (X ~ M.bind_sub im ++ E0)).
    { apply wk_sub_to_sam2 in H.
      apply suba2_regular in H. destruct_hypos.
      inversion H;subst... constructor...
      apply is_Menv_wf_env with (E0:=E0) in H8...
    }
    
    destruct H0 with (im:=im) (E0:= X ~ M.bind_sub im ++ E0) as [[evs1 IH1]|[evs1 IH1]]...
    { destruct im; constructor... }
    { intros. split;intros.
      + analyze_binds_uniq H4.
        apply H3 in BindsTac.
        inversion BindsTac;subst...
        { destruct H3 with (X:=X0)...
          pick_fresh Y. specialize_x_and_L Y (union L0 (singleton X0)).
          rewrite subst_tt_intro with (X:=Y) (T2:=A)...
          rewrite subst_tt_intro with (X:=Y) (T2:=B)...
          apply pos_rename_fix... }
        { apply posvar_self_notin...
          { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
            rewrite subst_tt_intro with (X:=Z)...
            apply subst_tt_type... }
          { apply notin_fv_tt_open_aux... }
        }
      + analyze_binds_uniq H4.
        { destruct im; inversion BindsTacVal. }
        apply H3 in BindsTac.
        inversion BindsTac;subst...
        { destruct H3 with (X:=X0)...
          pick_fresh Y. specialize_x_and_L Y (union L0 (singleton X0)).
          rewrite subst_tt_intro with (X:=Y) (T2:=A)...
          rewrite subst_tt_intro with (X:=Y) (T2:=B)...
          apply pos_rename_fix... }
        { apply posvar_self_notin...
          { pick_fresh Z. specialize_x_and_L Z (union L0 {{X0}})...
            rewrite subst_tt_intro with (X:=Z)...
            apply subst_tt_type... }
          { apply notin_fv_tt_open_aux... }
        }
    }
    + (* Lt *)
      left. exists evs1.
      apply M.Sa_rec_lt with (L:=L \u {{ X }} \u dom E0)...
      intros.
      replace evs1 with (if AtomSetImpl.mem X evs1 then AtomSetImpl.add X0 (remove X evs1) else evs1)...
      2:{ destruct (AtomSetImpl.mem X evs1) eqn:Eevs...
          apply mem_iff in Eevs.
          pose proof posvar_false _ _ _ _ _ _ IH1 X Eevs.
          destruct H5.
          exfalso. apply H5... }
      rewrite_alist (nil ++ X0 ~ M.bind_sub im ++ E0).
      apply M.sub_replacing_var...
      { inversion Hwfe;subst... constructor... }

    + (* Eq *)
      right.
      destruct (AtomSetImpl.mem X evs1) eqn:Eevs1.
      * exists ((remove X evs1) `union` fv_tt A)...
        apply M.Sa_rec_eq_in with (L:=L \u {{ X }} \u dom E0)...
        intros.
        replace (add X0 (remove X evs1)) with (if AtomSetImpl.mem X evs1 then AtomSetImpl.add X0 (remove X evs1) else evs1)...
        2:{ rewrite Eevs1... }
        rewrite_alist (nil ++ X0 ~ M.bind_sub im ++ E0).
        apply M.sub_replacing_var...
        { inversion Hwfe;subst... constructor... }
      * exists evs1.
        apply M.Sa_rec_eq_notin with (L:=L \u {{ X }} \u dom E0)...
        intros.
        replace evs1 with (if AtomSetImpl.mem X evs1 then AtomSetImpl.add X0 (remove X evs1) else evs1)... 2:{ rewrite Eevs1... }
        rewrite_alist (nil ++ X0 ~ M.bind_sub im ++ E0).
        apply M.sub_replacing_var...
        { inversion Hwfe;subst... constructor... }
  - right. apply Msub_refl...
    + apply is_Menv_wf_env with (E:=E)...
    + apply wf_type in H0...
    + apply MWF_WFS with (E':=E)...
Qed.

Theorem completeness_final: forall A B,
  wk_sub nil A B -> forall im,
  (exists evs, M.Sub im M.Lt evs nil A B) \/ 
  (exists evs, M.Sub im M.Eq evs nil A B).
Proof with auto.
  intros.
  apply completeness with (E:=nil) (im:=im) in H...
  { constructor. }
  { intros. split;intros;inversion H0. }
Qed.
