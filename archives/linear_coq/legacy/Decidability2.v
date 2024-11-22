Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import NominalUnfolding.
Require Export Coq.micromega.Lia.
Import Nominal.
Import String.


Definition menv := list (nat * nat).
Notation empty_menv := (@nil (nat * nat)).

Fixpoint find {A:Type} (n:nat) (E: list (nat * A)) :=
  match E with
  | (k, v) :: E' =>
        if (Nat.eqb n k) then Some v else find n E'
  | nil => None
  end.

Definition fresh_from_env {A : Type} (E: list (atom * A)) := (List.map fst E).


(* 
### The depth of fully expanded tree, but keeping binders during unfolding ###
*)
Fixpoint bindings_rec (E: menv) (n: nat) (T:typ) : nat :=
  match T with
  (* Normally, the leaf nodes are counted with depth 1 *)
  | typ_nat => 1
  | typ_top => 1
  | typ_fvar _ => 1
  (* 
     For bounded variable, the environment keeps the 
     **difference** of depth
     if we replace x (depth(x) = 1)
     by its expanded form (depth({x:A}) = 1 + depth(A)
     i.e. depth(x->1, A) in mu x. A
  *)
  | typ_bvar m => 
      match find (n - m) E with
      | Some k => k
      | None => 1
      (* For well formed types, we can always look up the
        depth of the bound variable.

        But for ill-formed types, we have to mark the
        depth of the bound variable as 1 to enable 
        generalization *)
      end 
  (* The depths for arrow/rcd structures are standard *)
  | typ_arrow A B => 1 + max (bindings_rec E n A) (bindings_rec E n B)
  | typ_rcd _ A => 1 + (bindings_rec E n A)
  | typ_mu A => 
      (* .
      since the binder x will become a free variable after unfolding,
      we keep x ~> 1 in the environment to
      first compute the depth when the recursive body is fully unfolded.
      *)
       let i := bindings_rec ((S n , 1) :: E) (S n) A in
       (* In the unfolded form for the whole type term,
          every x will be eventually unfolded to the depth of
          [i+1] ({x:A}).
       *)
      1 + bindings_rec ((S n, i + 1) :: E) (S n) A
  end.

Definition bindings T := bindings_rec nil 0 T.



Inductive WFMenv : menv -> nat -> Prop :=
| WFMenv_nil:
    WFMenv nil 0
| WFMenv_cons: forall E n m,
    WFMenv E n -> WFMenv ((S n,m)::E) (S n).


(* An inductive formulation of the measure algorithm,
   adapted to well formed types (without tricks in 
   implementing bound variables)
*)

Inductive WFC : list (atom * nat) -> typ -> nat -> Prop :=
| WFC_nat: forall E,
    uniq E ->
    WFC E typ_nat 1
| WFC_top: forall E, 
    uniq E ->
    WFC E typ_top 1
| WFC_fvar: forall E n X,
    uniq E ->
    binds X n E ->
    WFC E (typ_fvar X) n
| WFC_fvar2: forall E X,
    uniq E ->
    X \notin dom E ->
    WFC E (typ_fvar X) 1
| WFC_arrow: forall E n1 n2 T1 T2,
    WFC E T1 n1 ->
    WFC E T2 n2 ->
    WFC E (typ_arrow T1 T2) (1 + max n1 n2)
| WFC_rcd: forall E n T X,
    WFC E T n -> 
    WFC E (typ_rcd X T) (1 + n)
| WFC_mu: forall E m n T L,
    (forall X, X \notin L ->
        WFC (X ~ 1 ++ E) (open_tt T X) m) ->
    (forall X, X \notin L ->
        WFC (X ~ (m + 1) ++ E) (open_tt T X) n) ->
    WFC E (typ_mu T) (1 + n).

Hint Constructors WFC : core.

Definition env_of_cenv (E: list (atom * nat)) := 
  map (fun _ => bind_sub) E.

(* Lemma WFC_WF: forall E T m, WFC E T m -> WF (env_of_cenv E) T.
Proof with auto.
  intros. induction H...
  - (* WFC_bvar *)
    constructor.
    induction E. { inversion H0. } destruct a.
    apply binds_cons_uniq_iff in H0...
    destruct H0.
    { destruct_hypos. subst. simpl. left... }
    { destruct_hypos. inversion H. subst.
      right. apply IHE... }
  - (* WFC_mu *)
    apply WF_rec with (L:= dom E).
    intros. destruct (H X0 H0).

Qed. *)



Inductive WFMenv' : list (atom * nat) -> menv -> nat -> Prop :=
| WFMenv'_nil:
    WFMenv' nil nil 0
| WFMenv'_cons: forall F E n m X,
    X \notin dom F ->
    WFMenv' F E n -> WFMenv' ((X, m)::F) ((S n,m)::E) (S n).

Lemma WFMenv'_uniq : forall { E F n },
  WFMenv' E F n ->
  uniq E.
Proof with auto.
  intros. induction H...
Qed.

Lemma WFC_uniq: forall {E B n}, 
  WFC E B n -> uniq E.
Proof with auto.
  intros. induction H...
  pick_fresh W.
  assert (W `notin` L)...
  pose proof (H0 W H3).
  inversion H4...
Qed.


Inductive WFME: list (atom * nat) -> typ -> menv -> nat -> typ -> Prop :=
| WFME_nat: forall E F n,
    WFMenv' E F n ->
    WFME E typ_nat F n typ_nat
| WFME_top: forall E F n, 
    WFMenv' E F n ->
    WFME E typ_top F n typ_top
| WFME_fvar: forall E F n X m w,
    WFMenv' E F n ->
    binds X w E ->
    In (n - m, w) F ->
    WFME E (typ_fvar X) F n (typ_bvar m)
| WFME_fvar2: forall E F n X,
    WFMenv' E F n ->
    X `notin` dom E ->
    WFME E (typ_fvar X) F n (typ_fvar X)
| WFME_arrow: forall E F n T1 T2 T1' T2',
    WFME E T1 F n T1' ->
    WFME E T2 F n T2' ->
    WFME E (typ_arrow T1 T2) F n (typ_arrow T1' T2')
| WFME_rcd: forall E F n T X T',
    WFME E T F n T' -> 
    WFME E (typ_rcd X T) F n (typ_rcd X T')
| WFME_mu: forall E F n T T' L,
    (forall X m, X \notin L -> WFME ((X, m)::E) (open_tt T X) ((S n, m)::F) (S n) T') ->
    WFME E (typ_mu T) F n (typ_mu T').

Lemma WFME_WFMenv': forall { E F n T T' },
  WFME E T F n T' ->
  WFMenv' E F n.
Proof with auto.
  intros. induction H...
  pick_fresh W.
  assert (W `notin` L). { solve_notin. }
  specialize (H0 W 1 H1).
  dependent destruction H0...
Qed.

Lemma WFMenv'_WFMenv: forall { E F n  },
  WFMenv' E F n ->
  WFMenv F n.
Proof with auto.
  intros. induction H...
  - constructor.
  - econstructor...
Qed.

Lemma WFMenv_prop: forall {F m n v},
  WFMenv F n -> m > n -> ~ In (m, v) F.
Proof with auto.
  intros. induction H...
  intros F.
  destruct F.
  { inversion H1. subst. lia. }
  { apply IHWFMenv... lia.  }
Qed.

Lemma WFMenv_prop2: forall {F n v},
  WFMenv F n -> ~ In (S n, v) F.
Proof with auto.
  intros.
  eapply WFMenv_prop.
  apply H. lia.
Qed.

Lemma find_sem: forall k v F n, 
  WFMenv F n ->
  In (k, v) F -> find k F = Some v.
Proof with auto.
  induction F;intros...
  - inversion H0.
  - destruct H0. subst.
    + simpl. rewrite Nat.eqb_refl...
    + dependent destruction H.
      pose proof IHF _ H H0.
      simpl. destruct (k =? S n)%nat eqn:Eb...
      apply Nat.eqb_eq in Eb. subst.
      exfalso. eapply WFMenv_prop2. { apply H. }
      apply H0.
Qed.

(* the algorithm declaration and implementation are related *)
Lemma WFC_bindings_ind: forall E T F n T',
  WFME E T F n T' ->
  WFC E T (bindings_rec F n T').
Proof with auto.
  intros.
  pose proof WFME_WFMenv' H as Et1.
  pose proof WFMenv'_uniq Et1 as Et2.
  dependent induction H...
  - simpl. rewrite find_sem with (v:=w) (n:=n)...
    apply WFMenv'_WFMenv in H...
  - constructor...
  - constructor...
  - apply WFC_mu with (m:= bindings_rec ((S n , 1) :: F) (S n) T') 
      (L:=L `union` dom E);
    intros; fold bindings_rec.
    + apply H0... constructor...
    + apply H0... constructor...
Qed.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : typ => fv_tt x) in
  let D := gather_atoms_with (fun x : typ => fl_tt x) in
  let E := gather_atoms_with (fun x : env => dom x) in
  let F := gather_atoms_with (fun x : list (atom * nat) => dom x) in
  constr:(A `union` B `union` C \u D \u E \u F).

Lemma WFC_det: forall B E n1 n2,
  type B ->
  WFC E B n1 ->
  WFC E B n2 ->
  n1 = n2.
Proof with auto.
  intros. revert n1 n2 H0 H1. revert E.
  dependent induction H;intros;try solve
  [dependent destruction H1;
    dependent destruction H0;auto].
  - dependent destruction H0;
    dependent destruction H1...
    + eapply binds_unique;eassumption.
    + apply binds_In in H0. exfalso...
    + apply binds_In in H2. exfalso...
  - inversion H1;subst.
    inversion H2;subst.
    pose proof IHtype1 _ _ _ H6 H7.
    pose proof IHtype2 _ _ _ H8 H10...
    (* pose proof IHWF1 _ JMeq_refl _ _ H6 H7.
    pose proof IHWF2 _ JMeq_refl _ _ H8 H10. *)
    (* subst. reflexivity. *)
  - dependent destruction H1;
    dependent destruction H0.
    pose proof IHtype _ _ _ H0 H1...
  - inversion H1;subst.
    inversion H2;subst.
    f_equal.
    pick_fresh x.
    assert (x `notin` L) as Hx1...
    assert (x `notin` L0) as Hx2...
    assert (x `notin` L1) as Hx3...
    specialize (H4 x Hx2).
    specialize (H5 x Hx3).
    specialize (H6 x Hx2).
    specialize (H8 x Hx3).
    pose proof H0 _ Hx1 _ _ _ H4 H5.
    subst.
    pose proof H0 _ Hx1 _ _ _ H6 H8...
Qed.

Lemma uniq_change_value {A:Type}: forall E X a (b:A) F,
  uniq (E ++ [(X, a)] ++ F) ->
  uniq (E ++ [(X, b)] ++ F).
Proof with auto.
  induction E;intros.
  - simpl. simpl in H. inversion H...
  - inversion H. subst.
    apply IHE with (b:=b) in H2.
    constructor...
Qed.

Lemma WFC_type: forall E n B,
  WFC E B n -> type B.
Proof with auto.
  intros.
  induction H...
  apply type_mu with (L:=L)...
Qed.

Lemma env_of_cenv_dom: forall E F, 
  env_of_cenv E = F -> dom E = dom F.
Proof.
  induction E.
  - intros. inversion H. reflexivity.
  - intros. destruct a. simpl in H.
    destruct F. { inversion H. }
    inversion H. rewrite H2.
    apply IHE in H2. simpl. rewrite H2.
    reflexivity.
Qed.

Lemma fv_tt_mu: forall T X X0, X `notin` fv_tt (typ_mu T) -> X <> X0 -> X `notin` fv_tt (open_tt T X0).
Admitted. 


Lemma bindings_ext_fvar_1: forall E1 E2 X B n,
  WFC (E1 ++ E2) B n -> X \notin dom E1 \u dom E2 ->
  WFC (E1 ++ X ~ 1 ++ E2) B n.
Proof with auto.
  intros E1 E2 X B n HE.
  revert X. dependent induction HE;intros...
  +
    destruct (Atom.eq_dec X X0)...
  +
    eapply WFC_mu with (L:= L \u dom E1 \u dom E2 \u {{ X}}) (m := m).
    - intros. specialize_x_and_L X0 L.
      pose proof H0 ((X0, 1)::E1) E2 eq_refl X. apply H5...
    - intros. specialize_x_and_L X0 L.
      pose proof H2 ((X0, m+1)::E1) E2 eq_refl X. apply H5...
Qed.

Lemma bindings_ext_fvar_1': forall E X B n,
  WFC E B n -> X \notin dom E ->
  WFC (X ~ 1 ++ E) B n.
Proof with auto.
  intros. apply bindings_ext_fvar_1 with (E1:=nil) (E2:=E)...
Qed.


Lemma type_change_var: forall E1 E2 X1 X2 A k n,
  (* type A -> *)
  WFC (E1 ++ X1 ~ k ++ E2 ) A n -> X2 \notin dom E1 \u dom E2 \u fv_tt A ->
  WFC (E1 ++ X2 ~ k ++ E2 ) (subst_tt X1 X2 A) n.
Proof with auto.
  intros E1 E2 X1 X2 A k n Hwf. intros H1.
  assert (Et: uniq (E1 ++ X2 ~ k ++ E2 )).
  { apply uniq_insert_mid...
    apply WFC_uniq in Hwf...
    apply uniq_remove_mid in Hwf... }
  revert H1.

  dependent induction Hwf;intros;simpl...
  - destruct (X == X1).
    { subst. pose proof binds_mid_eq _ _ _ _ _ _ H0 H... }
    { constructor...
      apply binds_app_uniq_iff... 
      apply binds_app_uniq_iff in H0...
      destruct H0; destruct_hypos.
      { left. split... intros C. apply H2. simpl in C.
        apply add_iff in C. destruct C...
        + subst... simpl in H1. exfalso...
        + apply add_iff...
      }
      { right. apply binds_app_uniq_iff in H0...
        destruct H0; destruct_hypos.
        3:{ apply uniq_app_2 in H... }
        { destruct H0. inversion H0. exfalso...
          inversion H0. }
        { split... } 
      }
    }
  - destruct (X == X1)...
    { subst.  simpl in H0. exfalso...
      rewrite dom_app in H0. apply H0.
      apply union_iff. simpl...
    }
    { apply WFC_fvar2... assert (X <> X2)...
      simpl in H1... }
  - pose proof (IHHwf1 _ _ _ _ eq_refl Et).
    pose proof (IHHwf2 _ _ _ _ eq_refl Et).
    simpl in H1...
  - pose proof (IHHwf _ _ _ _ eq_refl Et).
    simpl in H...
  -
    unfold subst_tt. fold subst_tt.
    apply WFC_mu with (L:= union (dom E1) (union (dom E2) (fv_tt (typ_mu T))) \u L \u {{ X2 }} \u {{ X1 }}) (m:=m).
    + intros.
      rewrite subst_tt_open_tt_var...
      specialize_x_and_L X L.
      specialize_x_and_L X L0.
      pose proof (H0 ((X,1)::E1) E2 X1 k eq_refl).
      apply H5...
      * constructor...
      * solve_notin. apply fv_tt_mu...
    + intros.
      rewrite subst_tt_open_tt_var...
      specialize_x_and_L X L.
      specialize_x_and_L X L0.
      pose proof (H2 ((X,m+1)::E1) E2 X1 k eq_refl).
      apply H5...
      * constructor...
      * solve_notin. apply fv_tt_mu...
Qed.


Lemma WFC_change_var: forall E1 E2 X1 X2 A k n,
  WF ((env_of_cenv E1) ++ X1 ~ bind_sub ++ (env_of_cenv E2)) A ->
  WFC (E1 ++ X1 ~ k ++ E2 ) A n -> X2 \notin dom E1 \u dom E2 \u fv_tt A ->
  WFC (E1 ++ X2 ~ k ++ E2 ) (subst_tt X1 X2 A) n.
Proof with auto.
  intros E1 E2 X1 X2 A k n Hwf.
  revert k n X2.
  (* remember ([(X0, bind_sub)] ++ env_of_cenv E2) as E. *)
  dependent induction Hwf;intros...
  -  
    dependent destruction H. constructor.
    apply uniq_insert_mid...
    apply uniq_remove_mid in H...
  -  
    dependent destruction H. constructor.
    apply uniq_insert_mid...
    apply uniq_remove_mid in H...
  -  
    dependent destruction H0.
    --
      unfold subst_tt. destruct (X == X1).
      +
        subst. pose proof binds_mid_eq _ _ _ _ _ _ H1 H0. subst.
        constructor.
        { apply uniq_insert_mid... apply uniq_remove_mid in H0... }
        apply binds_app_uniq_iff. 
        { apply uniq_insert_mid... apply uniq_remove_mid in H0... }
        right. split...
      +
        constructor.
        { apply uniq_insert_mid... apply uniq_remove_mid in H0... }
        apply binds_app_uniq_iff. 
        { apply uniq_insert_mid... apply uniq_remove_mid in H0... }
        apply binds_app_uniq_iff in H1...
        destruct H1; destruct_hypos.
        { left. split... intros C. apply H2. simpl in C.
          apply add_iff in C. destruct C...
          + subst... apply union_iff. right. apply union_iff. right. simpl.
            apply singleton_iff...
          + exfalso. apply H3. apply add_iff. right...
        }
        { right. apply binds_app_uniq_iff in H1...
          destruct H1; destruct_hypos.
          3:{ apply uniq_app_2 in H0... }
          { destruct H1. inversion H1. exfalso...
            inversion H1. }
          { split... }
        }
    --
      unfold subst_tt. destruct (X==X1).
      { subst. exfalso... apply H1. rewrite dom_app.
        apply union_iff. right. apply add_iff. left... }
      { simpl in H2. assert (X <> X2)... apply WFC_fvar2...
        apply uniq_remove_mid in H0... }
  - unfold subst_tt. fold subst_tt.
    dependent destruction H.
    pose proof (IHHwf1 E1 E2 X1 JMeq_refl k n1 X2 H).
    pose proof (IHHwf2 E1 E2 X1 JMeq_refl k n2 X2 H0).
    simpl in H1.
    constructor...
  - unfold subst_tt. fold subst_tt.
    dependent destruction H.
    pose proof (IHHwf E1 E2 X1 JMeq_refl k n X2 H).
    simpl in H0.
    constructor...
  -
    unfold subst_tt. fold subst_tt.
    dependent destruction H1.
    apply WFC_mu with (L:= union (dom E1) (union (dom E2) (fv_tt (typ_mu A))) \u L \u L0 \u {{ X2 }} \u {{ X1 }}) (m:=m).
    + intros.
      rewrite subst_tt_open_tt_var...
      specialize_x_and_L X L.
      specialize_x_and_L X L0.
      pose proof (H0 ((X, 1)::E1) E2 X1 JMeq_refl k m X2).
      apply H5...
      assert (X2 <> X)... solve_notin.
      apply fv_tt_mu...
    + intros.
      rewrite subst_tt_open_tt_var...
      specialize_x_and_L X L.
      specialize_x_and_L X L0.
      pose proof (H0 ((X, m+1)::E1) E2 X1 JMeq_refl k n X2).
      apply  H5...
      assert (X2 <> X)... solve_notin.
      apply fv_tt_mu...
Qed.

Lemma type_WFC: forall A F, 
  WF F A -> 
  forall E, uniq E -> env_of_cenv E = F ->
  exists t, WFC E A t.
Proof with auto.
  intros A F H.
  dependent induction H;intros; try solve [eexists;auto]...
  - hnf in H. apply binds_In in H.
    apply env_of_cenv_dom in H1.
    rewrite <- H1 in H.
    apply binds_In_inv in H.
    destruct H. exists x... 
  - specialize (IHWF1 _ H1 H2).
    specialize (IHWF2 _ H1 H2).
    destruct IHWF1. destruct IHWF2.
    exists (1 + max  x x0)...
  - specialize (IHWF _ H0 H1).
    destruct IHWF. exists (1 + x)...
  - pick_fresh W.
    assert (Htmp: W `notin` L)... 
    assert (uniq ((W,1)::E0))...
    pose proof (H0 W Htmp _ H3).
    assert (env_of_cenv ((W, 1) :: E0) = [(W, bind_sub)] ++ E ).
    { simpl. rewrite H2... }
    specialize (H4 H5). destruct H4.
    assert (uniq ((W,x+1)::E0))...
    pose proof (H0 W Htmp _ H6).
    assert (env_of_cenv ((W, x+1) :: E0) = [(W, bind_sub)] ++ E ).
    { simpl. rewrite H2... }
    specialize (H7 H8). destruct H7.
    exists (1 + x0).

    apply WFC_mu with (m:=x) (L:=union L
               (union (fv_tt A) (union (fl_tt A) (union (dom E) (dom E0)))) \u {{ W }});intros.
    + specialize_x_and_L W L.
      rewrite <- H2 in H.
      pose proof WFC_change_var nil E0 W X (open_tt A W) _ _ H H4.
      rewrite <- subst_tt_intro in H10...
      apply H10... solve_notin. apply fv_tt_mu...
    + specialize_x_and_L W L.
      rewrite <- H2 in H.
      pose proof WFC_change_var nil E0 W X (open_tt A W) _ _ H H7.
      rewrite <- subst_tt_intro in H10...
      apply H10... solve_notin. apply fv_tt_mu...
Qed.

Lemma bindings_ext: forall E1 E2 X k B n,
  WFC (E1 ++ E2) B n -> X \notin dom E1 \u dom E2 \u fv_tt B ->
  WFC (E1 ++ X ~ k ++ E2) B n.
Proof with auto.
  intros E1 E2 X k B n HE.
  revert X k. dependent induction HE;intros...
  +
    apply WFC_fvar2... simpl in H1...
  +
    simpl in H...
  +
    eapply WFC_mu with (L:= L \u dom E1 \u dom E2 \u {{ X}}) (m := m).
    - intros. specialize_x_and_L X0 L.
      pose proof H0 ((X0, 1)::E1) E2 eq_refl X k. apply H5...
      solve_notin. apply fv_tt_mu...
    - intros. specialize_x_and_L X0 L.
      pose proof H2 ((X0, m+1)::E1) E2 eq_refl X k. apply H5...
      solve_notin. apply fv_tt_mu...
Qed.


Lemma bindings_ext2: forall E X k B n,
  WFC E B n -> X \notin dom E \u fv_tt B ->
  WFC (X ~ k ++ E) B n.
Proof with auto.
  intros. apply bindings_ext with (E1:=nil) (E2:=E)...
Qed.

Lemma bindings_sem: forall A E1 E2 X m B (* n k *) r,
  WF ((env_of_cenv E1) ++ X ~ bind_sub ++ (env_of_cenv E2)) A ->
  (* WFC ((* E1 ++ *) X ~ 1 ++ E2) A n ->  *)
  WFC ( E1 ++  X ~ 1 ++ E2) B m ->
  WFC ( E1 ++  X ~ 1 ++ E2) (subst_tt X B A) r ->
  WFC ( E1 ++  X ~ m ++ E2) A r.
Proof with auto.
  intros A E1 E2 X0 m B r Hwf.
  revert B m r.
  (* remember ([(X0, bind_sub)] ++ env_of_cenv E2) as E. *)
  dependent induction Hwf;intros...
  -  
    dependent destruction H0. constructor.
    eapply uniq_change_value;eassumption.
  -
    dependent destruction H0. constructor. 
    eapply uniq_change_value;eassumption.
  -
    simpl in H1. destruct (X == X0).
    +
      pose proof WFC_type _ _ _ H0.
      pose proof (WFC_det _ _ _ _ H2 H0 H1).
      subst X m. constructor...
      apply WFC_uniq in H0.
      eapply uniq_change_value;eassumption.
    +
      inversion H1.
      --
        subst.
        constructor. { eapply uniq_change_value. apply H3. }
        apply binds_app_uniq_iff in H5...
        destruct H5.
        { apply binds_app_uniq_iff...
          eapply uniq_change_value;apply H3. }
        { destruct_hypos.
          apply binds_cons_uniq_iff in H2...
          2:{ eapply uniq_app_2... apply H3. }
          destruct H2;destruct_hypos...
          apply binds_app_uniq_iff...
          { eapply uniq_change_value;apply H3. }
          exfalso...
        }
      --
        subst. apply WFC_fvar2...
        eapply uniq_change_value. apply H3.
  - 
    specialize (IHHwf1 _ _ _ JMeq_refl).
    specialize (IHHwf2 _ _ _ JMeq_refl).
    dependent destruction H0.
    pose proof IHHwf1 _ _ _ H H0_.
    pose proof IHHwf2 _ _ _ H H0_0.
    constructor...
  -
    dependent destruction H0.
    specialize (IHHwf _ _ _ JMeq_refl _ _ _ H H0).
    constructor...
  -
    dependent destruction H2.
    assert (Htmp: exists t, 
      WFC (E1 ++ [(X0, m)] ++ E2) (typ_mu A) t).
    { pose proof type_WFC.
      assert (WF (env_of_cenv E1 ++ [(X0, bind_sub)] ++ env_of_cenv E2) 
    (typ_mu A)).
      { econstructor. intros. apply H... }
      specialize (H4 _ _ H5). clear H5.
      apply WFC_uniq in H1.
      assert (uniq (E1 ++ [(X0, m)] ++ E2)).
      { eapply uniq_change_value. apply H1. }
      specialize (H4 _ H5). clear H5.
      destruct H4.
      { unfold env_of_cenv.
        rewrite map_app. f_equal. }
      exists x... }
    destruct Htmp as [t' Htmp].
    inversion Htmp;subst.
    apply WFC_mu with (L:=L `union` L0 `union` dom E1 `union` dom E2 `union` {{ X0 }} `union` fv_tt B \u L1 ) (m:=m1);
    intros...
    specialize_x_and_L X L1.
    specialize_x_and_L X L0.
    specialize_x_and_L X L.

    rewrite subst_tt_open_tt_var in H2...
    2:{ apply WFC_type in H1... }
    rewrite subst_tt_open_tt_var in H3...
    2:{ apply WFC_type in H1... }

    pose proof (H0 ( [(X,m1+1)] ++ E1) 
          (E2)
          X0 JMeq_refl).

    apply H6 with (B:=B).
    + rewrite app_assoc. apply bindings_ext2...
    + pose proof (H0 ( [(X,1)] ++ E1) 
      (E2)
      X0 JMeq_refl).
      apply H8 with (m:=m) in H2.
      2:{ rewrite app_assoc. apply bindings_ext2... }
      assert (m1 = m0).
      { 
        pose proof WFC_type _ _ _ H5. 
        eapply WFC_det.
        + apply H9. 
        + apply H5.  
        + apply H2. }
      subst m1...
Qed.

Lemma find_eq_cons {A:Type}: forall E m b (w:A),
  m <> b ->
  find m ((b, w) :: E) = find m E.
Proof with auto.
  intros. simpl. apply Nat.eqb_neq in H. rewrite H...
Qed.

Lemma type_WFC': forall (A : typ),
  type A ->
  forall E : list (atom * nat),
  uniq E -> exists t : nat, WFC E A t.
Proof with auto. intros A Ht.
  induction Ht;simpl;intros...
  - exists 1...
  - exists 1...
  - destruct (KeySetProperties.In_dec X (dom E)).
    + apply binds_In_inv in i. destruct i.
      exists x...
    + exists 1...
  - destruct (IHHt1 _ H) as [n1 H1].
    destruct (IHHt2 _ H) as [n2 H2].
    exists (1 + max n1 n2)...
  - destruct (IHHt _ H) as [n H1].
    exists (1 + n)...
  - pick_fresh W.
    assert (W `notin` L)...
    pose proof H0 W H2.
    assert (uniq ((W, 1) :: E))...
    pose proof (H3 _ H4) as He1. destruct He1 as [m He1].
    assert (uniq ((W, m+1):: E))...
    specialize (H3 _ H5) as He2. destruct He2 as [n He2].
    exists (S n).
    apply WFC_mu with (L:= union L (union (fv_tt T) (union (fl_tt T) (dom E))) \u {{W}}) (m:=m).
    + intros.
      specialize_x_and_L X L.
      (* rewrite <- H2 in H. *)
      rewrite subst_tt_intro with (X:=W)...
      pose proof type_change_var nil E W X (open_tt T W) 1 m He1.
      apply H7. solve_notin. apply fv_tt_mu...
    +  intros.
      specialize_x_and_L X L.
      rewrite subst_tt_intro with (X:=W)...
      pose proof type_change_var nil E W X (open_tt T W) (m+1) n He2.
      apply H7. solve_notin. apply fv_tt_mu...
Qed.


Lemma bindings_find: forall A X,
    type A -> X `notin` fv_tt A ->
    bindings (open_tt A (typ_rcd X (open_tt A X))) =
    bindings_rec [(1, 1 + bindings_rec [(1,1)] 1 A)] 1 A.
Proof.
  intros.
  assert (type (typ_mu A)). { admit. }
  assert (type ((open_tt A (typ_rcd X (open_tt A X))))). { admit. }
  pose proof type_WFC' _ H2 nil (uniq_nil _).
  destruct H3.
  pose proof type_WFC' (typ_mu A) H1 [(X, 1)].
Admitted.



(******************************
 ******************************
 ********** Testings **********
 ******************************
 ******************************)


 Parameter X : atom.
 Parameter Y : atom.
 Parameter Z : atom.
 

(* mu x. mu y. x -> y *)
Compute 
  (bindings (typ_mu (typ_mu (typ_arrow (typ_bvar 1) (typ_bvar 0))))).

  
(* mu y. {x : mu z. x -> z} -> y *)
Compute 
  (bindings ((typ_mu (typ_arrow  
                          (typ_rcd X ( 
                            (typ_mu (typ_arrow (typ_bvar 0) X))))
                          (typ_bvar 0)
                          )))).


(* {x : mu z. x -> z} -> {y : {x : mu z. x -> z} -> y} *)
Compute 
(bindings (((typ_arrow  
                      (typ_rcd X ( 
                        (typ_mu (typ_arrow (typ_bvar 0) X))))
                      (typ_rcd Y (typ_arrow  
                        (typ_rcd X ( 
                          (typ_mu (typ_arrow (typ_bvar 0) X))))
                        Y
                      ))
                    )))).

(* {x : x -> {z: x -> z}} -> {y : {x : x -> {z: x -> z}} -> y} *)
Compute 
(bindings (((typ_arrow  
                      (typ_rcd X ( 
                        ((typ_arrow (typ_rcd Z (typ_arrow Z X)) X))))
                      (typ_rcd Y (typ_arrow  
                        (typ_rcd X ( 
                          (typ_arrow (typ_rcd Z (typ_arrow Z X)) X)))
                        Y
                      ))
)))).


Fixpoint get_inner_body (T:typ) : typ :=
  match T with
  | typ_mu A => A
  | _ => T
  end.
Definition Nunfold (A:typ) (X:atom) := open_tt A (typ_rcd X (open_tt A X)).
                              

Definition  T := (typ_mu (typ_mu (typ_mu (typ_arrow 
(typ_arrow (typ_bvar 1) (typ_bvar 2))
(typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 1) (typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 1) (typ_arrow (typ_bvar 0) (typ_bvar 0)))))))) 
)))).

(* Definition  T := (typ_mu (typ_mu (typ_mu (typ_arrow 
(typ_arrow (typ_bvar 1) (typ_bvar 2))
(typ_arrow typ_nat (typ_arrow typ_nat (typ_arrow typ_nat (typ_arrow typ_nat (typ_arrow typ_nat (typ_arrow typ_nat (typ_arrow typ_nat typ_nat))))))) 
)))). *)

Compute (bindings ((typ_mu (typ_bvar 0)))).
Compute (bindings ((Nunfold  (get_inner_body (typ_mu (typ_bvar 0))) X))).

Compute (bindings T).
Compute (bindings (Nunfold (get_inner_body T) X)).
Compute (bindings 
    (Nunfold  (get_inner_body
      (Nunfold (get_inner_body T) X))
      Y)).
  Compute (bindings 
    (Nunfold  (get_inner_body
      (Nunfold  (get_inner_body
        (Nunfold (get_inner_body T) X))
        Y)) Z)).
Compute 
  (bindings ((typ_mu (typ_arrow 
          (typ_arrow
            (typ_mu (typ_arrow (typ_arrow X X) (typ_bvar 0)))
            (typ_mu (typ_arrow (typ_arrow X X) (typ_bvar 0)))) 
          (typ_bvar 0))))).

Compute (bindings (typ_mu (typ_nat))).
Compute (bindings (Nunfold (get_inner_body (typ_mu typ_nat)) X)).
Compute (bindings (typ_mu (typ_bvar 0))).
Compute (bindings (Nunfold (get_inner_body (typ_mu (typ_bvar 0))) X)).



(* mu x. mu y. x -> x -> y *)
Definition Origin := (typ_mu (typ_mu (typ_arrow (typ_bvar 1) (typ_arrow (typ_bvar 1) (typ_bvar 0))))).

Compute  (bindings Origin). (* 21 *)


Definition T1 := (typ_mu (typ_arrow (typ_bvar 1) (typ_arrow (typ_bvar 1) (typ_bvar 0)))).

Goal  T1 = get_inner_body Origin.
unfold Origin.
unfold T1.
auto.
Qed.


Definition T2 := Nunfold T1 X.

Compute T2.

Compute (bindings T2). (* 5 = 1 * 5 *)

Compute  (bindings T1). (* 1 *)

Definition T3 := 
         (typ_arrow (typ_rcd X (typ_mu (typ_arrow X (typ_arrow X 0))))
                    (typ_arrow (typ_rcd X (typ_mu (typ_arrow X (typ_arrow X 0)))) 0)).

Goal  T3 = get_inner_body T2.
unfold Origin.
unfold T1.
auto.
Qed.



Definition T4 := Nunfold T3 Y.

Compute T4.
Compute (bindings T4). (* 4 = 2 * 2 *)

Compute (bindings T3). (* 2 *)

(* mu z . mu x. mu y. x -> z -> y *)
Definition S0 := typ_mu (typ_mu (typ_mu (typ_arrow (typ_bvar 1) (typ_arrow (typ_bvar 2) (typ_bvar 0))))).

Compute (bindings S0). (* 85 *)

Definition S1 := Nunfold (get_inner_body S0) Z.

Compute (bindings S1). (* 49 = 7 * 7 *)

Compute S1.

Compute (bindings (get_inner_body S0)). (* 7 *)

Definition S2 := Nunfold (get_inner_body S1) X.

Compute S2.

Compute (bindings S2). (* 45 = 15 * 3 *)

Compute (bindings (get_inner_body S1)). (* 15 *)

Definition S3 := Nunfold (get_inner_body S2) Y.

Compute S3.

Compute (bindings S3). (* 44 = 22 * 2 *)

Compute (bindings (get_inner_body S2)). (* 22 *)

Lemma bindings_mu: forall A X,
  X \notin fv_tt A ->
  1 + bindings (open_tt A (typ_rcd X (open_tt A X))) <= bindings (typ_mu A).
Proof with auto.
  induction A.
Abort.





(*

mu x. mu y. x -> {z : mu x. mu y. x -> z -> y} -> y

mu y. {x: mu y. x -> {z : mu x. mu y. x -> z -> y} -> y} -> {z : mu x. mu y. x -> z -> y} -> y
*)
