Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import PositiveBase.


Module M.

Inductive IsoMode := Neg | Pos.

Inductive CmpMode := Lt | Eq.


Inductive binding : Set :=
  | bind_sub : IsoMode -> binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).
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

Definition max_cm (cm1 cm2 : CmpMode) : CmpMode :=
  match cm1, cm2 with
    | Lt, _ => Lt
    | _, Lt => Lt
    | Eq, Eq => Eq
  end.

(*
IsoMode := + | -
E [IsoMode] |- T1 [CmpMode] T2
*)
Inductive Sub : IsoMode -> CmpMode -> env -> typ -> typ -> Prop :=
(* 
|- E
----------------
E [_]|- nat <:= nat 
*)
| Sa_nat: forall E im cm,
    wf_env E ->
    Sub im cm E typ_nat typ_nat
(*
|- E
----------------
E [=] |- top <:= top
*)
| Sa_top_eq: forall E im cm,
    wf_env E ->
    Sub im cm E typ_top typ_top  
(*
TODO: is != top necessary?, if we are going to interpret <: as no greater than
|- E, A != top
----------------
E [<] |- A <:= top
*)
| Sa_top_lt: forall E im A,
    wf_env E -> WFS E A ->
    Sub im Lt E A typ_top
| Sa_fvar_pos: forall E X im cm,
    wf_env E -> binds X (bind_sub im) E ->
    Sub im cm E (typ_fvar X) (typ_fvar X)
| Sa_fvar_neg: forall E X im,
    wf_env E -> binds X (bind_sub (flip_im im)) E ->
    Sub im Eq E (typ_fvar X) (typ_fvar X)
| Sa_arrow: forall E A1 A2 B1 B2 cm1 cm2 im,
    Sub (flip_im im) cm1 E B1 A1 ->
    Sub im cm2 E A2 B2 ->
    Sub im (max_cm cm1 cm2) E (typ_arrow A1 A2) (typ_arrow B1 B2)
| Sa_rec: forall L A1 A2 E im cm,
    (forall X,  X \notin L -> 
        Sub im cm (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
    Sub im cm E (typ_mu A1) (typ_mu A2).

#[global] Hint Constructors Sub wf_env WFS : core.

Lemma WFS_type: forall E T,
    WFS E T -> type T.
Proof with auto.
  intros. induction H...
  apply type_mu with (L:=L)...
Qed.

Lemma uniq_from_wf_env: forall E,
    wf_env E -> uniq E.
Proof.
  intros. induction H; auto.
Qed.

Example test_Sub_1: Sub Pos Lt empty (typ_mu (typ_arrow typ_top 0)) (typ_mu (typ_arrow 0 0)).
Proof with auto.
  apply Sa_rec with (L:={}).
  intros. unfold open_tt. simpl.
  apply Sa_arrow with (cm1:=Lt) (cm2:=Eq);simpl;try rewrite eq_dec_refl...
  apply Sa_top_lt.
  { constructor... }
  { apply WFS_fvar with (im:=Pos)... }
  apply Sa_fvar_pos. { constructor... } { constructor... }
Qed.

Example test_Sub_2: ~ (Sub Pos Eq empty (typ_mu (typ_arrow 0 typ_nat)) (typ_mu (typ_arrow 0 typ_top))).
Proof with auto.
  intros C.
  inversion C;subst...
  pick_fresh X. specialize_x_and_L X L.
  unfold open_tt in H4. simpl in H4.
  inversion H4;subst...
  simpl in H6, H8.
  inversion H8;subst... destruct cm1;inversion H.
Qed.

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


Theorem Msub_eq_sem: forall E im A B,
    Sub im Eq E A B -> A = B.
Proof with auto.
  intros.
  dependent induction H...
  - destruct cm1, cm2;inversion x. rewrite IHSub1, IHSub2...
  - pick_fresh X. specialize_x_and_L X L.
    f_equal. apply open_tt_fresh_eq_inv with (X:=X)...
Qed.

Theorem Sub_regular: forall im cm E A B,
    Sub im cm E A B -> wf_env E /\ WFS E A /\ WFS E B.
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
Qed.

(* Use a predicate to relate A with all variables in E, s.t. ensure the posvar property *)

Inductive WFM: env -> IsoMode -> typ -> Prop :=
| WFM_top : forall E im, WFM E im typ_top
| WFM_nat : forall E im, WFM E im typ_nat
| WFM_fvar : forall E im X, (* <--- the difference *)
    wf_env E -> binds X (bind_sub im) E -> WFM E im (typ_fvar X)
| WFM_arrow : forall E im A1 A2,
    WFM E (flip_im im) A1 -> WFM E im A2 -> WFM E im (typ_arrow A1 A2)
| WFM_rec : forall L E im A,
    (forall X, X \notin L -> WFM (X ~ bind_sub im ++ E) im (open_tt A X)) ->
    WFM E im (typ_mu A).

#[global] Hint Constructors Sub wf_env WFM : core.

Theorem Reflexivity: forall im E A,
    wf_env E -> WFM E im A -> Sub im Lt E A A.
Proof with auto.
  intros.
  induction H0...
  - apply Sa_arrow with (cm1:=Lt) (cm2:=Lt)...
  - apply Sa_rec with (L:=L \u dom E)...
Qed.

End M.


Lemma Msub_posvar: forall E im A B X,
    M.Sub im M.Lt E A B -> 
    (binds X (M.bind_sub im) E -> posvar Pos X A B)
    /\ (binds X (M.bind_sub (M.flip_im im)) E -> posvar Neg X A B).
Proof with auto.
  intros. generalize dependent X.
  dependent induction H...
  - split;intros.
    + constructor. apply M.WFS_type in H0...
    + constructor. apply M.WFS_type in H0...
  - split;intros.
    + destruct (X == X0).
      * subst. apply pos_fvar_x.
      * apply pos_fvar_y...
    + destruct (X == X0).
      * subst. apply M.uniq_from_wf_env in H.
        pose proof binds_unique _ _ _ _ _ H0 H1 H.
        inversion H2. destruct im;inversion H4.
      * apply pos_fvar_y...
  - intros. destruct IHSub1 with (X:=X)...
    destruct IHSub2 with (X:=X)... 
    split;intros.
    + constructor... apply H2. destruct im...
    + constructor...
  - split;intros.
    + apply pos_rec with (L:=L)...
      { intros. specialize_x_and_L Y L. destruct H0 with (X:=X)... }
      { intros. specialize_x_and_L Y L. destruct H0 with (X:=Y)... }
    + apply pos_rec with (L:=L)...
      { intros. specialize_x_and_L Y L. destruct H0 with (X:=X)... }
      { intros. specialize_x_and_L Y L. destruct H0 with (X:=Y)... }
Qed.


Fixpoint mk_Menv (E:env) : M.env :=
  match E with
    | nil => nil
    | (X, bind_sub) :: E' => (X, M.bind_sub M.Pos) :: mk_Menv E'
    | (X, bind_typ T) :: E' => (X, M.bind_typ T) :: mk_Menv E'
  end.

Fixpoint mk_env (E:M.env) : env :=
  match E with
    | nil => nil
    | (X, M.bind_sub im) :: E' => (X, bind_sub) :: mk_env E'
    | (X, M.bind_typ T) :: E' => (X, bind_typ T) :: mk_env E'
  end.

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


(* Theorem Msub_sound: forall E im A B,
  M.Sub im M.Lt (mk_Menv E) A B -> Sub E A B.
Proof with auto.
  intros. dependent induction H...
  - constructor... admit.
  - constructor... admit.
  - constructor... admit. admit.
  - admit. *)
Lemma mk_Menv_is_Menv: forall E,
  is_Menv (mk_Menv E) E.
Proof with auto.
  induction E...
  + constructor.
  + destruct a. destruct b...
    - constructor...
    - constructor...
Qed.

Lemma mk_env_is_Menv: forall E,
  is_Menv E (mk_env E).
Proof with auto.
  induction E...
  + constructor.
  + destruct a. destruct b...
    - destruct i; constructor...
    - constructor...
Qed.


Lemma Msub_sound_aux:
  forall A, type A -> 
  forall B, type B ->
  forall E E' im,
  is_Menv E' E ->
  (M.Sub im M.Lt E' A B -> wk_sub E A B)
  /\(M.Sub (M.flip_im im) M.Lt E' B A -> wk_sub E B A).
(* 
Direct induction on M.Sub fails in contravarient case.

Proof with auto.
  intros.
  dependent induction H2...
  - apply sam2_nat... admit.
  - apply sam2_top... admit.
  - apply sam2_top... admit. admit.
  - apply sam2_fvar... admit. admit.
  - inversion H;inversion H0;subst. apply sam2_arrow...
    + apply IHSub1... *)
Proof with auto.
  intros A HA.
  induction HA;intros.
  - split;intros.
    + inversion H1;subst.
      { constructor... eapply Menv_wf_env;eassumption. }
      { constructor... eapply Menv_wf_env;eassumption. }
    + inversion H1;subst.
      { constructor... eapply Menv_wf_env;eassumption. }
      { constructor...
        + apply MWFS_WF with (E':=E)in H4 ...
          apply completeness_wfa. apply soundness_wf...
        + eapply Menv_wf_env;eassumption. }
  - split;intros.
    + inversion H1;subst...
      { constructor... eapply Menv_wf_env;eassumption. }
      { constructor... eapply Menv_wf_env;eassumption. }
    + inversion H1;subst...
      { constructor... eapply Menv_wf_env;eassumption. }
  - split;intros.
    + inversion H1;subst...
      { constructor... 
        + apply MWFS_WF with (E':=E)in H4 ...
          apply completeness_wfa. apply soundness_wf...
        + eapply Menv_wf_env;eassumption. }
      { constructor...
        + apply is_Menv_binds with (E':=E) in H7...
        + eapply Menv_wf_env;eassumption. }
    + inversion H1;subst...
      { constructor...
        + apply is_Menv_binds with (E':=E) in H8...
        + eapply Menv_wf_env;eassumption. }
  - split;intros.
    + inversion H1;subst.
      { constructor...
        + apply completeness_wfa. apply soundness_wf...
          apply MWFS_WF with (E:=E')...
        + eapply Menv_wf_env;eassumption. }
      inversion H;subst.
      destruct IHHA1 with (B:=B1) (E:=E) (E':=E') (im := im)...
      destruct IHHA2 with (B:=B2) (E:=E) (E':=E') (im := im)...
    + inversion H1;subst.
      inversion H;subst.
      destruct IHHA1 with (B:=A1) (E:=E) (E':=E') (im := im)...
      destruct IHHA2 with (B:=A2) (E:=E) (E':=E') (im := im)...
      apply W_arrow...
      apply H2. destruct im...
  - split;intros.
    + inversion H3;subst.
      { constructor...
        + apply completeness_wfa. apply soundness_wf...
          apply MWFS_WF with (E:=E')...
        + eapply Menv_wf_env;eassumption. }
      apply W_rec with (L:=L \u L0 \u fv_tt A2); intros.
      * specialize_x_and_L X L. specialize_x_and_L X L0. 
        destruct H0 with (B:=open_tt A2 X)
          (E:=X ~ bind_sub ++ E) (E':=X ~ M.bind_sub im ++ E') (im := im)...
        { apply type_mu_open... }
        {  destruct im; constructor... }
      * specialize_x_and_L X L. specialize_x_and_L X L0.
        apply Msub_posvar with (X:=X) in H8. destruct H8...
    + inversion H3;subst.
      apply W_rec with (L:=L \u L0 \u fv_tt A1); intros.
      * specialize_x_and_L X L. specialize_x_and_L X L0.
        destruct H0 with (B:=open_tt A1 X)
          (E:=X ~ bind_sub ++ E) (E':=X ~ M.bind_sub (M.flip_im im) ++ E') (im := im)...
        { apply type_mu_open... }
        { destruct im; constructor... }
      * specialize_x_and_L X L. specialize_x_and_L X L0.
        apply Msub_posvar with (X:=X) in H9. destruct H9...
Qed.


Theorem Msub_sound: forall E im A B,
  M.Sub im M.Lt E A B -> sub (mk_env E) A B.
Proof with auto.
  intros.
  destruct Msub_sound_aux with (A:=A) (B:=B) (E:=mk_env E) (E':=E) (im:=im)...
  { apply M.Sub_regular in H. destruct_hypos. apply M.WFS_type in H0... }
  { apply M.Sub_regular in H. destruct_hypos. apply M.WFS_type in H1... }
  { apply mk_env_is_Menv... }
  apply sub_amber_2_to_sub.
  apply wk_sub_to_sam2...
Qed.


Fixpoint mk_Menv_with (im:M.IsoMode) (E:env) : M.env :=
  match E with
    | nil => nil
    | (X, bind_sub) :: E' => (X, M.bind_sub im) :: mk_Menv_with im E'
    | (X, bind_typ T) :: E' => (X, M.bind_typ T) :: mk_Menv_with im E'
  end.
(* 
Lemma Msub_complete_aux2: forall E A B,
  wk_sub E A B ->
  forall im,
  (M.Sub im M.Lt (mk_Menv_with im E) A B).
Proof with auto.
  intros E A B Hsub.
  induction Hsub;intros...
  - admit.
  - admit.
  - apply M.Sa_fvar_pos. admit. admit. 
  - constructor.
    + apply IHHsub1.
  
  admit. (* cannot merge two ex contexts *)
Admitted.   *)

(* 

Assignment proposal

decide posvar X A B?
if so then same as im else flip im

*)


Inductive is_Menv_str (im:M.IsoMode) (A:typ) (B:typ): M.env -> env -> Prop :=
| is_Menv_str_nil: is_Menv_str im A B nil nil
| is_Menv_str_pos: forall X E' E,
    is_Menv_str im A B E' E ->
    posvar Pos X A B ->
    is_Menv_str im A B ((X, M.bind_sub im) :: E') ((X, bind_sub) :: E)
| is_Menv_str_neg: forall X E' E,
    is_Menv_str im A B E' E ->
    (* ~ posvar Pos X A B -> *)
    posvar Neg X A B ->
    is_Menv_str im A B ((X, M.bind_sub (M.flip_im im)) :: E') ((X, bind_sub) :: E)
.

Lemma is_Menv_sem: forall im A B E E' X,
  is_Menv_str im A B E E' ->
  binds X bind_sub E' ->
  (binds X (M.bind_sub im) E /\ posvar Pos X A B)
  \/ (binds X (M.bind_sub (M.flip_im im)) E /\ posvar Neg X A B).
Proof with auto.
  intros. generalize dependent X.
  induction H;intros...
  - inversion H0.
  - destruct H1...
    + inversion H1;subst...
    + destruct IHis_Menv_str with (X:=X0);destruct_hypos...
  - destruct H1...
    + inversion H1;subst...
    + destruct IHis_Menv_str with (X:=X0);destruct_hypos... 
Qed.

Lemma is_Menv_str_arr_distrb:
  forall im A1 A2 B1 B2 E E',
  is_Menv_str im (typ_arrow A1 A2) (typ_arrow B1 B2) E' E ->
  is_Menv_str (M.flip_im im) B1 A1 E' E /\ 
  is_Menv_str im A2 B2 E' E.
Proof with auto.
  intros.
  dependent induction H.
  - split;try constructor.
  - destruct_hypos. inversion H0;subst. split.
    + replace (M.bind_sub im) with
        (M.bind_sub (M.flip_im (M.flip_im im))) by (destruct im; auto)...
      apply is_Menv_str_neg...
    + apply is_Menv_str_pos...
  - destruct_hypos. inversion H0;subst. split.
    + apply is_Menv_str_pos...        
    + apply is_Menv_str_neg... 
Qed.


Lemma posvar_refl: forall X T m, 
  type T -> X \notin fv_tt T -> posvar m X T T.
Proof with auto.
  intros. revert m. induction H;intros...
  - destruct m.
    + destruct (X == X0)...
      subst. exfalso. apply H0. simpl...
    + destruct (X == X0)...
      subst...
  - simpl in H0...
  - simpl in H0...
    apply pos_rec_t with (L:=L)...
Qed.


Lemma is_Menv_str_mu_distrb:
  forall im A B E E',
    is_Menv_str im (typ_mu A) (typ_mu B) E' E ->
  exists L, forall X, X \notin L ->
    is_Menv_str im (open_tt A X) (open_tt B X) E' E.
Proof with auto.
  intros.
  dependent induction H;intros.
  - exists (fv_tt A \u fv_tt B).  constructor.
    (* Search posvar fv_tt. *)
  - destruct IHis_Menv_str as [L ].
    inversion H0;subst.
    + exists (L \u L0 \u {{X}}). intros.
      specialize_x_and_L X0 L.
      specialize_x_and_L X0 (L0 \u {{X}}).
      apply is_Menv_str_pos...
    + exists (L \u L0 \u {{X}}). intros.
      specialize_x_and_L X0 L.
      specialize_x_and_L X0 (L0 \u {{X}}).
      apply is_Menv_str_pos...
      apply posvar_refl...
      apply notin_fv_tt_open_aux...
  - destruct IHis_Menv_str as [L ].
    inversion H0;subst.
    + exists (L \u L0 \u {{X}}). intros.
      specialize_x_and_L X0 L.
      specialize_x_and_L X0 (L0 \u {{X}}).
      apply is_Menv_str_neg...
    + exists (L \u L0 \u {{X}}). intros.
      specialize_x_and_L X0 L.
      specialize_x_and_L X0 (L0 \u {{X}}).
      apply is_Menv_str_neg...
      apply posvar_refl... 
      apply notin_fv_tt_open_aux...
Qed.

Lemma is_Menv_str_WF: forall im A E E',
  is_Menv_str im A A E' E ->
  WF E A ->
  M.Sub im M.Lt E' A A.
Proof with auto.
  intros. generalize dependent im.
  generalize dependent E'.
  dependent induction H0;intros...
  - apply M.Sa_top_eq... admit.
  - apply M.Sa_nat... admit.
  - apply is_Menv_sem with (X:=X) in H0... destruct H0;
    destruct_hypos...
    + constructor... admit.
    + inversion H1;subst. exfalso...
  - apply is_Menv_str_arr_distrb in H...
    destruct_hypos...
  - apply is_Menv_str_mu_distrb in H3...
    destruct H3 as [L0].
    apply M.Sa_rec with (L:=L \u L0 \u fv_tt A)... intros.
    specialize_x_and_L X L0.
    specialize_x_and_L X L...
    apply H0. constructor...
    Search posvar open_tt.
    apply posvar_refl...
    { apply wf_type in H... }
    apply notin_fv_tt_open_aux...
    + apply IHWF1...
    + apply IHWF2... *)

Lemma Msub_complete_aux_relax: forall E A B,
  wk_sub E A B ->
  forall E' im,
  is_Menv_str im A B E' E ->
  (M.Sub im M.Lt E' A B).
Proof with auto.
  intros E A B Hsub.
  induction Hsub;intros...
  - apply M.Sa_nat... admit.
  - destruct (decide_typ A typ_top).
    + subst. constructor... admit.
    + apply M.Sa_top_lt... admit. admit.
  - pose proof is_Menv_sem _ _ _ _ _ X H1 H.
    destruct H2;destruct_hypos.
    + apply M.Sa_fvar_pos... admit.
    + inversion H3;subst... exfalso...
  - apply is_Menv_str_arr_distrb in H.
    destruct_hypos. constructor...
  - 
    apply is_Menv_str_mu_distrb in H2.
    destruct H2 as [L0].
    apply M.Sa_rec with (L:=L \u L0).
    intros.
    specialize_x_and_L X L.
    specialize_x_and_L X L0.
    apply H0... constructor...
  - apply M.Reflexivity...  admit. (* reflexivity *)
Admitted.


Lemma Msub_complete_aux: forall E A B,
  wk_sub E A B ->
  forall E' im,
  is_Menv E' E -> M.WFM E' im A ->
   M.WFM E' im B -> (* cannot be dropped otherwise arrow case fails *)
  (M.Sub im M.Lt E' A B).
Proof with auto.
  intros E A B Hsub.
  induction Hsub;intros...
  - apply M.Sa_nat... admit.
  - destruct (decide_typ A typ_top).
    + subst. constructor... admit.
    + apply M.Sa_top_lt... admit. admit.
  - apply M.Reflexivity... admit. (* reflexivity *)
  - inversion H0;subst. inversion H1;subst...
  - inversion H3;subst.
    inversion H4;subst.
    apply M.Sa_rec with (L:=L \u L0 \u L1).
    intros.
    specialize_x_and_L X L.
    specialize (H0 (X ~ M.bind_sub im ++ E') im).
    apply H0... destruct im; constructor...
  - apply M.Reflexivity...  admit. (* reflexivity *)
Admitted.


Lemma WF_menv_nil: forall A im,
  WF nil A -> M.WFM nil im A.
Proof with auto.
  intros. revert im. dependent induction H;intros...
  - constructor... exists (mk_Menv E), (M.Pos);split... apply mk_Menv_is_Menv...
  - exists (mk_Menv E), (M.Pos);split... apply mk_Menv_is_Menv...
  - admit.
   (* exists (mk_Menv_with X im E). *)
  - destruct IHWF1 as [E1 [im1 [? ?]]], IHWF2 as [E2 [im2 [? ?]]].
    (* exists (E1 ++ E2), (M.Pos);split...
    + apply Menv_app_is_Menv...
    + apply M.WFM_arrow... *)
Admitted. 

Theorem Msub_complete: forall A B,
  wk_sub nil A B ->
  forall im, M.Sub im M.Lt nil A B.
Proof with auto.
  intros.
  apply Msub_complete_aux with (E:=nil)...
  constructor. apply WF_

(* or, closed types are enough ? *)




(* Fixpoint mk_benv_for (m:) (A:typ)  *)


Lemma Msub_complete_menv_ex: forall E A B,
  wk_sub E A B -> 
  exists E' im, is_Menv E' E /\ M.WFM E' im A /\ M.WFM E' im B.
Proof with auto.
  intros.
  induction H...
  - exists (mk_Menv E), (M.Pos);split;[|split]... apply mk_Menv_is_Menv...
  - 
    (* exists (mk_Menv_with X im E);split;[|split]... apply mk_Menv_is_Menv... *)
  - destruct IHwk_sub1...
    + subst. destruct IHwk_sub2...
      * subst. left... 
      * destruct H0 as [E' [? [? ?]]].
        right. exists E';split;[|split]...
    + destruct H as [E' [? [? ?]]].
      right. exists E';split;[|split]...


  exists (mk_Menv E), (M.Pos);split;[|split]... apply mk_Menv_is_Menv...



Lemma Msub_sound_aux:
  forall A, type A -> 
  forall B, type B ->
  wk_sub E B A ->
  forall E E' im,
  is_Menv E' E ->
  (M.Sub im M.Lt E' A B -> wk_sub E A B)
  /\(M.Sub (M.flip_im im) M.Lt E' B A -> wk_sub E B A).


Theorem Sub_sem: forall E A B,
  Sub E A B -> M.Sub M.Pos M.Eq (mk_Menv E) A B \/ M.Sub M.Pos M.Lt (mk_Menv E) A B.
Admitted.

Theorem Msub_eq_sem: forall E im A B,
  M.Sub im M.Eq (mk_Menv E) A B <-> A = B.
Admitted.
