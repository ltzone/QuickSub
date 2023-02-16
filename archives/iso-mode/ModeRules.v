Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Typesafety.


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
| WFS_rcd : forall E l T,
    WFS E T ->
    WFS E (typ_rcd l T)
| WFS_rec : forall L E A,
    (* (forall X , X \notin L -> forall im, 
        WFS (X ~ bind_sub im ++ E) (open_tt A (typ_rcd X (open_tt A X)))) -> *)
      (forall  X , X \notin L -> forall im,
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
    wf_env E -> A <> typ_top ->
    Sub im Lt E A typ_top
| Sa_fvar_pos: forall E X im cm,
    wf_env E -> binds X (bind_sub im) E ->
    Sub im cm E (typ_fvar X) (typ_fvar X)
| Sa_fvar_neg: forall E X im,
    wf_env E -> binds X (bind_sub (flip_im im)) E ->
    Sub im Eq E (typ_fvar X) (typ_fvar X)
| Sa_arrow: forall E A1 A2 B1 B2 cm im,
    Sub (flip_im im) cm E B1 A1 ->
    Sub im cm E A2 B2 ->
    Sub im cm E (typ_arrow A1 A2) (typ_arrow B1 B2)
| Sa_rec: forall L A1 A2 E im cm,
    (forall X,  X \notin L -> 
        Sub im cm (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
    Sub im cm E (typ_mu A1) (typ_mu A2).

#[global] Hint Constructors Sub wf_env WFS : core.

Example test_Sub_1: Sub Pos Lt empty (typ_mu (typ_arrow typ_top 0)) (typ_mu (typ_arrow 0 0)).
Proof with auto.
  apply Sa_rec with (L:={}).
  intros.
  apply Sa_arrow;simpl;try rewrite eq_dec_refl...
  apply Sa_top_lt. { constructor... } { intros C. inversion C. }
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
  inversion H8.
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
  - induction B;inversion H1...
    destruct (n == n0);inversion H3. simpl in H, H0.
    rewrite IHA with (n:=n) (B:=B)...
Qed.


Theorem Msub_eq_sem: forall E im A B,
    Sub im Eq E A B -> A = B.
Proof with auto.
  intros.
  dependent induction H...
  - rewrite IHSub1, IHSub2...
  - pick_fresh X. specialize_x_and_L X L.
    f_equal. apply open_tt_fresh_eq_inv with (X:=X)...
Qed.

End M.

Fixpoint mk_Menv (E:env) : M.env :=
  match E with
    | nil => nil
    | (X, bind_sub) :: E' => (X, M.bind_sub M.Pos) :: mk_Menv E'
    | (X, bind_typ T) :: E' => (X, M.bind_typ T) :: mk_Menv E'
  end.

Inductive is_Menv (im: M.IsoMode): M.env -> env -> Prop :=
  | is_Menv_nil: is_Menv im nil nil
  | is_Menv_sub: forall E' E X,
      is_Menv im E' E ->
      is_Menv im ((X, M.bind_sub M.Pos) :: E') ((X, bind_sub) :: E)
  | is_Menv_typ: forall E' E X T,
      is_Menv im E' E ->
      is_Menv im ((X, M.bind_typ T) :: E') ((X, bind_typ T) :: E).


(* Theorem Msub_sound: forall E im A B,
  M.Sub im M.Lt (mk_Menv E) A B -> Sub E A B.
Proof with auto.
  intros. dependent induction H...
  - constructor... admit.
  - constructor... admit.
  - constructor... admit. admit.
  - admit. *)

Theorem Msub_sound:
  forall A, type A -> 
  forall B, type B ->
  forall E E' im,
  is_Menv im E' E ->
  (M.Sub im M.Lt E' A B -> Sub E A B)
  /\ (M.Sub im M.Lt E' B A -> Sub E B A).
Proof with auto.
  intros A HA.
  induction HA;intros.
  - split;intros.
    + inversion H1;subst.
      admit. admit.
    + inversion H1;subst. admit. admit.
  - split;intros.
    + inversion H1;subst...
      admit. admit.
    + inversion H1;subst...
      admit.
  - split;intros.
    + inversion H1;subst...
      admit. admit.
    + inversion H1;subst... admit.
  - split;intros.
    + inversion H1;subst.
      { admit. } 
     apply S_arrow. 
      { destruct IHHA1 with (B:=B1) (E:=E)(E':=E')(im:=M.flip_im im)... admit. }
      { apply IHHA2 with (E':=E') (im:=im)... inversion H... }
    
    apply S_rec with (L:=L). admit. admit.
      intros. specialize_x_and_L X L.

  generalize dependent E.
  dependent induction H0;intros...
  - constructor. admit.
  - constructor... admit.
  - constructor... admit. admit.
  - constructor... admit. admit.
  - constructor...
    + apply IHSub1...

Theorem Sub_sem: forall E A B,
  Sub E A B -> M.Sub M.Pos M.Eq (mk_Menv E) A B \/ M.Sub M.Pos M.Lt (mk_Menv E) A B.
Admitted.

Theorem Msub_eq_sem: forall E im A B,
  M.Sub im M.Eq (mk_Menv E) A B <-> A = B.
Admitted.
