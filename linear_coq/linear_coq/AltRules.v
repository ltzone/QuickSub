Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export LinearRule.


Inductive Result := 
  | Lt : Result
  | Eq : atoms -> Result
  .


Definition compose_res (r1 r2: Result) : option Result :=
  match r1, r2 with
    | Lt, Lt => Some Lt
    | Eq evs1, Lt => if AtomSetImpl.is_empty evs1 then Some Lt else None
    | Lt, Eq evs2 => if AtomSetImpl.is_empty evs2 then Some Lt else None
    | Eq evs1, Eq evs2 => Some (Eq (AtomSetImpl.union evs1 evs2))
  end.


Inductive Sub2 : IsoMode -> Result -> env -> typ -> typ -> Prop :=
  | Sa2_nat: forall E im,
      Sub2 im (Eq emp) E typ_nat typ_nat
  | Sa2_top_eq: forall E im,
      Sub2 im (Eq emp) E typ_top typ_top  
  | Sa2_top_lt: forall E im A,
      A <> typ_top ->
      Sub2 im Lt E A typ_top
  | Sa2_fvar_pos: forall E X im,
      binds X (bind_sub im) E ->
      Sub2 im (Eq emp) E (typ_fvar X) (typ_fvar X)
  | Sa2_fvar_neg: forall E X im,
      binds X (bind_sub (flip_im im)) E ->
      Sub2 im (Eq (singleton X)) E (typ_fvar X) (typ_fvar X)
  | Sa2_arrow: forall E A1 A2 B1 B2 res1 res2 cm im,
      Sub2 (flip_im im) res1 E B1 A1 ->
      Sub2 im res2 E A2 B2 ->
      compose_res res1 res2 = Some cm ->
      Sub2 im cm  E (typ_arrow A1 A2) (typ_arrow B1 B2)
  | Sa2_rec_lt: forall L A1 A2 E im,
      (forall X,  X \notin L -> 
          Sub2 im Lt (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
      Sub2 im Lt E (typ_mu A1) (typ_mu A2)
  | Sa2_rec_eq_notin: forall L A1 A2 evs E im,
      (forall X,  X \notin L -> 
          Sub2 im (Eq evs) (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
      Sub2 im (Eq evs) E (typ_mu A1) (typ_mu A2)
  | Sa2_rec_eq_in: forall L A1 A2 evs E im,
      (forall X,  X \notin L -> 
          Sub2 im (Eq (add X evs)) (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
      Sub2 im (Eq (evs `union` fv_tt A1)) E (typ_mu A1) (typ_mu A2)
  | Sa2_evs_proper: forall im evs evs' E A1 A2,
      Sub2 im  (Eq evs) E A1 A2 ->
      evs [=] evs' ->
      Sub2 im  (Eq evs') E A1 A2
  .

#[global]
Hint Constructors Sub2 : core.

Lemma WFS_im_inv_simpl: forall (E2 : list (atom * binding)) (X : atom) 
(im1 im2 : IsoMode) (A : typ),
  WFS ( X ~ bind_sub im1 ++ E2) A ->
  WFS ( X ~ bind_sub im2 ++ E2) A.
Proof with auto.
  intros.
  rewrite_alist (nil ++ X ~ bind_sub im2 ++ E2).
  apply WFS_im_inv with (im1:=im1)...
Qed.

Lemma sub2_sub : forall im r E A B,
    wf_env E /\ WFS E A /\ WFS E B ->
    Sub2 im r E A B ->
    match r with
    | Lt => Sub im Rules.Lt emp E A B
    | Eq evs => Sub im Rules.Eq evs E A B
    end.
Proof with auto.
  intros im r E A B (Hwfe & Hwfa & Hwfb) H.
  induction H; intros; simpl...
  - 
    inversion Hwfa; inversion Hwfb;subst.
    destruct res1 as [|ev1], res2 as [|ev2]; simpl in *.
    + inversion H1;subst.
      apply Sa_evs_proper with (evs:=emp \u emp)... 2:{ fsetdec. }
      apply Sa_arrow with (cm1:=Rules.Lt) (cm2:=Rules.Lt)...
    + destruct (AtomSetImpl.is_empty ev2) eqn:Heq;
      inversion H1;subst.
      assert (Sub im Rules.Lt (emp \u ev2) E (typ_arrow A1 A2) (typ_arrow B1 B2)).
      { apply Sa_arrow with (cm1:=Rules.Lt) (cm2:=Rules.Eq)...
        simpl. rewrite Heq...
      }
      pose proof sub_lt_then_emp _ _ _ _ _ _ H2 eq_refl.
      apply Sa_evs_proper with (evs:=emp \u ev2)...
    + destruct (AtomSetImpl.is_empty ev1) eqn:Heq;
      inversion H1;subst.
      assert (Sub im Rules.Lt (ev1 \u emp) E (typ_arrow A1 A2) (typ_arrow B1 B2)).
      { apply Sa_arrow with (cm1:=Rules.Eq) (cm2:=Rules.Lt)...
        simpl. rewrite Heq...
      }
      pose proof sub_lt_then_emp _ _ _ _ _ _ H2 eq_refl.
      apply Sa_evs_proper with (evs:=ev1 \u emp)...
    + inversion H1;subst.
      apply Sa_arrow with (cm1:=Rules.Eq) (cm2:=Rules.Eq)...
  - 
    inversion Hwfa;subst. inversion Hwfb;subst.
    apply Sa_rec_lt with (L:=L \u dom E \u L0 \u L1)...
    intros. apply H0...
    + specialize_x_and_L X L0. apply WFS_im_inv_simpl with (im1:=im0)...
    + specialize_x_and_L X L1. apply WFS_im_inv_simpl with (im1:=im1)...
  - 
    inversion Hwfa;subst. inversion Hwfb;subst.
    apply Sa_rec_eq_notin with (L:=L \u dom E \u L0 \u L1)...
    intros. apply H0...
    + specialize_x_and_L X L0. apply WFS_im_inv_simpl with (im1:=im0)...
    + specialize_x_and_L X L1. apply WFS_im_inv_simpl with (im1:=im1)...
  - 
    inversion Hwfa;subst. inversion Hwfb;subst.
    apply Sa_rec_eq_in with (L:=L \u dom E \u L0 \u L1)...
    intros. apply H0...
    + specialize_x_and_L X L0. apply WFS_im_inv_simpl with (im1:=im0)...
    + specialize_x_and_L X L1. apply WFS_im_inv_simpl with (im1:=im1)...
  -
    apply Sa_evs_proper with (evs:=evs)...
Qed.



Lemma sub_sub2 : forall im cm evs E A B,
    Sub im cm evs E A B ->
    match cm with
    | Rules.Lt => Sub2 im Lt E A B
    | Rules.Eq => Sub2 im (Eq evs) E A B
    end.
Proof with auto.
  intros im cm evs E A B H.
  induction H; simpl...
  - destruct cm1, cm2; simpl in *. 
    + inversion H1;subst.
      apply Sa2_arrow with (res1:=Lt) (res2:=Lt)...
    + 
      destruct (AtomSetImpl.is_empty evs2) eqn:Heq;
      inversion H1;subst.
      apply Sa2_arrow with (res1:=Lt) (res2:=(Eq evs2))...
      simpl. rewrite Heq...
    +
      destruct (AtomSetImpl.is_empty evs1) eqn:Heq;
      inversion H1;subst.
      apply Sa2_arrow with (res1:=(Eq evs1)) (res2:=Lt)...
      simpl. rewrite Heq...
    +
      inversion H1;subst.
      apply Sa2_arrow with (res1:=(Eq evs1)) (res2:=(Eq evs2))...
  -
    apply Sa2_rec_lt with (L:=L \u dom E)...
  -
    apply Sa2_rec_eq_notin with (L:=L \u dom E)...
  -
    apply Sa2_rec_eq_in with (L:=L \u dom E)...
  -
    destruct cm...
    apply Sa2_evs_proper with (evs:=evs)...
Qed.