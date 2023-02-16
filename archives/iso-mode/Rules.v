Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export String.

Inductive typ : Set :=
| typ_top   : typ
| typ_nat   : typ
| typ_bvar  : nat -> typ
| typ_fvar  : var -> typ
| typ_mu :    typ -> typ
| typ_arrow : typ -> typ -> typ
| typ_rcd : var -> typ -> typ.


Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_top         => typ_top
  | typ_bvar J      => if K === J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_mu T        => typ_mu (open_tt_rec (S K) U T)
  | typ_rcd l T => typ_rcd l (open_tt_rec K U T)
  end.

(* T type U name *)
Definition open_tt T U := open_tt_rec 0 U T.

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_nat :
      type typ_nat
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2)
  | type_rcd : forall l T,
      type T ->
      type (typ_rcd l T)
  | type_mu : forall L T,
      (forall X, X \notin L -> type (open_tt T (typ_fvar X))) ->
      type (typ_mu T).

Global Hint Constructors type : core.


Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_mu T => typ_mu (subst_tt Z U T)
  | typ_rcd l T => typ_rcd l (subst_tt Z U T)
  end.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_mu T => (fv_tt T)
  | typ_rcd l T => fv_tt T
  end.

Fixpoint fl_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fl_tt T1) `union` (fl_tt T2)
  | typ_mu T => (fl_tt T)
  | typ_rcd X T => {{ X }} `union` fl_tt T
  end.

Inductive binding : Set :=
  | bind_sub : binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).
Notation empty := (@nil (atom * binding)).


Inductive WFS : env -> typ -> Prop :=
| WFS_top : forall E, WFS E typ_top
| WFS_nat : forall E, WFS E typ_nat
| WFS_fvar : forall X E,
    binds X bind_sub E ->
    WFS E (typ_fvar X)
| WFS_arrow : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_arrow A B)
| WFS_rcd : forall E l T,
    WFS E T ->
    WFS E (typ_rcd l T)
| WFS_rec : forall L E A,
    (forall  X, X \notin L -> 
        WFS (X ~ bind_sub ++ E) (open_tt A (typ_rcd X (open_tt A X)))) ->
      (forall  X, X \notin L -> 
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


Inductive Sub : env -> typ -> typ -> Prop :=
| S_nat: forall E,
    wf_env E ->
    Sub E typ_nat typ_nat
| S_fvar: forall E X,
    wf_env E ->
    WFS E (typ_fvar X) ->
    Sub E (typ_fvar X) (typ_fvar X)
| S_arrow: forall E A1 A2 B1 B2,
    Sub E B1 A1 ->
    Sub E A2 B2 ->
    Sub E (typ_arrow A1 A2) (typ_arrow B1 B2)
| S_rec: forall L A1 A2 E,
    (forall X,
        X \notin L -> WFS (X ~ bind_sub ++ E) (open_tt A1 X)) ->
    (forall X,
        X \notin L -> WFS (X ~ bind_sub ++ E) (open_tt A2 X)) ->
    (forall X,
        X \notin L ->
        Sub (X ~ bind_sub ++ E) (open_tt A1 (typ_rcd X (open_tt A1 X))) (open_tt A2 (typ_rcd X (open_tt A2 X)))) ->
    Sub E (typ_mu A1) (typ_mu A2)
| S_rcd : forall A B l E,
    Sub E A B ->
    Sub E (typ_rcd l A) (typ_rcd l B)             
| S_top: forall A E,
    WFS E A ->
    wf_env E ->
    Sub E A typ_top.

Inductive Mode := Neg | Pos.

Definition flip (m : Mode) : Mode :=
  match m with
  | Neg => Pos
  | Pos => Neg
  end.

Definition equiv E A B := Sub E A B /\ Sub E B A.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_nat : exp
  | exp_unfold : typ -> exp -> exp
  | exp_fold : typ -> exp -> exp
.

Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs t e1 => exp_abs t (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_nat => exp_nat
  | exp_unfold T e => exp_unfold T (open_ee_rec k f e)
  | exp_fold T e => exp_fold T (open_ee_rec k f e)                               
  end.

Notation open_ee e1 e2     := (open_ee_rec 0 e2 e1).

Fixpoint subst_ee (y:atom) (u:exp) (e:exp) {struct e} : exp :=
  match e with
  | (exp_bvar n)   => exp_bvar n
  | (exp_fvar x)   => (if x == y then u else (exp_fvar x))
  | (exp_abs T e1)    => exp_abs T (subst_ee y u e1)
  | (exp_app e1 e2) => exp_app (subst_ee y u e1) (subst_ee y u e2)
  | exp_nat => exp_nat
  | exp_unfold T e => exp_unfold T (subst_ee y u e)
  | exp_fold T e => exp_fold T (subst_ee y u e)                              
  end.

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (exp_bvar nat)   => {}
  | (exp_fvar x)   => {{x}}
  | (exp_abs T e)     => fv_exp e
  | (exp_app e1 e2) => fv_exp e1 \u fv_exp e2
  | exp_nat => {}
  | exp_unfold T e => fv_exp e
  | exp_fold T e => fv_exp e                       
  end.


Inductive expr : exp -> Prop :=
 | lc_fvar : forall (x:var),
     expr (exp_fvar x)
 | lc_abs : forall (e:exp) L T,
     (forall x, x \notin L -> expr (open_ee e (exp_fvar x)))  ->
     type T ->
     expr (exp_abs T e)
 | lc_app : forall (e1 e2:exp),
     expr e1 ->
     expr e2 ->
     expr (exp_app e1 e2)
 | lc_nat :
     expr exp_nat
 | lc_unfold: forall T e,
     type T ->
     expr e ->
     expr (exp_unfold T e)
 | lc_fold: forall T e,
     type T ->
     expr e ->
     expr (exp_fold T e)
.



Inductive typing : env -> exp -> typ -> Prop :=
| typing_nat: forall G,
    wf_env G ->
    typing G (exp_nat) (typ_nat)
| typing_var : forall (G:env) (x:var) (T:typ),
     wf_env G ->
     binds x (bind_typ T) G  ->
     typing G (exp_fvar x) T
 | typing_abs : forall (L:vars) (G:env) (T1:typ) (e:exp) (T2:typ),
     (forall x , x \notin L -> typing ((x ~ bind_typ T1) ++ G) (open_ee e x) T2)  ->
     typing G (exp_abs T1 e) (typ_arrow T1 T2)
 | typing_app : forall (G:env) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (exp_app e1 e2) T2
 | typing_fold : forall G A e ,
     typing G e  (open_tt A  (typ_mu A))    ->
     WFS G (typ_mu A) ->
     typing G (exp_fold (typ_mu A) e) (typ_mu A)
 | typing_unfold : forall G T e,
     typing G e (typ_mu T) ->
     typing G (exp_unfold (typ_mu T) e)  (open_tt T  (typ_mu T))
 | typing_sub: forall G T e S ,
     typing G e S ->
     Sub G S T ->
     typing G e T
.          

Inductive value : exp -> Prop :=
  | value_abs : forall t1 T, 
      expr (exp_abs T t1) ->
      value (exp_abs T t1)
  | value_nat:
      value exp_nat
  | value_fold: forall T e,
      type T ->
      value e ->
      value (exp_fold T e)
.

      

Inductive step : exp -> exp -> Prop :=
 | step_beta : forall (e1 e2:exp) T,
     expr (exp_abs T e1) ->
     value e2 ->
     step (exp_app  (exp_abs T e1) e2)  (open_ee e1 e2)
 | step_app1 : forall (e1 e2 e1':exp),
     expr e2 ->
     step e1 e1' ->
     step (exp_app e1 e2) (exp_app e1' e2)
 | step_app2 : forall v1 e2 e2',
     value v1 ->
     step e2 e2' ->
     step (exp_app v1 e2) (exp_app v1 e2')
 | step_fld: forall S T v,
     value v ->
     type T ->
     type S ->
     step (exp_unfold S (exp_fold T v)) v
 | step_fold: forall e e' T,
     step e e' ->
     type T ->
     step (exp_fold T e) (exp_fold T e')
 | step_unfold: forall e e' T,
     step e e' ->
     type T ->
     step (exp_unfold T e) (exp_unfold T e')
.
  

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : typ => fv_tt x) in
  let E := gather_atoms_with (fun x : exp => fv_exp x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : typ => fl_tt x) in
  constr:(A `union` B `union` C \u E  \u F \u G).


Global Hint Constructors Sub WFS   wf_env  typing value step expr : core.





(* ********************************************************************** *)
(** ** Properties of type substitution in types *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
    destruct (j === n)... destruct (i === n)...
Qed.

(** Opening a locally closed term is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  unfold open_tt in *.
  pick fresh X.
  apply open_tt_rec_type_aux with (j:=0) (V:=(typ_fvar X))...
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with auto.
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    contradict H; fsetdec.
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
  Case "typ_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "typ_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  destruct (X == Z)...
  pick fresh Y.
  apply type_mu with (L:=L \u {{Z}})...
  intros.
  rewrite subst_tt_open_tt_var...
Qed.


Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with congruence || eauto.
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...

    destruct (j===n)... destruct (i===n)...
Qed.


Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with auto.
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    auto
  ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_exp e ->
  e = subst_ee x u e.
Proof with auto.
  intros x u e; induction e; simpl; intro H; f_equal...

    destruct (a==x)...
    contradict H; fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with auto.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...

    destruct (k === n); subst...

    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with congruence || auto.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.


Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_exp e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e).
Proof with congruence || auto.
  induction e; intros u k Fr; simpl in *; f_equal...

    destruct (k === n)... simpl. destruct (x == x)...

    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_exp e ->
  open_ee e u = subst_ee x u (open_ee e x).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

Global Hint Resolve subst_tt_type  : core.

(** We also add as hints the lemmas concerning [body_e]. *)


(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the MetatheoryEnv library. *)





Definition relation (X:Type) := X -> X -> Prop.

Section Star.

  Variable A : Type.
  Variable R : relation A.

  Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

  Lemma star_one:
    forall a b, R a b -> star a b.
  Proof.
    eauto using star.
  Qed.

  Lemma star_trans:
    forall a b, star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; eauto using star.
  Qed.


  Hypothesis R_functional:
    forall a b c, R a b -> R a c -> b = c.

  Lemma star_star_inv:
    forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
  Proof.
    induction 1; intros.
    - auto.
    - inversion H1; subst.
      + right. eauto using star.
      + assert (b = b0) by (eapply R_functional; eauto). subst b0.
        apply IHstar; auto.
  Qed.

  Definition irred a : Prop := forall b, ~(R a b).

  Lemma finseq_unique:
    forall a b,
      star a b -> irred b -> forall b',
      star a b' -> irred b' ->
      b = b'.
  Proof.
    intros a b s.
    induction s; intros; eauto.
    unfold irred in H.
    destruct H0; eauto.
    assert (not (R a b)) by eauto.
    contradiction.
    destruct H1.
    unfold irred in H2.
    assert (not (R a b)) by eauto.
    contradiction.
    eapply IHs; eauto.
    assert (b = b0).
    apply R_functional with (a:=a).
    apply H.
    apply H1.
    subst.
    auto.
  Qed.

End Star.