Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export DoubleUnfolding.


Module Anchor.


Inductive typ : Set :=
| typ_top   : typ          
| typ_nat   : typ
| typ_bvar  : nat -> typ
| typ_fvar  : var -> typ
| typ_mu :    typ -> typ
| typ_arrow : typ -> typ -> typ
| typ_rcd : typ -> typ -> typ
.



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
  | typ_rcd T1 T2 => typ_rcd (open_tt_rec K U T1) (open_tt_rec K U T2)
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
  | type_rcd : forall  T1 T2,
      type T1 ->
      type T2 ->
      type (typ_rcd T1 T2)
  | type_mu : forall L T,
      (forall X, X \notin L -> type (open_tt T (typ_fvar X))) ->
      type (typ_mu T)
.

Hint Constructors type : core.

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top         
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_mu T => typ_mu (subst_tt Z U T)
  | typ_rcd T1 T2 => typ_rcd (subst_tt Z U T1) (subst_tt Z U T2)
  end.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}              
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_mu T => (fv_tt T)
  | typ_rcd T1 T2 => fv_tt T1 \u fv_tt T2                    
  end.


Inductive binding : Set :=
  | bind_sub : binding.

Definition env := list (atom * binding).
Notation empty := (@nil (atom * binding)).


Inductive WF : env -> typ -> Prop :=
| WF_top : forall E, WF E typ_top                       
| WF_nat : forall E, WF E typ_nat
| WF_fvar : forall X E,
    binds X bind_sub E ->
    WF E (typ_fvar X)
| WF_arrow : forall E A B,
    WF E A ->
    WF E B ->
    WF E (typ_arrow A B)
| WF_rcd : forall E T1 T2,
    WF E T1 ->
    WF E T2 ->
    WF E (typ_rcd T1 T2)
| WF_rec : forall L E A,
      (forall  X, X \notin L -> 
        WF (X ~ bind_sub ++ E) (open_tt A X)) ->
      WF E (typ_mu A).


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
| WFS_rcd : forall E T1 T2,
    WFS E T1 ->
    WFS E T2 ->
    WFS E (typ_rcd T1 T2)
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
.

     
Inductive Sub : env -> typ -> typ -> Prop :=
| S_nat: forall E,
    wf_env E ->
    Sub E typ_nat typ_nat
| S_fvar: forall E X,
    wf_env E ->
    WFS E (typ_fvar X) ->
    Sub E (typ_fvar X) (typ_fvar X)
| S_top : forall E A,
    wf_env E ->
    WFS E A -> 
    Sub E A typ_top      
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
| S_rcd : forall A B S T E,
    Sub E A B ->
    Sub E S T ->
    Sub E T S ->
    Sub E (typ_rcd S A) (typ_rcd T B)
.


Inductive sub : env -> typ -> typ -> Prop :=
| Sa_nat: forall E,
    wf_env E ->
    sub E typ_nat typ_nat
| Sa_fvar: forall E X,
    wf_env E ->
    WF E (typ_fvar X) ->
    sub E (typ_fvar X) (typ_fvar X)
| Sa_top : forall E A,
    wf_env E ->
    WF E A -> 
    sub E A typ_top     
| Sa_arrow: forall E A1 A2 B1 B2,
    sub E B1 A1 ->
    sub E A2 B2 ->
    sub E (typ_arrow A1 A2) (typ_arrow B1 B2)
| Sa_rec: forall L A1 A2 E,
    (forall X,
        X \notin L ->
        sub (X ~ bind_sub ++ E) (open_tt A1 X) (open_tt A2 X)) ->
    (forall X,
        X \notin L ->
        sub (X ~ bind_sub ++ E) (open_tt A1 (open_tt A1 X))  (open_tt A2 (open_tt A2 X))) ->
    sub E (typ_mu A1) (typ_mu A2)
| Sa_rcd : forall A B S T E,
    sub E A B ->
    sub E S T ->
    sub E T S ->
    sub E (typ_rcd S A) (typ_rcd T B)
.


Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...

    destruct (k === n)... simpl. destruct (X == X)...

    destruct (a == X)... contradict Fr; fsetdec.
Qed.

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
  assumption.
Qed.

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
    destruct (j === n)... destruct (i === n)...
Qed.

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...

    unfold open_tt in *.
    pick fresh X.
    apply open_tt_rec_type_aux with (j:=0) (V:=X).
    auto.
    auto.
Qed.

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with auto.
  induction T; simpl; intro H; f_equal...

    destruct (a == Z)...
    contradict H; fsetdec.
Qed.
    
Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...

    destruct (k === n); subst...

    destruct (a == X); subst... apply open_tt_rec_type...
Qed.

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

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

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  destruct (X == Z)...

    pick fresh Y and apply type_mu...
    rewrite subst_tt_open_tt_var...
Qed.




Hint Constructors  WF WFS Sub sub: core.

Lemma notin_fv_tt_open_aux : forall X U T,
    X `notin` fv_tt T ->
    X \notin fv_tt U ->
    X `notin` fv_tt (open_tt T U).
Proof with auto.
  intros.
  simpl.
  unfold open_tt.
  unfold open_tt_rec.
  generalize 0.
  induction T;simpl in *;intros...
  destruct (n0==n)...
Qed.

Lemma WF_type: forall E A,
    WF E A ->
    type A.
Proof with auto.
  intros.
  induction H...
  apply type_mu with (L:=L)...
Qed.


Lemma WF_weakening: forall E1 E2 T E,
    WF (E1 ++ E2) T ->
    WF (E1 ++ E ++ E2) T.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    apply WF_rec with (L:=L)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H0...
Qed.

Lemma subst_tt_wf: forall A B E X,
    WF E A ->
    WF E B ->
    WF E (subst_tt X A B).
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H0;intros;simpl in *...
  -
    destruct (X0==X)...
  -
    apply WF_rec with (L:=L \u {{X}} \u fv_tt A0).
    intros.
    rewrite  subst_tt_open_tt_var...
    apply H0...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
    apply WF_weakening...
    apply WF_type in H1...
Qed.


Lemma wfs_to_wf: forall E A,
    WFS E A ->
    WF E A.
Proof with auto.
  intros.
  induction H...
  apply WF_rec with (L:=L)...
Qed.

Lemma WFS_weakening: forall E1 E2 T E,
    WFS (E1 ++ E2) T ->
    WFS (E1 ++ E ++ E2) T.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    apply WFS_rec with (L:=L);intros...
    +
      rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
      apply H0...
    +
      rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
      apply H2...
Qed.

Lemma WFS_type: forall E A,
    WFS E A ->
    type A.
Proof with auto.
  intros.
  induction H...
  apply type_mu with (L:=L)...
Qed.

Lemma rcd_transform2:forall A C (X Y :atom),
    X <> Y -> type C ->
    (open_tt (subst_tt X C A) (typ_rcd Y (open_tt (subst_tt X C A) Y))) = (subst_tt X C (open_tt A (typ_rcd Y (open_tt A Y)))).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  f_equal...
  simpl...
  destruct (Y==X)...
  destruct H...
  f_equal...
  rewrite subst_tt_open_tt_var...
Qed.

Lemma subst_tt_wfs: forall A B E X,
    WFS E A ->
    WFS E B ->
    WFS E (subst_tt X A B).
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H0;intros;simpl in *...
  -
    destruct (X0==X)...
  -
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A0);intros...
    +
      rewrite rcd_transform2...
      apply H0...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      apply WFS_type in H3...
    +
      rewrite  subst_tt_open_tt_var...
      apply H2...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      apply WFS_type in H3...
Qed.

Lemma wf_to_wfs: forall E A,
    WF E A ->
    WFS E A.
Proof with auto.
  intros.
  induction H...
  apply WFS_rec with (L:=L \u fv_tt A)...
  intros.
  rewrite subst_tt_intro with (X:=X)...
  apply subst_tt_wfs...
Qed.



Lemma sub_regular : forall  E A B,
    sub E A B ->
    WF E A /\ WF E B /\ wf_env E.
Proof with auto.
  intros.
  dependent induction H;try solve [destruct_hypos;repeat split;auto]...  
  split.
  apply WF_rec with (L:=L)...
  intros.
  apply H0 in H3.
  destruct_hypos...
  split.
  apply WF_rec with (L:=L)...
  intros.
  apply H0 in H3.
  destruct_hypos...
  pick fresh X.
  specialize_x_and_L X L.
  destruct_hypos.
  inversion H4...
Qed.

Lemma Sub_regular : forall  E A B,
    Sub E A B ->
    WFS E A /\ WFS E B /\ wf_env E.
Proof with auto.
  intros.
  dependent induction H;try solve [destruct_hypos;repeat split;auto]...  
  split.
  apply WFS_rec with (L:=L);intros...
  eapply H2...
  split.
  apply WFS_rec with (L:=L);intros...
  eapply H2...
  pick fresh X.
  specialize_x_and_L X L.
  destruct_hypos.
  inversion H4...
Qed.  
  

Lemma WF_subst_rcd: forall E A,
    WF E A ->
    forall X B,
      type B ->
    WF E (subst_tt X (typ_rcd X B) A) ->
    WF E (subst_tt X B A).
Proof with auto.
  intros E A H.
  induction H;intros;simpl in *...
  -
    destruct (X==X0)...
    inversion H1...
  -
    dependent destruction H2...
  -
    dependent destruction H2...
  -
    dependent destruction H2...
    apply WF_rec with (L:=L \u L0 \u fv_tt A \u fv_tt B \u {{X}}).
    intros.
    rewrite subst_tt_open_tt_var...
    apply H0...
    rewrite <- subst_tt_open_tt_var...
    apply H2...
Qed.



Lemma open_var_distinct : forall C i j A B ,
    i <> j ->
    type A -> type B ->
  open_tt_rec i A (open_tt_rec j B C) = open_tt_rec j B (open_tt_rec i A C).
Proof with congruence || eauto.
  intros C.
  induction C;intros;simpl;try solve [f_equal;eauto]...
  -
    destruct (j==n)...
    destruct (i==n)...
    subst...
    simpl...
    destruct (n==n)...
    rewrite <- open_tt_rec_type...
    destruct (i==n)...
    simpl...
    destruct (i==n)...
    rewrite <- open_tt_rec_type...
    simpl...
    destruct (i==n)...
    destruct (j==n)...
Qed.


Lemma notin_fv_tt_open_tt_rec : forall T X U n,
    X `notin` fv_tt T ->
    X \notin fv_tt U ->
    X `notin` fv_tt (open_tt_rec n U T).
Proof with auto.
  induction T;intros;simpl in *;intros...
  destruct (n0==n)...
Qed.

Lemma subst_var_false: forall A X  E C,
    sub E (subst_tt X (typ_rcd X C) A) X -> False.
Proof with auto.
  induction A;intros;simpl in H;try solve [inversion H]...
  destruct (a==X);subst...
  inversion H...
  inversion H...
Qed.  
  
Lemma sub_subst_rcd_dismiss: forall E E1 A B X C D,
    sub (E1++[(X, bind_sub)] ++ E) (subst_tt X (typ_rcd X C) A)
        (subst_tt X (typ_rcd X D) B) ->
    type C -> type D ->
    WF (E1 ++ [(X, bind_sub)] ++ E) A ->
    WF (E1 ++ [(X, bind_sub)] ++ E) B ->
    sub (E1++[(X, bind_sub)] ++ E) A B.
Proof with auto.
  intros.
  dependent induction H...
  -
    induction A;simpl in *;try solve [inversion x|inversion x0]...
    induction B;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a==X);simpl in *;try solve [inversion x]...
    destruct (a==X);simpl in *;try solve [inversion x0]...
  -
    induction A;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a==X);simpl in *;try solve [inversion x0]...
    induction B;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a0==X);simpl in *;try solve [inversion x]...
    rewrite <- x.
    rewrite <- x0...
  -
    induction B;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a==X);simpl in *;try solve [inversion x]...
  -
    induction A;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a==X);simpl in *;try solve [inversion x0]...
    induction B;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a==X);simpl in *;try solve [inversion x]...
    clear IHA1 IHA2 IHB1 IHB2.
    inversion x;inversion x0;clear x x0.
    dependent destruction H3.
    dependent destruction H4.
    constructor...
    apply IHsub1 with (C:=D) (D:=C)...
    apply IHsub2 with (C:=C) (D:=D)...
  -
    induction A;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a==X);simpl in *;try solve [inversion x0]...
    induction B;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a==X);simpl in *;try solve [inversion x]...
    clear IHA IHB.
    inversion x;inversion x0;clear x x0.
    dependent destruction H5.
    dependent destruction H6.
    apply Sa_rec with (L:=L \u {{X}} \u L0 \u L1 \u fv_tt A \u fv_tt B \u fv_tt C \u fv_tt D);intros...
    + 
      rewrite_alist (([(X0, bind_sub)] ++ E1) ++ (X, bind_sub) :: E).
      apply H0 with (X0:=X0) (C:=C) (D:=D)...
      *
        rewrite H9.
        rewrite  subst_tt_open_tt_var...
      *
        rewrite H8.
        rewrite  subst_tt_open_tt_var...
      *
        rewrite_alist ([(X0, bind_sub)] ++ E1 ++ (X, bind_sub) :: E)...
      *
        rewrite_alist ([(X0, bind_sub)] ++ E1 ++ (X, bind_sub) :: E)...
    +
      rewrite_alist (([(X0, bind_sub)] ++ E1) ++ (X, bind_sub) :: E).
      apply H2 with (X0:=X0) (C:=C) (D:=D)...
      *
        rewrite H9.
        rewrite  subst_tt_open_tt_var...
        rewrite  <- subst_tt_open_tt...
      *
        rewrite H8.
        rewrite  subst_tt_open_tt_var...
        rewrite  <- subst_tt_open_tt...
      *
        rewrite subst_tt_intro with (X:=X0)...
        rewrite_alist ([(X0, bind_sub)] ++ E1 ++ (X, bind_sub) :: E).
        apply subst_tt_wf...
      *
        rewrite subst_tt_intro with (X:=X0)...
        rewrite_alist ([(X0, bind_sub)] ++ E1 ++ (X, bind_sub) :: E).
        apply subst_tt_wf...
  -
    induction A;simpl in *;try solve [inversion x|inversion x0]...
    destruct (a==X);simpl in *;try solve [inversion x0]...
    +
      induction B;simpl in *;try solve [inversion x|inversion x0]...
      destruct (a0==X);simpl in *;try solve [inversion x]...
      *
        subst.
        constructor...
        apply sub_regular in H0...
        destruct_hypos...
      *
        clear IHB1 IHB2.
        inversion x0;inversion x;clear x x0.
        subst.
        apply subst_var_false in H1...
        destruct H1.
    +
      induction B;simpl in *;try solve [inversion x|inversion x0]...
      destruct (a==X);simpl in *;try solve [inversion x]...
      *
        clear IHA1 IHA2.
        inversion x0;inversion x;clear x x0.
        subst.
        apply subst_var_false in H0...
        destruct H0.
      *
        clear IHA1 IHA2 IHB1 IHB2.
        inversion x0;inversion x;clear x x0.
        dependent destruction H4.
        dependent destruction H5.
        constructor...
        apply IHsub1 with (C:=C) (D:=D)...
        apply IHsub2 with (C:=C) (D:=D)...
        apply IHsub3 with (C:=D) (D:=C)...
Qed.
        
     
Lemma sub_subst_rcd: forall E A B,
    sub E A B ->
    forall X C D,
      sub E (subst_tt X (typ_rcd X C) A) (subst_tt X (typ_rcd X D) B) ->
      type C -> type D ->
      sub E (subst_tt X C A) (subst_tt X D B).
Proof with auto.
  intros E A B H.
  induction H;intros...
  -
    simpl in *.
    destruct (X==X0)...
    dependent destruction H1...
  -
    simpl in *.
    constructor...
    apply sub_regular in H1.
    destruct_hypos.
    apply WF_subst_rcd...
  -
    simpl in *...
    dependent destruction H1...
  -
    simpl in *.
    dependent destruction H3...
    apply Sa_rec with (L:=L \u L0 \u {{X}} \u fv_tt A1 \u fv_tt A2);intros.
    +
      rewrite subst_tt_open_tt_var...
      rewrite subst_tt_open_tt_var...
      apply H0...
      rewrite <- subst_tt_open_tt_var...
      rewrite <- subst_tt_open_tt_var...
      apply H3...
    +
      rewrite subst_tt_open_tt_var...
      rewrite subst_tt_open_tt_var...
      rewrite <- subst_tt_open_tt...
      rewrite <- subst_tt_open_tt...
      apply H2...
      rewrite  subst_tt_open_tt...
      rewrite <- subst_tt_open_tt_var...
      rewrite  subst_tt_open_tt...
      rewrite <- subst_tt_open_tt_var...
      apply H4...
  -
    simpl in *...
    dependent destruction H2...
Qed.



Lemma rcd_transform: forall A B (X Y :atom),
    X <> Y -> type B -> type (open_tt A Y) ->
    subst_tt X (typ_rcd X B) (open_tt A (typ_rcd Y (open_tt A Y))) =
  open_tt (subst_tt X (typ_rcd X B) A) (typ_rcd Y (open_tt (subst_tt X (typ_rcd X B) A) Y)).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  f_equal...
  simpl...
  destruct (Y==X)... destruct H...
  f_equal...
  rewrite subst_tt_open_tt...
  f_equal...
  rewrite <- subst_tt_fresh...
Qed.

Lemma Sub_subst_rcd: forall E A B,
    Sub E A B ->
    forall X C D,
      Sub E (subst_tt X C A) (subst_tt X D B) ->
      WFS E C -> WFS E D -> WFS E X ->
      Sub E (subst_tt X (typ_rcd X C) A) (subst_tt X (typ_rcd X D) B).
Proof with auto.
  intros E A B H.
  induction H;intros...
  -
    simpl in *.
    destruct (X==X0);subst...
  -
    simpl in *.
    constructor...
    apply subst_tt_wfs...
  -
    simpl in *...
    dependent destruction H1...
  -
    simpl in *.
    dependent destruction H3...
    apply S_rec with (L:=L \u L0 \u {{X}} \u fv_tt A1 \u fv_tt A2);intros.
    +
      rewrite subst_tt_open_tt_var...
      apply subst_tt_wfs...
      constructor.
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      apply H...
      constructor...
      apply WFS_type in H6...
    +
      rewrite subst_tt_open_tt_var...
      apply subst_tt_wfs...
      constructor.
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      apply H0...
      constructor...
      apply WFS_type in H7...
    +
      assert (type C) by (apply WFS_type in H6;auto)...
      assert (type D) by (apply WFS_type in H7;auto)...
      rewrite <- rcd_transform...
      rewrite <- rcd_transform...
      apply H2...
      rewrite <- rcd_transform2...
      rewrite <- rcd_transform2...
      apply H5...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
      apply WFS_weakening...
      specialize_x_and_L X0 L.
      apply WFS_type in H0...
      specialize_x_and_L X0 L.
      apply WFS_type in H...
  -
    simpl in *...
    dependent destruction H2...
Qed.

Lemma sub_to_Sub: forall E A B,
    sub E A B ->
    Sub E A B.
Proof with auto.
  intros.
  induction H;try solve [constructor;auto;apply wf_to_wfs;auto]...
  apply S_rec with (L:=L \u fv_tt A1 \u fv_tt A2);intros...
  -
    specialize_x_and_L X L.
    apply Sub_regular in H0.
    destruct_hypos...
  -
    specialize_x_and_L X L.
    apply Sub_regular in H0.
    destruct_hypos...
  -
    rewrite subst_tt_intro with (X:=X)...
    remember (subst_tt X (typ_rcd X (open_tt A1 X)) (open_tt A1 X)).
    rewrite subst_tt_intro with (X:=X)...
    subst.
    apply Sub_subst_rcd...
    rewrite <- subst_tt_intro...
    rewrite <- subst_tt_intro...
    specialize_x_and_L X L.
    apply Sub_regular in H0.
    destruct_hypos...
    specialize_x_and_L X L.
    apply Sub_regular in H0.
    destruct_hypos...
Qed.  

          
Lemma open_twice_to_once: forall E1 E2 X A1 A2,
     sub (E1 ++ [(X, bind_sub)] ++ E2) (open_tt A1 (typ_rcd X (open_tt A1 X)))
         (open_tt A2 (typ_rcd X (open_tt A2 X))) ->
     X \notin fv_tt A1 \u fv_tt A2 ->
     WF (E1 ++ [(X, bind_sub)] ++ E2) (open_tt A1 X) ->
     WF (E1 ++ [(X, bind_sub)] ++ E2) (open_tt A2 X) ->
     sub (E1 ++ [(X, bind_sub)] ++ E2) (open_tt A1 X) (open_tt A2 X).
Proof with auto.
  intros.
  rewrite subst_tt_intro with (X:=X) in H...
  remember (subst_tt X (typ_rcd X (open_tt A1 X)) (open_tt A1 X)).
  rewrite subst_tt_intro with (X:=X) in H...
  subst.
  apply sub_subst_rcd_dismiss in H...
  apply WF_type in H1...
  apply WF_type in H2...
Qed.
        

Lemma Sub_to_sub: forall E A B,
    Sub E A B ->
    sub E A B.
Proof with auto.
  intros.
  induction H;try solve [constructor;auto;apply wfs_to_wf;auto]...
  apply Sa_rec with (L:=L \u fv_tt A1 \u fv_tt A2);intros...
  -
    specialize_x_and_L X L.
    rewrite_alist (nil ++ [(X, bind_sub)] ++ E) in H2.
    apply open_twice_to_once in H2...
    apply wfs_to_wf in H...
    apply wfs_to_wf in H0...
  -
    assert (Hq:=H2).
    specialize_x_and_L X L.
    rewrite_alist (nil ++ [(X, bind_sub)] ++ E) in H2.
    apply open_twice_to_once in H2...
    apply sub_subst_rcd with (X:=X) (C:=open_tt A1 X) (D:=open_tt A2 X) in H2...
    rewrite <- subst_tt_intro in H2...
    rewrite <- subst_tt_intro in H2...
    rewrite <- subst_tt_intro...
    rewrite <- subst_tt_intro...
    apply WFS_type in H...
    apply WFS_type in H0...
    apply wfs_to_wf in H...
    apply wfs_to_wf in H0...
Qed.

End Anchor.




(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)
(* ========================================================== *)


Fixpoint upcast (A:typ) : Anchor.typ :=
  match A with
  | typ_nat => Anchor.typ_nat
  | typ_top => Anchor.typ_top
  | typ_fvar x => Anchor.typ_fvar x
  | typ_bvar b => Anchor.typ_bvar b
  | typ_arrow s t => Anchor.typ_arrow (upcast s) (upcast t)
  | typ_mu s => Anchor.typ_mu (upcast s)
  end.

Fixpoint upcast_env (E:env) : Anchor.env :=
  match E with
  | nil => nil
  | (x,bind_sub)::E' => (x,Anchor.bind_sub)::(upcast_env E')
  | (x,bind_typ _)::E' => (x,Anchor.bind_sub)::(upcast_env E')
  end.


Lemma notin_dom_upcast: forall E a,
     a `notin` dom E ->
     a `notin` dom (upcast_env E).
Proof with auto.
  induction E;intros...
  destruct a.
  simpl in *.
  destruct b...
Qed.

Lemma In_upcast:forall E X,
  In (X, bind_sub) E ->
     In (X, Anchor.bind_sub) (upcast_env E).
Proof with auto.
  induction E;intros...
  destruct a...
  simpl in *...
  destruct H...
  inversion H.
  apply in_eq...
  destruct b...
  apply in_cons...
  apply in_cons...
Qed.  


Lemma upcast_open : forall A B,
    upcast (open_tt A B) = Anchor.open_tt (upcast A) (upcast B).
Proof with auto.
  intros.
  unfold open_tt.
  unfold Anchor.open_tt.
  generalize 0.
  generalize dependent B.
  induction A;intros;simpl;try solve [f_equal;auto]...
  -
    destruct (n0==n);simpl...
Qed.

Lemma upcast_open_var : forall A (X:atom),
    upcast (open_tt A X) = Anchor.open_tt (upcast A) (Anchor.typ_fvar X).
Proof with auto.
  intros.
  rewrite upcast_open...
Qed.

Lemma WF_upcast : forall E A,
    WF E A -> Anchor.WF (upcast_env E) (upcast A).
Proof with auto.
  intros.
  induction H;simpl in *...
  -
    constructor...
    unfold binds in *.
    apply In_upcast...
  -
    apply Anchor.WF_rec with (L:=L \u Anchor.fv_tt (upcast A));intros...
    specialize_x_and_L X L.
    rewrite upcast_open in H0...
Qed.

Lemma wf_env_upcast : forall E,
    wf_env E -> Anchor.wf_env (upcast_env E).
Proof with auto using notin_dom_upcast.
  intros.
  induction E;simpl...
  constructor...
  destruct a.
  dependent destruction H.
  constructor...
  constructor...
Qed.  

Lemma double_unfolding_upcast : forall E A B,
    sub E A B -> Anchor.sub (upcast_env E) (upcast A) (upcast B).
Proof with auto using wf_env_upcast, WF_upcast.
  intros.
  induction H;simpl...
  -
    constructor...
    constructor...
    unfold binds in *.
    apply In_upcast...
  -
    apply Anchor.Sa_rec with (L:=L \u Anchor.fv_tt (upcast A1) \u Anchor.fv_tt (upcast A2));intros...
    +
      rewrite <- upcast_open_var...
      rewrite <- upcast_open_var...
      apply H0...
    +
      rewrite <- upcast_open_var...
      rewrite <- upcast_open_var...
      rewrite <- upcast_open...
      rewrite <- upcast_open...
      apply H2...
Qed.      
      
Lemma double_unfolding_to_Anchor_unfolding : forall E A B,
    sub E A B -> Anchor.Sub (upcast_env E) (upcast A) (upcast B).
Proof with auto.
  intros.
  apply double_unfolding_upcast in H.
  apply Anchor.sub_to_Sub...
Qed.



Fixpoint erase (A:Anchor.typ) : typ :=
  match A with
  | Anchor.typ_nat => typ_nat
  | Anchor.typ_top => typ_top
  | Anchor.typ_fvar x => typ_fvar x
  | Anchor.typ_bvar b => typ_bvar b
  | Anchor.typ_arrow s t => typ_arrow (erase s) (erase t)
  | Anchor.typ_mu s => typ_mu (erase s)
  | Anchor.typ_rcd l t => erase t
  end.

Fixpoint erase_env (E:Anchor.env) : env :=
  match E with
  | nil => nil
  | (x,Anchor.bind_sub)::E' => (x,bind_sub)::(erase_env E')
  end.


Lemma notin_dom_downcast: forall E a,
     a `notin` dom E ->
     a `notin` dom (erase_env E).
Proof with auto.
  induction E;intros...
  destruct a.
  simpl in *.
  destruct b...
Qed.

Lemma In_downcast:forall E X,
  In (X, Anchor.bind_sub) E ->
     In (X, bind_sub) (erase_env E).
Proof with auto.
  induction E;intros...
  destruct a...
  simpl in *...
  destruct H...
  inversion H.
  apply in_eq...
  destruct b...
  apply in_cons...
Qed.  


Lemma downcast_open : forall A B,
    erase (Anchor.open_tt A B) = open_tt (erase A) (erase B).
Proof with auto.
  intros.
  unfold open_tt.
  unfold Anchor.open_tt.
  generalize 0.
  generalize dependent B.
  induction A;intros;simpl;try solve [f_equal;auto]...
  -
    destruct (n0==n);simpl...
Qed.

Lemma downcast_open_var : forall A (X:atom),
    erase (Anchor.open_tt A (Anchor.typ_fvar X)) = open_tt (erase A)  X.
Proof with auto.
  intros.
  rewrite downcast_open...
Qed.

Lemma WF_downcast : forall E A,
    Anchor.WF E A -> WF (erase_env E) (erase A).
Proof with auto.
  intros.
  induction H;simpl in *...
  -
    constructor...
    unfold binds in *.
    apply In_downcast...
  -
    apply WF_rec with (L:=L \u fv_tt (erase A));intros...
    specialize_x_and_L X L.
    rewrite downcast_open in H0...
    specialize_x_and_L X L.
    rewrite downcast_open in H0...
    rewrite subst_tt_intro with (X:=X)...
    apply subst_tt_wf...
Qed.

Lemma wf_env_downcast : forall E,
    Anchor.wf_env E -> wf_env (erase_env E).
Proof with auto using notin_dom_downcast.
  intros.
  induction E;simpl...
  destruct a.
  dependent destruction H.
  constructor...
Qed.  


Lemma double_unfolding_downcast : forall E A B,
    Anchor.sub E A B -> sub (erase_env E) (erase A) (erase B).
Proof with auto using wf_env_downcast, WF_downcast.
  intros.
  induction H;simpl...
  -
    constructor...
    dependent destruction H0.
    unfold binds in *.
    apply In_downcast...
  -
    apply sa_rec with (L:=L \u fv_tt (erase A1) \u fv_tt (erase A2));intros...
    +
      rewrite <- downcast_open_var...
      rewrite <- downcast_open_var...
      apply H0...
    +
      rewrite <- downcast_open_var...
      rewrite <- downcast_open_var...
      rewrite <- downcast_open...
      rewrite <- downcast_open...
      apply H2...
Qed.      

Lemma Anchor_unfolding_to_double_unfolding: forall E A B,
    Anchor.Sub E A B -> sub (erase_env E) (erase A) (erase B).
Proof with auto.
  intros.
  apply double_unfolding_downcast...
  apply Anchor.Sub_to_sub...
Qed.

