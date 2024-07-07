Require Import Metalib.Metatheory.
Require Import Program.Equality.

Require Coq.Lists.List.

Inductive typ : Set :=
| typ_top   : typ
| typ_nat   : typ
| typ_bvar  : nat -> typ
| typ_fvar  : var -> typ
| typ_mu    : typ -> typ
| typ_arrow : typ -> typ -> typ
| typ_rcd   : list (var * typ) -> typ
.


Fixpoint size_typ (t : typ) : nat :=
  match t with
  | typ_top => 1
  | typ_nat => 1
  | typ_bvar _ => 1
  | typ_fvar _ => 1
  | typ_mu t => 1 + size_typ t
  | typ_arrow t1 t2 => 1 + size_typ t1 + size_typ t2
  | typ_rcd l => 1 + List.fold_right (fun x acc => acc + size_typ (snd x)) 0 l
  end.


(* Theorem Forall_impl_In :
forall (A : Type) (P Q : A -> Prop) (l : list A),
  Forall P l ->
  (forall x : A, In x l -> P x -> Q x) ->
  Forall Q l.
Proof.
  intros.
  induction l...
  { constructor... }
  { inversion H;subst. constructor.
    + apply H0;auto. left;auto.
    + apply IHl;auto. intros. apply H0;auto. right;auto. }
Qed. *)

(* Fixpoint size_typ (t : typ) : nat :=
  match t with
  | typ_top => 1
  | typ_nat => 1
  | typ_bvar _ => 1
  | typ_fvar _ => 1
  | typ_mu t => 1 + size_typ t
  | typ_arrow t1 t2 => 1 + size_typ t1 + size_typ t2
  | typ_rcd l => 1 + size_typ_list l
  end
with size_typ_list (l : typ_list) : nat :=
  match l with
  | typ_nil => 0
  | typ_cons l t l' => size_typ t + size_typ_list l'
  end.

Fixpoint typ_to_list (ts: typ_list) : list (atom * typ) :=
  match ts with
  | typ_nil => nil
  | typ_cons l t ts' => (l,t) :: typ_to_list ts'
  end.

Fixpoint list_to_typ (ls: list (atom * typ)) : typ_list :=
  match ls with
  | nil => typ_nil
  | (l,t) :: ls' => typ_cons l t (list_to_typ ls')
  end.

Scheme typ_typ_list_rec := Induction for typ Sort Set
with list_typ_rec := Induction for typ_list Sort Set. *)




Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : list (atom * T)) : Prop :=
    match ls with
      | nil => True
      | cons h t => P (snd h) /\ All t
    end.

End All.


Section typ_ind'.

Variable P : typ -> Prop.

Theorem binds_transfrom: forall ls,
  (All typ P ls) ->
  (forall l t, binds l t ls -> P t).
Proof.
  intros.
  induction ls.
  - inversion H0.
  - destruct H. inversion H0;subst.
    + apply H.
    + apply IHls;auto.
Qed.

Hypothesis 
  (H1: P typ_top)
  (H2: P typ_nat)
  (H3: forall n, P (typ_bvar n))
  (H4: forall x, P (typ_fvar x))
  (H5: forall t, P t -> P (typ_mu t))
  (H6: forall t1 t2, P t1 -> P t2 -> P (typ_arrow t1 t2)).

Hypothesis
  (H7: forall ls, 
    (forall l t, binds l t ls -> P t) -> P (typ_rcd ls)).


Fixpoint typ_ind' (t: typ) : P t :=
  match t with
  | typ_top => H1
  | typ_nat => H2
  | typ_bvar n => H3 n
  | typ_fvar x => H4 x
  | typ_mu t => H5 t (typ_ind' t)
  | typ_arrow t1 t2 => H6 t1 t2 (typ_ind' t1) (typ_ind' t2)
  | typ_rcd ls => H7 ls (binds_transfrom ls ((
      fix typ_list_ind (ls': list (atom * typ)) : All typ P ls' :=
        match ls' return All typ P ls' with
        | nil => I
        | cons t ts => conj (typ_ind' (snd t)) (typ_list_ind ts)
        end
  ) ls))
  end.

End typ_ind'.


Section typ_rec'.

Variable P : typ -> Set.



Hypothesis 
  (H1: P typ_top)
  (H2: P typ_nat)
  (H3: forall n, P (typ_bvar n))
  (H4: forall x, P (typ_fvar x))
  (H5: forall t, P t -> P (typ_mu t))
  (H6: forall t1 t2, P t1 -> P t2 -> P (typ_arrow t1 t2)).

Hypothesis
  (H7: P (typ_rcd nil))
  (H8: forall l t ls, P t -> P (typ_rcd ls) -> P (typ_rcd (cons (l, t) ls))).


Fixpoint typ_rec' (t: typ) : P t :=
  match t with
  | typ_top => H1
  | typ_nat => H2
  | typ_bvar n => H3 n
  | typ_fvar x => H4 x
  | typ_mu t => H5 t (typ_rec' t)
  | typ_arrow t1 t2 => H6 t1 t2 (typ_rec' t1) (typ_rec' t2)
  | typ_rcd ls => ((
      fix typ_list_ind (ls': list (atom * typ)) : P (typ_rcd ls') :=
        match ls' return P (typ_rcd ls') with
        | nil => H7
        | cons (l, t) ts => H8 l t ts (typ_rec' t) (typ_list_ind ts)
        end
  ) ls)
  end.

End typ_rec'.

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.



(* ********************************************************************** *)
(** * Opening *)

(** Opening up abstractions and locally closed types *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_top         => typ_top
  | typ_bvar J      => if K === J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_mu T        => typ_mu (open_tt_rec (S K) U T)
  | typ_rcd l       => typ_rcd (map (open_tt_rec K U) l)
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
  | type_mu : forall L T,
      (forall X, X \notin L -> type (open_tt T (typ_fvar X))) ->
      type (typ_mu T)
  | type_rcd: forall l (Huniq: uniq l),
      (forall i T, binds i T l -> type T) ->
      type (typ_rcd l)
.


#[global] Hint Constructors type : core.


Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_mu T => typ_mu (subst_tt Z U T) 
  | typ_rcd l => typ_rcd (map (subst_tt Z U) l)
  end.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_mu T => (fv_tt T)
  | typ_rcd l => List.fold_right union {} (List.map (fun x => fv_tt (snd x)) l)
  end.



Inductive IsoMode := Neg | Pos.

Inductive CmpMode := Lt | Eq.


Inductive binding : Set :=
  | bind_sub : IsoMode -> binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).
Definition emp := Metatheory.empty.
Notation empty := (@nil (atom * binding)).

Fixpoint Tlookup (i':var) (Tr: list (atom * typ)) : option typ :=
  match Tr with
  |  (i, T) :: Tr' =>
      if i == i' then Some T else Tlookup i' Tr'
  | _ => None
  end.


(* Fixpoint Tlookup (i':var) (Tr: list (atom * typ)) : option typ :=
  match Tr with
  | (i, T1) :: T2 =>
      if i == i' then Some T1 else Tlookup i' T2
  | _ => None
  end. *)

(* Fixpoint collectLabel (T : list (atom * typ)) : atoms :=
  match T with
  | (i, T1) :: T2 => {{i}} \u collectLabel T2
  | _ => {}
  end. *)

Fixpoint collectLabel (T : list (atom * typ)) : atoms :=
  match T with
  | (i, T1):: T2 => {{i}} \u collectLabel T2
  | _ => {}
  end.


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
      WFS E (typ_mu A)
| WFS_rcd : forall E T,
    uniq T ->
    (forall i T', binds i T' T -> WFS E T') ->
    WFS E (typ_rcd T)
.


Fixpoint fl_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fl_tt T1) `union` (fl_tt T2)
  | typ_mu T => (fl_tt T)
  | typ_rcd l => List.fold_right union {} (List.map (fun x => fl_tt (snd x)) l)
  end.


Fixpoint fl_env (E:env) : atoms :=
match E with
| nil => {}
| (x,bind_sub y)::E' =>  (fl_env E')
| (x,bind_typ y)::E' => (fl_tt y) \u (fl_env E')
end.

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

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_nat : exp
  | exp_unfold : typ -> exp -> exp
  | exp_fold : typ -> exp -> exp
  | exp_rcd : list (atom * exp) -> exp
  | exp_rcd_proj : exp -> atom -> exp
.


Section exp_rec'.

Variable P : exp -> Set.



Hypothesis 
  (H1: forall n, P (exp_bvar n))
  (H2: forall x, P (exp_fvar x))
  (H3: forall T e, P e -> P (exp_abs T e))
  (H4: forall e1 e2, P e1 -> P e2 -> P (exp_app e1 e2))
  (H5: P exp_nat)
  (H6: forall T e, P e -> P (exp_unfold T e))
  (H7: forall T e, P e -> P (exp_fold T e))
  (H8: P (exp_rcd nil))
  (H9: forall l e ls, P e -> P (exp_rcd ls) -> P (exp_rcd (cons (l, e) ls)))
  (H10: forall e l, P e -> P (exp_rcd_proj e l)).

Fixpoint exp_rec' (e: exp) : P e :=
  match e with
  | exp_bvar n => H1 n
  | exp_fvar x => H2 x
  | exp_abs T e => H3 T e (exp_rec' e)
  | exp_app e1 e2 => H4 e1 e2 (exp_rec' e1) (exp_rec' e2)
  | exp_nat => H5
  | exp_unfold T e => H6 T e (exp_rec' e)
  | exp_fold T e => H7 T e (exp_rec' e)
  | exp_rcd ls => ((
      fix exp_list_ind (ls' : list (atom * exp)) : P (exp_rcd ls') :=
        match ls' return P (exp_rcd ls') with
        | nil => H8
        | cons (l, e) ls => H9 l e ls (exp_rec' e) (exp_list_ind ls)
        end
  ) ls)
  | exp_rcd_proj e l => H10 e l (exp_rec' e)
  end.

End exp_rec'.

Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


Fixpoint collectLabele (e: list (atom * exp)) : atoms :=
  match e with
  | (i, e1) :: e2 => {{i}} \u collectLabele e2
  | _ => {}
  end.



Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs t e1 => exp_abs t (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_nat => exp_nat
  | exp_unfold T e => exp_unfold T (open_ee_rec k f e)
  | exp_fold T e => exp_fold T (open_ee_rec k f e)
  | exp_rcd l => exp_rcd (map (open_ee_rec k f) l) 
  | exp_rcd_proj e l => exp_rcd_proj (open_ee_rec k f e) l
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
  | exp_rcd l => exp_rcd (map (subst_ee y u) l)
  | exp_rcd_proj e l => exp_rcd_proj (subst_ee y u e) l
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
  | exp_rcd l => List.fold_right union {} (List.map (fun x => fv_exp (snd x)) l)
  | exp_rcd_proj e1 i => fv_exp e1
  end.



Fixpoint tlookup (i':var) (Er:list (atom * exp)) : option exp :=
  match Er with
  | (i, T) :: Er' => if i == i' then Some T else tlookup i' Er'
  | _ => None
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
  | lc_rcd: forall l,
      (forall lb x, binds lb x l -> expr x) ->
      expr (exp_rcd l)
  | lc_rcd_proj: forall e l,
      expr e ->
      expr (exp_rcd_proj e l) 
.

Definition body_e (e : exp) :=
    exists L, forall x : atom, x `notin` L -> expr (open_ee e x).
  

(* Notation "l1 ++ l2" := (tys_app l1 l2) (at level 60, right associativity) : typ_list_scope.

Delimit Scope typ_list_scope with typ_list.

Notation " X ~ T " := (typ_cons X T typ_nil )%typ_list (at level 50) : typ_list_scope. *)


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
| Sa_rcd_eq: forall E im, 
    wf_env E ->
    Sub im Eq emp E (typ_rcd nil) (typ_rcd nil)
| Sa_rcd_lt: forall E tys im,
    tys <> nil ->
    uniq tys ->
    wf_env E ->
    (forall l T, binds l T tys -> WFS E T) ->
    Sub im Lt emp E (typ_rcd tys) (typ_rcd nil)
| Sa_rcd_cons: forall E l tys1 tys1' tys2 tys2' (T1 T2:typ) im cm1 cm2 cm evs1 evs2
    (Hl1: l `notin` dom (tys1 ++ tys1'))
    (Hl2: l `notin` dom (tys2 ++ tys2')),
    Sub im cm1 evs1 E T1 T2 ->
    Sub im cm2 evs2 E (typ_rcd (tys1 ++ tys1')) (typ_rcd (tys2 ++ tys2')) ->
    compose_cm cm1 cm2 evs1 evs2 = Some cm ->
    Sub im cm (evs1 `union` evs2) E 
      (typ_rcd (tys1 ++ l ~ T1 ++ tys1'))
      (typ_rcd (tys2 ++ l ~ T2 ++ tys2'))
| Sa_evs_proper: forall im cm evs evs' E A1 A2,
    Sub im cm evs E A1 A2 ->
    evs [=] evs' ->
    Sub im cm evs' E A1 A2
.

#[global] Hint Constructors Sub wf_env WFS : core.

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
 | typing_proj : forall G e T i Ti,
     typing G e (typ_rcd T) ->
     Tlookup i T = Some Ti ->
     typing G (exp_rcd_proj e i) Ti
 | typing_rcd_cons: forall G es tys,
     wf_env G -> uniq es -> uniq tys ->
     (* (forall i ei, binds i ei es -> exists Ti, binds i Ti tys) -> *)
     dom es [=] dom tys ->
     (forall i ei Ti, binds i Ti tys -> binds i ei es -> typing G ei Ti) ->
     typing G (exp_rcd es) (typ_rcd tys)
 | typing_sub: forall G T e S evs cm,
     typing G e S ->
     Sub Pos cm evs G S T ->
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
  | value_rcd: forall l,
      (forall lb x, binds lb x l -> value x) ->
      value (exp_rcd l).

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
 | step_projrcd: forall e i vi ,
     value (exp_rcd e) ->
     tlookup i e = Some vi->
     step (exp_rcd_proj (exp_rcd e) i) vi
 | step_proj: forall e1 e2 i,
     step e1 e2 ->
     step (exp_rcd_proj e1 i) (exp_rcd_proj e2 i)
 | step_rcd_head: forall es1 es2 e1 e2 l,
     Forall (fun x => value (snd x)) es1 ->
     step e1 e2 ->
     step (exp_rcd (es1 ++ l ~ e1  ++ es2)) (exp_rcd (es1 ++ l ~ e2 ++ es2))
.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union`  E \u C \u D \u F).

#[global] Hint Constructors Sub WFS typing step value expr wf_env: core.