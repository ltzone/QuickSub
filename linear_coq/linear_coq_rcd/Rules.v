Require Import Metalib.Metatheory.
Require Import Program.Equality.

Inductive typ : Set :=
| typ_top   : typ
| typ_nat   : typ
| typ_bvar  : nat -> typ
| typ_fvar  : var -> typ
| typ_mu :    typ -> typ
| typ_arrow : typ -> typ -> typ
| typ_rcd_nil : typ
| typ_rcd_cons : var -> typ -> typ -> typ  
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
  | typ_rcd_nil     => typ_rcd_nil
  | typ_rcd_cons i T1 T2  => typ_rcd_cons i (open_tt_rec K U T1) (open_tt_rec K U T2)                          
  end.

(* T type U name *)
Definition open_tt T U := open_tt_rec 0 U T.


Inductive rt_type : typ -> Prop :=
  | rt_type_rcd_nil :
      rt_type typ_rcd_nil
  | rt_type_rcd_cons : forall i T1 T2,
      rt_type (typ_rcd_cons i T1 T2)
.

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
  | type_rcd_nil :
      type typ_rcd_nil
  | type_rcd_cons : forall i T1 T2,
      type T1 ->
      type T2 ->
      rt_type T2 ->
      type (typ_rcd_cons i T1 T2)
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
  | typ_rcd_nil     => typ_rcd_nil
  | typ_rcd_cons i T1 T2  => typ_rcd_cons i (subst_tt Z U T1) (subst_tt Z U T2)                   
  end.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_mu T => (fv_tt T)
  | typ_rcd_nil     => {}
  | typ_rcd_cons i T1 T2  => fv_tt T1 \u fv_tt T2
  end.


Inductive IsoMode := Neg | Pos.

Inductive CmpMode := Lt | Eq.


Inductive binding : Set :=
  | bind_sub : IsoMode -> binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).
Definition emp := Metatheory.empty.
Notation empty := (@nil (atom * binding)).


Fixpoint Tlookup (i':var) (Tr:typ) : option typ :=
  match Tr with
  | (typ_rcd_cons i T1 T2) =>
      if i == i' then Some T1 else Tlookup i' T2
  | _ => None
  end.

Fixpoint collectLabel (T : typ) : atoms :=
  match T with
  | (typ_rcd_cons i T1 T2) => {{i}} \u collectLabel T2
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
| WFS_rcd_nil : forall E,
      WFS E typ_rcd_nil
| WFS_rcd_cons : forall E i T1 T2,
      WFS E T1 ->
      WFS E T2 ->
      rt_type T2 ->
      i \notin (collectLabel T2) ->
      WFS E (typ_rcd_cons i T1 T2)
.


Fixpoint fl_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fl_tt T1) `union` (fl_tt T2)
  | typ_mu T => (fl_tt T)
  | typ_rcd_nil     => {}
  | typ_rcd_cons i T1 T2  => {{i}} \u fl_tt T1 \u fl_tt T2
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
  | exp_rcd_nil : exp
  | exp_rcd_cons : var -> exp -> exp -> exp
  | exp_rcd_proj : exp -> var -> exp
.

Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


Fixpoint collectLabele (e: exp) : atoms :=
  match e with
  | (exp_rcd_cons i e1 e2) => {{i}} \u collectLabele e2
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
  | exp_rcd_nil => exp_rcd_nil
  | exp_rcd_cons i e1 e2 => exp_rcd_cons i (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_rcd_proj e1 i => exp_rcd_proj (open_ee_rec k f e1) i   
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
  | exp_rcd_nil => exp_rcd_nil
  | exp_rcd_cons i e1 e2 => exp_rcd_cons i (subst_ee y u e1) (subst_ee y u e2)
  | exp_rcd_proj e1 i => exp_rcd_proj (subst_ee y u e1) i
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
  | exp_rcd_nil => {}
  | exp_rcd_cons i e1 e2 => fv_exp e1 \u fv_exp e2
  | exp_rcd_proj e1 i => fv_exp e1
  end.

Inductive rt_expr : exp -> Prop :=
  | rt_expr_rcd_nil :
      rt_expr exp_rcd_nil
  | rt_expr_rcd_cons : forall i e1 e2,
      rt_expr (exp_rcd_cons i e1 e2)
.

Fixpoint tlookup (i':var) (Er:exp) : option exp :=
  match Er with
  | (exp_rcd_cons i e1 e2) =>
      if i == i' then Some e1 else tlookup i' e2
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
  | lc_rcd_nil :
      expr exp_rcd_nil
  | lc_rcd_cons : forall i e1 e2,
      expr e1 ->
      expr e2 ->
      rt_expr e2 ->
      expr (exp_rcd_cons i e1 e2)
  | lc_rcd_proj : forall i e,
      expr e ->
      expr (exp_rcd_proj e i)
     .

Definition body_e (e : exp) :=
    exists L, forall x : atom, x `notin` L -> expr (open_ee e x).
  
  

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
| Sa_rcd_eq: forall A1 A2 E im evs,
    wf_env E ->
    rt_type A1 ->
    rt_type A2 ->
    collectLabel A2 [=] collectLabel A1 ->
    WFS E A1 -> WFS E A2 ->
    (forall i t1 t2, Tlookup i A1 = Some t1 ->  Tlookup i A2 = Some t2 -> 
      exists evs', evs' [<=] evs /\ Sub im Eq evs E t1 t2) ->
    (forall X, X `in` evs -> 
      exists i t1 t2 evs', 
        Tlookup i A1 = Some t1 /\ Tlookup i A2 = Some t2 /\
        Sub im Eq evs' E t1 t2 /\ X `in` evs') ->
    Sub im Eq evs E A1 A2
| Sa_rcd_lt: forall A1 A2 E im,
    wf_env E ->
    rt_type A1 ->
    rt_type A2 ->
    collectLabel A2 [<=] collectLabel A1 ->
    WFS E A1 -> WFS E A2 ->
    (forall i t1 t2, Tlookup i A1 = Some t1 ->  Tlookup i A2 = Some t2 -> 
      exists cm evs', Sub im cm evs' E t1 t2) ->
    (exists i t1 t2 evs', Tlookup i A1 = Some t1 /\  Tlookup i A2 = Some t2 /\
        Sub im Lt evs' E t1 t2) ->
    Sub im Lt emp E A1 A2
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
 | typing_sub: forall G T e S evs cm,
     typing G e S ->
     Sub Pos cm evs G S T ->
     (* because we do not want to apply e:A, |-(+) A <: B and |-(-) B <: C and get e:C, which breaks the transitivity *)
     typing G e T.

Inductive value : exp -> Prop :=
  | value_abs : forall t1 T, 
      expr (exp_abs T t1) ->
      value (exp_abs T t1)
  | value_nat:
      value exp_nat
  | value_fold: forall T e,
      type T ->
      value e ->
      value (exp_fold T e). 

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
     step (exp_unfold T e) (exp_unfold T e').

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union`  E \u C \u D \u F).

#[global] Hint Constructors Sub WFS typing step value expr wf_env: core.