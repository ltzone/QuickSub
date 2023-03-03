Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export LinearRule.



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


Lemma trans_aux: forall B E,
    WFS E B -> forall im cm1 cm2 A C evs1 evs2,
    Sub im cm1 evs1 E A B -> Sub im cm2 evs2 E B C -> 
    exists evs, evs [<=] evs1 `union` evs2 /\
      Sub im (seq_cm cm1 cm2) evs E A C.
Proof with auto.
  intros B E H.
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
        admit.

    +
      dependent induction H;subst...
      *
        (* A <: nat, nat <: top *)
        exists emp;split... fsetdec.
      *
        admit.
    +
      admit.
  -
    (* B = X  *)
    dependent induction H0;subst...
    +
      dependent induction H2;subst...
      *
        (* X <:(+) X, X <: top *)
        exists emp;split... fsetdec.
      *
        (* X <:(+) X, X <:(+) X *)
        exists emp;split... fsetdec.
      *
        (* X <:(+) X, X <:(-) X *)
        apply uniq_from_wf_env in H1.
        pose proof binds_unique _ _ _ _ _ H0 H2 H1 as Eb.
        inversion Eb;subst... destruct im0;inversion H5.
        (* contradiction *)
      *
        admit.
    +
      dependent induction H2;subst...
      *
        (* X <: (-) X, X <: Top
        Note: in this case, evs is not union evs1 evs2
        *)
        exists emp;split... admit.
      *
        (* X <:(-) X, X <:(+) X *)
        apply uniq_from_wf_env in H1.
        pose proof binds_unique _ _ _ _ _ H0 H2 H1 as Eb.
        inversion Eb;subst... destruct im0;inversion H5.
        (* contradiction *)
      *
        (* X <:(-) X, X <:(-) X *)
        exists {{ X }};split... admit.
      *
        admit.
    +
      destruct IHSub with (X0:=X) as [evs0 [? ?]]...
      exists evs0;split... fsetdec.
  -
    (* B = A -> B *)
    dependent induction H1;subst...
    +
      dependent induction H2;subst...
      *
        (* A1 -> A2 < A -> B < Top  *)
        exists emp;split...
        { fsetdec. }
        rewrite seq_cm_lt2. apply Sa_top_lt...
        { get_well_form... } { intros C. inversion C. }
      *
        (* A1 -> A2 < A -> B < B1 -> B2 *)
        destruct IHWFS1 with (im:=flip_im im)
          (cm1:=cm2) (evs1:=evs2) (A0:=B1)
          (cm2:=cm1) (evs2:=evs1) (C:=A1) as [evs1' [Es1a Es1b]]...
        destruct IHWFS2 with (im:=im)
          (cm1:=cm0) (evs1:=evs0) (A:=A2)
          (cm2:=cm3) (evs2:=evs3) (C:=B2) as [evs2' [Es2a Es2b]]...
        exists (evs1' `union` evs2'). split. { fsetdec. }
        apply Sa_arrow with (cm1:= seq_cm cm2 cm1) (cm2:= seq_cm cm0 cm3)...
        { clear IHSub1 IHSub2 IHSub0 IHSub3.
          destruct cm2, cm3, cm1, cm0, cm, cm4; simpl in *;
          try solve 
          [ destruct (AtomSetImpl.is_empty evs2);inversion H2|
            destruct (AtomSetImpl.is_empty evs3);inversion H2|
            destruct (AtomSetImpl.is_empty evs1);inversion H1|
            destruct (AtomSetImpl.is_empty evs0);inversion H1
            ]...
          + admit.
          + 
          (* 
          require syntactic equal
          
          If B = A2 |> { ... } evs0 not empty
          then exists x, ~ posvar x B A2
          but A2 = B2
          so ~ posvar x B B2
          but B = B2 |> emp
          contradiction
          
          *)
          admit.
          + admit.
          + admit.
          + 
          (* require syntactic *) admit.
          +
          (* require syntactic *) admit.
          
        }
    
