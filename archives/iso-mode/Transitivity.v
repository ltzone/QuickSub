Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Infra.




Lemma trans_aux : forall E B,
WFS E B ->
forall A C,
  Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
intros E B H.
dependent induction H;intros...
- (* top *)
dependent induction H...
+
  dependent induction H1...
- (* nat *)
dependent induction H...
- (* var *)
dependent induction H0...
- (* arrow *)
assert (WFS E A0).
get_well_form...
assert (WFS E C).
get_well_form...
dependent induction H3... (* induction A0 *)
+ (* top *)
  dependent destruction H1...
+ (* nat *)
  dependent destruction H1.
+ (* var *)
  dependent destruction H1.
+ (* arrow *)
  dependent induction H4;try solve [dependent destruction H2;inversion H3]...
  * (* top *)
    constructor...
    get_well_form...
  * (* arrow *)
    clear IHWFS5 IHWFS3 IHWFS4 IHWFS6.
    dependent destruction H1.
    dependent destruction H2.
    constructor...
+ (* rcd *)
  dependent induction H1...
+ (* rec *)
  dependent induction H1...
- (* rcd *)
assert (WFS E A /\ WFS E C /\ wf_env E).
get_well_form...
destruct_hypos.
dependent induction H2; try solve [inversion H0;dependent destruction H0;auto]...
+ (* rcd *)
  dependent induction H1...
  *
    inversion H0;subst.
    --
      dependent destruction H0...
- (* rec *)
dependent induction H3...
+ (* rec *)
  clear H4 H6.
  dependent induction H7...
  * (* rec *)
    apply S_rec with (L:=L \u L0 \u L1)...
  *
    apply S_top...
    apply WFS_rec with (L:= L \u L0);intros.
    specialize_x_and_L X L0.
    get_well_form...
    specialize_x_and_L X L0.
    get_well_form...
Qed.


Lemma Transitivity : forall E B A C,
  Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
intros.
assert (WFS E B).
apply sub_regular in H0.
apply H0.
apply trans_aux with (B:=B)...
Qed.


