From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJF4_Rules LJFPS_Rules LJFPS_Exchange.

From Equations Require Import Equations.

Scheme bct4_mut := Induction for bct4 Sort Prop
  with ept4_mut := Induction for ept4 Sort Prop
  with lfc4_mut := Induction for lfc4 Sort Prop
  with rfc4_mut := Induction for rfc4 Sort Prop.

Combined Scheme LJF4_mutind_all from bct4_mut, ept4_mut, lfc4_mut, rfc4_mut.

Theorem LJFPS_completeness : 
    (forall {C: sctx} {L: lctx} {K: o}, bct4 C L K -> bct C L K) /\
    (forall {C: sctx} {L: lctx} {K: o}, ept4 C L K -> ept C L K) /\
    (forall {C: sctx} {N K: o}, lfc4 C N K -> lfc C N K) /\
    (forall {C: sctx} {K: o}, rfc4 C K -> rfc C K).
Proof.
    apply LJF4_mutind_all ; intros.
        - apply bct_boxR. apply b. apply H.
        - apply bct_AndNR. apply H. apply H0.
        - apply bct_ImpR. apply H.
        - eapply ept_Lf. apply i. apply b. apply n. apply H.
        - apply ept_Rf. apply p. apply H.
        - eapply LJFPS_exchange_ordered_ept. 2: apply Permutation_sym. 2: apply p.
            apply ept_boxL. apply b. apply p0. apply H.
        - eapply LJFPS_exchange_ordered_ept. 2: apply Permutation_sym. 2: apply p.
            apply ept_AndPL. apply b. apply H.
        - eapply LJFPS_exchange_ordered_ept. 2: apply Permutation_sym. 2: apply p.
            apply ept_OrL. apply b. apply H. apply H0.
        - eapply LJFPS_exchange_ordered_ept. 2: apply Permutation_sym. 2: apply p.
            apply ept_TrueL. apply b. apply H.
        - apply eager_FalseL. apply b. apply i.
        - apply lfc_Rl. apply b. apply p. apply H.
        - apply lfc_Il. apply n. apply a.
        - apply lfc_AndNL_1. apply b. apply H.
        - apply lfc_AndNL_2. apply b. apply H.
        - apply lfc_ImpL. apply b. apply H. apply H0.
        - apply rfc_Rr. apply n. apply H.
        - apply rfc_Ir. apply i. apply p. apply a.
        - apply rfc_AndPR. apply H. apply H0.
        - apply rfc_OrR_1. apply H.
        - apply rfc_OrR_2. apply H.
        - apply rfc_TrueR.
Qed.

            
        


