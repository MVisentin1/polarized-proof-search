From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJF_Rules LJF4_Rules LJF4_Exchange Schemes.

Theorem LJF4_soundness : 
  (forall {C: sctx} {L: lctx} {K: o}, bct4 C L K -> ufcL C L K Unbracketed) /\
  (forall {C: sctx} {L: lctx} {K: o}, ept4 C L K -> ufcL C L K Bracketed) /\
  (forall {C: sctx} {N K: o}, lfc4 C N K -> lfcL C N K) /\
  (forall {C: sctx} {K: o}, rfc4 C K -> rfcL C K).
Proof.
    apply LJF4_mutind_all ; intros.
    - apply ufcL_boxR. apply b. apply H.
    - apply ufcL_AndNR. apply H. apply H0.
    - apply ufcL_ImpR. apply H.
    - eapply ufcL_Lf. apply i. apply b. apply n. apply H.
    - apply ufcL_Rf. apply p. apply H.
    - eapply ufcL_boxL. apply p. apply b. apply p0. apply H.
    - eapply ufcL_AndPL. apply p. apply b. apply H.
    - eapply ufcL_OrL. apply p. apply b. apply H. apply H0.
    - eapply ufcL_TrueL. apply p. apply b. apply H.
    - apply ufcL_FalseL. apply i. apply b.
    - apply lfcL_Rl. apply b. apply p. apply H.
    - apply lfcL_Il. apply n. apply a.
    - apply lfcL_AndNL_1. apply b. apply H.
    - apply lfcL_AndNL_2. apply b. apply H.
    - apply lfcL_ImpL. apply b. apply H. apply H0.
    - apply rfcL_Rr. apply n. apply H.
    - apply rfcL_Ir. apply i. apply p. apply a.
    - apply rfcL_AndPR. apply H. apply H0.
    - apply rfcL_OrR_1. apply H.
    - apply rfcL_OrR_2. apply H.
    - apply rfcL_TrueR.
Qed.