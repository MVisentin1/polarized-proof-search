From Stdlib Require Import List PeanoNat.
From LJF Require Import SharedLogic Decidability 
    Predicates Subformula Pndctx LJFPS_Rules Sequents Measures.

Definition phase_ranking (S: sequent) : nat :=
    match S with
    | Sbct _ _ K => 1
    | Sept _ L _ => 0
    | Slfc _ N _ => 3
    | Srfc _ K   => 2
    end
.

Definition phase_measure (S: sequent) : nat :=
    match S with
    | Sbct _ _ K => osize K
    | Sept _ L _ => octx_size L
    | Slfc _ N _ => osize N
    | Srfc _ K   => osize K
    end
.

(*Definition sequent_eq (S1 S2 : sequent) : Prop :=
    match S1, S2 with
    | Sbct C1 L1 K1, Sbct C2 L2 K2 =>
        pndctx_set_eq C1 C2 /\ L1 = L2 /\ K1 = K2
    | Sept C1 L1 K1, Sept C2 L2 K2 =>
        pndctx_set_eq C1 C2 /\ L1 = L2 /\ K1 = K2
    | Slfc C1 N1 K1, Slfc C2 N2 K2 =>
        pndctx_set_eq C1 C2 /\ N1 = N2 /\ K1 = K2
    | Srfc C1 K1,    Srfc C2 K2    =>
        pndctx_set_eq C1 C2 /\ K1 = K2
    | _, _ => False
    end
.

Lemma sequent_eq_dec :
    forall (S1 S2: sequent),
        {sequent_eq S1 S2} + {~ sequent_eq S1 S2}.
Proof.
    intros. unfold sequent_eq.
    destruct S1 as [p l k | p l k | p n k | p k]; 
    destruct S2 as [p0 l0 k0 | p0 l0 k0 | p0 n0 k0 | p0 k0]. 
    all : try (right ; intro ;apply H).
    -   destruct (pndctx_set_eq_dec p p0); 
        destruct (list_eq_dec o_eq_dec l l0);
        destruct (o_eq_dec k k0).
        all : try (right ; intro ; destruct H ; destruct H0 ; contradiction).
        left. auto.
    -   destruct (pndctx_set_eq_dec p p0); 
        destruct (list_eq_dec o_eq_dec l l0);
        destruct (o_eq_dec k k0).
        all : try (right ; intro ; destruct H ; destruct H0 ; contradiction).
        left. auto.
    -   destruct (pndctx_set_eq_dec p p0);
        destruct (o_eq_dec n n0);
        destruct (o_eq_dec k k0).
        all : try (right ; intro ; destruct H ; destruct H0 ; contradiction).
        left. auto.
    -   destruct (pndctx_set_eq_dec p p0);
        destruct (o_eq_dec k k0).
        all : try (right ; intro ; destruct H ; destruct H0 ; contradiction).
        left. auto.
Qed.*)