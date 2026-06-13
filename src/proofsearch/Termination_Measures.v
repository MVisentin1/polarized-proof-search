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

Definition number_focus_decision (S: sequent) : nat :=
    let neg := length (sequent_subformulas_negative S) in
    let pos := length (sequent_subformulas_positive S) in
    let per := length (sequent_subformulas_permeable S) in
    let bra := length (sequent_subformulas_bracketable S) in
    2^per * neg * bra + 2^per * pos
.

Definition pndctx_set_eq (C1 C2 : pndctx) : Prop :=
   incl (pndctx_list C1) (pndctx_list C2) /\ incl (pndctx_list C2) (pndctx_list C1).

Lemma pndctx_set_eq_dec :
    forall (C1 C2: pndctx), {pndctx_set_eq C1 C2} + {~ pndctx_set_eq C1 C2}.
Proof.
    intros. unfold pndctx_set_eq.
    unfold incl.
    destruct 
        (Forall_dec (fun A => In A (pndctx_list C2)) 
        (fun A => in_dec o_eq_dec A (pndctx_list C2)) 
        (pndctx_list C1));
    destruct 
        (Forall_dec (fun A => In A (pndctx_list C1)) 
        (fun A => in_dec o_eq_dec A (pndctx_list C1)) 
        (pndctx_list C2)).
    - left. split. 
        eapply Forall_forall. apply f.
        eapply Forall_forall. apply f0.
    - right. intro. apply n.
        destruct H. apply Forall_forall. apply H0.
    - right. intro. apply n.
        destruct H. apply Forall_forall. apply H.
    - right. intro. apply n.
        destruct H. apply Forall_forall. apply H.
Qed.

Definition sequent_eq (S1 S2 : sequent) : Prop :=
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
Qed.



    
