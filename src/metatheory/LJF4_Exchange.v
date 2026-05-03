From Stdlib Require Import List.
From CARVe Require Import contexts.list.
From CARVe Require Import algebras.dill.
From LJF Require Import LJF_Rules LJF4_Rules SharedLogic.
From Stdlib Require Import Permutation.

Scheme bct4_mut := Induction for bct4 Sort Prop
  with ept4_mut := Induction for ept4 Sort Prop
  with lfc4_mut := Induction for lfc4 Sort Prop
  with rfc4_mut := Induction for rfc4 Sort Prop.

Combined Scheme LJF4_mutind from bct4_mut, ept4_mut, lfc4_mut, rfc4_mut.

Lemma LJF4_exchange_perm :
  (forall C K, bct4 C K -> forall C', Permutation C C' -> bct4 C' K) /\
  (forall C K, ept4 C K -> forall C', Permutation C C' -> ept4 C' K) /\
  (forall C N K, lfc4 C N K -> forall C', Permutation C C' -> lfc4 C' N K) /\
  (forall C P, rfc4 C P -> forall C', Permutation C C' -> rfc4 C' P).
Proof.  apply LJF4_mutind ; intros.
    - apply bct4_R_box. apply b. apply H. apply H0.
    - apply bct4_R_AndN.
        + apply H. apply H1.
        + apply H0. apply H1.
    - apply bct4_R_Impl. apply H. apply perm_skip. apply H0.
    - apply ept4_L_f with (N := N). 
        + eapply perm_exh with (l := C) ; [>typeclasses eauto | typeclasses eauto | exact H0 | exact e].
        + apply Permutation_in with (l := C). apply H0. apply h.
        + apply b.
        + apply n. 
        + apply H. apply H0.
    - apply ept4_R_f.
        + eapply perm_exh with (l := C) ; [>typeclasses eauto | typeclasses eauto | exact H0 | exact e].
        + apply p.
        + apply H. apply H0. 
    - destruct (perm_upd_rel_ex H0 u) as (C1' & Hupd' & Hp1). 
        eapply ept4_L_box with (B := B).
        + eapply perm_has_entry with (l := C). apply h. apply H0.
        + apply Hupd'.
        + apply b.
        + apply p.
        + apply H. apply Hp1.
    - destruct (perm_upd_rel_ex H0 u) as (C1' & Hupd' & Hp1). 
        eapply ept4_L_AndP with (B1 := B1) (B2 := B2).
        + apply perm_has_entry with (l := C). apply h. apply H0.
        + apply Hupd'.
        + apply b.
        + apply H. apply Permutation_cons. reflexivity. apply Permutation_cons.
            reflexivity. apply Hp1.
    - destruct (perm_upd_rel_ex H1 u) as (C1' & Hupd' & Hp1). 
        eapply ept4_L_Or with (B1 := B1) (B2 := B2).
        + apply perm_has_entry with (l := C). apply h. apply H1.
        + apply Hupd'.
        + apply b.
        + apply H. apply Permutation_cons. reflexivity. apply Hp1.
        + apply H0. apply Permutation_cons. reflexivity. apply Hp1.
    - destruct (perm_upd_rel_ex H0 u) as (C1' & Hupd' & Hp1). 
        eapply ept4_L_True.
        + apply perm_has_entry with (l := C). apply h. apply H0.
        + apply Hupd'.
        + apply b.
        + apply H. apply Hp1. 
    - apply ept4_L_False. apply perm_has_entry with (l := C). apply h. apply H. apply b. 
    - apply lfc4_R_l.
        + eapply perm_exh with (l := C) ; [>typeclasses eauto | typeclasses eauto | exact H0 | exact e].
        + apply b.
        + apply p.
        + apply H. apply Permutation_cons. reflexivity. apply H0.
    - apply lfc4_I_l. 
        + eapply perm_exh with (l := C) ; [> typeclasses eauto | typeclasses eauto | apply H | exact e].
        + apply n.
        + apply a.
    - apply lfc4_L_AndN_1.
        + eapply perm_exh with (l := C) ; [> typeclasses eauto | typeclasses eauto | apply H0 | exact e].
        + apply b.
        + apply H. apply H0.
    - apply lfc4_L_AndN_2.
        + eapply perm_exh with (l := C) ; [> typeclasses eauto | typeclasses eauto | apply H0 | exact e].
        + apply b.
        + apply H. apply H0.
    - apply lfc4_L_Impl.
        + eapply perm_exh with (l := C) ; [> typeclasses eauto | typeclasses eauto | apply H1 | exact e].
        + apply b.
        + apply H. apply H1.
        + apply H0. apply H1.
    - apply rfc4_R_r. 
        + eapply perm_exh with (l := C); [> typeclasses eauto | typeclasses eauto | apply H0 | exact e].
        + apply n.
        + apply H. apply H0.
    - apply rfc4_I_r.
        + eapply perm_exh with (l := C); [> typeclasses eauto | typeclasses eauto | apply H | exact e].
        + apply perm_has_entry with (l := C). apply h. apply H.
        + apply p.
        + apply a.
    - apply rfc4_R_AndP.
        + eapply perm_exh with (l := C); [> typeclasses eauto | typeclasses eauto | apply H1 | exact e].
        + apply H. apply H1.
        + apply H0. apply H1.
    - apply rfc4_R_Or_1.
        + eapply perm_exh with (l := C); [> typeclasses eauto | typeclasses eauto | apply H0 | exact e].
        + apply H. apply H0.
    - apply rfc4_R_Or_2.
        + eapply perm_exh with (l := C); [> typeclasses eauto | typeclasses eauto | apply H0 | exact e].
        + apply H. apply H0.
    - apply rfc4_R_True.
        + eapply perm_exh with (l := C); [> typeclasses eauto | typeclasses eauto | apply H | exact e].
Qed.
