From Stdlib Require Import List SetoidList.
From LJF Require Import SharedLogic Predicates Sequents Pndctx Search_Procedure LJFPS_Rules LJFh_Rules Schemes Subsequent_Preservation.
From Equations Require Import Equations.

Definition returns_some_proof {A B : Prop} (r : option ({A} + {B})) : Prop :=
  match r with Some (left _) => True | _ => False end.

Definition returns_some_disproof {A B : Prop} (r : option ({A} + {B})) : Prop :=
  match r with Some (right _) => True | _ => False end.

Definition returns_none {A B : Prop} (r : option ({A} + {B})) : Prop :=
  match r with None => True | _ => False end.

Lemma returns_some_proof_inv {A B : Prop} {r : option ({A} + {B})} :
  returns_some_proof r -> exists p : A, r = Some (left p).
Proof.
    intros. destruct r as [[s | s]|] ; try contradiction.
    eexists s. reflexivity.
Qed.

Lemma try_Lf_complete :
    forall (C : pndctx) (K : o) (try_N : forall N : o, In N (pndctx_list C) -> option (sumbool (lfc C N K) (~ lfc C N K)))
            (neg_ctx : list o)
            (H_Forall : Forall (fun N : o => In N (pndctx_list C) /\ negative N) neg_ctx)
            (M : o), 
        In M neg_ctx ->
        (forall (Hin : In M (pndctx_list C)), returns_some_proof (try_N M Hin)) ->
        returns_some_proof (try_Lf try_N neg_ctx H_Forall).
Proof.
    intros C K try_N neg_ctx. induction neg_ctx ; intros.
    - inversion H.
    - destruct H ; subst.
        + specialize (H0 (proj1 (Forall_inv H_Forall))). simp try_Lf.
            apply returns_some_proof_inv in H0. destruct H0. rewrite H. simpl. apply I.
        + specialize (IHneg_ctx (Forall_inv_tail H_Forall) M H H0).
            apply returns_some_proof_inv in IHneg_ctx. destruct IHneg_ctx. simp try_Lf.
            destruct (try_N a (proj1 (Forall_inv H_Forall))).
            destruct s.
            -- simpl. apply I.
            -- simpl. rewrite H1. simpl. apply I.
            -- simpl. rewrite H1. simpl. apply I.
Qed.
                
Lemma try_Lf_wrapper_complete :
    forall (C : pndctx) (K : o) 
            (try_N : forall N : o, In N (pndctx_list C) -> option (sumbool (lfc C N K) (~ lfc C N K)))
            (M : o),
        In M (pndctx_list C) ->
        negative M ->
        (forall Hin : In M (pndctx_list C), returns_some_proof (try_N M Hin)) ->
        returns_some_proof (try_Lf_wrapper try_N).
Proof.
    intros. unfold try_Lf_wrapper.
    apply (try_Lf_complete C K try_N (filter negative_b (pndctx_list C)) (filter_neg_forall C) M).
    - apply (proj2 (filter_In negative_b M (pndctx_list C)) (conj H (proj2 (negative_b_iff M) H0))).
    - apply H1.
Qed. 

Theorem search_complete :
    (forall {Hstack: hist} {C: pndctx} {L: octx} {K: o}, 
        bcth Hstack C L K ->
        forall (init : sequent) 
            (Hsub : subsequent (Sbct C L K) init)
            (Hstack_NoDup  : NoDupA pndctx_o_eq Hstack)
            (Hstack_sub  : Forall (fun e => subsequent (Sept (fst e) nil (snd e)) init) Hstack),
            returns_some_proof (search init (Sbct C L K) Hsub Hstack Hstack_NoDup Hstack_sub)) /\

    (forall {Hstack: hist} {C: pndctx} {L: octx} {K: o}, 
        epth Hstack C L K ->
        forall (init : sequent) 
            (Hsub : subsequent (Sept C L K) init)
            (Hstack_NoDup  : NoDupA pndctx_o_eq Hstack)
            (Hstack_sub  : Forall (fun e => subsequent (Sept (fst e) nil (snd e)) init) Hstack),
        returns_some_proof (search init (Sept C L K) Hsub Hstack Hstack_NoDup Hstack_sub)) /\

   (forall {Hstack: hist} {C: pndctx} {N K: o}, 
        lfch Hstack C N K ->
        forall (init : sequent) 
            (Hsub : subsequent (Slfc C N K) init)
            (Hstack_NoDup  : NoDupA pndctx_o_eq Hstack)
            (Hstack_sub  : Forall (fun e => subsequent (Sept (fst e) nil (snd e)) init) Hstack),
        returns_some_proof (search init (Slfc C N K) Hsub Hstack Hstack_NoDup Hstack_sub)) /\

    (forall {Hstack: hist} {C: pndctx} {K: o}, 
        rfch Hstack C K ->
        forall (init : sequent) 
            (Hsub : subsequent (Srfc C K) init)
            (Hstack_NoDup  : NoDupA pndctx_o_eq Hstack)
            (Hstack_sub  : Forall (fun e => subsequent (Sept (fst e) nil (snd e)) init) Hstack),
        returns_some_proof (search init (Srfc C K) Hsub Hstack Hstack_NoDup Hstack_sub)).
Proof.
    apply LJFh_mutind_all ; intros.
    - destruct D ; simp search ; cbv zeta.
        + destruct p ; simp search ; cbv zeta.
            -- specialize (H init (subp_bct_boxR (Bracketable_pos (Atom Pos n) (Pos_atom n)) Hsub) Hstack_NoDup Hstack_sub).
                apply returns_some_proof_inv in H. destruct H.
                rewrite H. simpl. apply I.
            -- specialize (H init (subp_bct_boxR (Bracketable_neg_atom (Atom Neg n) (Is_atom Neg n) (Neg_atom n)) Hsub) Hstack_NoDup Hstack_sub).
                apply returns_some_proof_inv in H. destruct H.
                rewrite H. simpl. apply I.
        + specialize (H init (subp_bct_boxR (Bracketable_pos TT Pos_true) Hsub) Hstack_NoDup Hstack_sub).
            apply returns_some_proof_inv in H. destruct H.
                rewrite H. simpl. apply I.
        + specialize (H init (subp_bct_boxR (Bracketable_pos FF Pos_false) Hsub) Hstack_NoDup Hstack_sub).
            apply returns_some_proof_inv in H. destruct H.
            rewrite H. simpl. apply I.
        + specialize (H init (subp_bct_boxR (Bracketable_pos (AndP D1 D2) (Pos_and D1 D2)) Hsub) Hstack_NoDup Hstack_sub).
            apply returns_some_proof_inv in H. destruct H.
            rewrite H. simpl. apply I.
        + inversion b ; inversion H0.
        + specialize (H init (subp_bct_boxR (Bracketable_pos (Or D1 D2) (Pos_or D1 D2)) Hsub) Hstack_NoDup Hstack_sub).
            apply returns_some_proof_inv in H. destruct H.
            rewrite H. simpl. apply I.
        + inversion b ; inversion H0.
    - simp search.
        specialize (H init (proj1 (subp_bct_AndNR Hsub)) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. 
        specialize (H0 init (proj2 (subp_bct_AndNR Hsub)) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H0. destruct H0. cbn in H0. cbn. rewrite H0. simpl. apply I.
    - simp search.
        specialize (H init (subp_bct_ImpR Hsub) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H.
        rewrite H. simpl. apply I.
    - rewrite search_equation_9. destruct (InA_dec (eqA:=pndctx_o_eq) pndctx_o_eq_dec (C, K) Hs).
        + contradiction.
        + simpl. 
            assert (returns_some_proof 
                    (try_Lf_wrapper 
                        (fun N0 HinN => 
                        search init (Slfc C N0 K) (subp_ept_Lf HinN Hsub) ((C, K) :: Hs) (NoDupA_cons n1 Hstack_NoDup)  (Forall_cons (C, K) Hsub Hstack_sub)))).
            -- apply (try_Lf_wrapper_complete C K _ N i n0). intros.
                specialize (H init (subp_ept_Lf Hin Hsub) (NoDupA_cons n1 Hstack_NoDup) (Forall_cons (C, K) Hsub Hstack_sub)).
                apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
            -- destruct (Decidability.positive_dec K).
                ++ simp search. destruct (search init (Srfc C K) (subp_ept_Rf Hsub) ((C, K) :: Hs) (NoDupA_cons (x:=(C, K)) n1 Hstack_NoDup) (Forall_cons (C, K) Hsub Hstack_sub)).
                    --- destruct s.
                        +++ simpl. apply I.
                        +++ simpl. apply returns_some_proof_inv in H0. destruct H0. cbn in H0. cbn. rewrite H0. simpl. apply I.
                    --- simpl. apply returns_some_proof_inv in H0. destruct H0. cbn in H0. cbn. rewrite H0. simpl. apply I.
                ++ simp search. apply returns_some_proof_inv in H0. destruct H0. cbn in H0. cbn. rewrite H0. simpl. apply I.
    - rewrite search_equation_9. destruct (InA_dec (eqA:=pndctx_o_eq) pndctx_o_eq_dec (C, P) Hs).
        + contradiction.
        + simpl. destruct (Decidability.positive_dec P).
            -- simpl. specialize (H init (subp_ept_Rf Hsub) (NoDupA_cons (x:=(C, P)) n0 Hstack_NoDup) (Forall_cons (C, P) Hsub Hstack_sub)).
                apply returns_some_proof_inv in H. destruct H. cbn in H. cbn. rewrite H. simpl. apply I.
            -- contradiction.
    - destruct B ; simp search ; cbv zeta ; try (solve [inversion p ; inversion H0]).
        + destruct p0 ; simp search ; cbv zeta.
            -- specialize (H init (subp_ept_boxL Hsub) Hstack_NoDup Hstack_sub).
                apply returns_some_proof_inv in H. destruct H.
                rewrite H. simpl. apply I.
            -- specialize (H init (subp_ept_boxL Hsub) Hstack_NoDup Hstack_sub).
                apply returns_some_proof_inv in H. destruct H.
                rewrite H. simpl. apply I.
        + specialize (H init (subp_ept_boxL Hsub) Hstack_NoDup Hstack_sub).
            apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
        + specialize (H init (subp_ept_boxL Hsub) Hstack_NoDup Hstack_sub).
            apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
    - simp search.
        specialize (H init (subp_ept_AndPL Hsub) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
    - simp search.
        specialize (H init (proj1 (subp_ept_OrL Hsub)) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H. rewrite H. simpl.
        specialize (H0 init (proj2 (subp_ept_OrL Hsub)) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H0. destruct H0. cbn in H0. cbn. rewrite H0. simpl. apply I.
    - simp search.
        specialize (H init (subp_ept_TrueL Hsub) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
    - simp search.
        destruct (Decidability.bracketable_dec K).
        + simpl. apply I.
        + contradiction.
    - inversion p ; subst.
        + rewrite search_equation_18 ; cbv zeta.
            specialize (H init (subp_lfc_Rl Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
        + rewrite search_equation_20 ; cbv zeta.
            specialize (H init (subp_lfc_Rl Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
        + rewrite search_equation_21 ; cbv zeta.
            specialize (H init (subp_lfc_Rl Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
        + rewrite search_equation_22 ; cbv zeta.
            specialize (H init (subp_lfc_Rl Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
        + rewrite search_equation_24 ; cbv zeta.
            specialize (H init (subp_lfc_Rl Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
    - inversion n.
        + inversion a ; subst.
            simp search.
            destruct (Decidability.o_eq_dec (Atom Neg n0) (Atom Neg n0)).
            -- simpl. apply I.
            -- inversion H0 ; subst. contradiction.
        + inversion a ; subst. inversion H0.
        + inversion a ; subst. inversion H0.
    - simp search.
        specialize (H init (subp_lfc_AndNL_1 Hsub) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
    - rewrite search_equation_23.
        specialize (H init (subp_lfc_AndNL_2 Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H.
        destruct (search init (Slfc C B1 K) (subp_lfc_AndNL_1 Hsub) Hs Hstack_NoDup Hstack_sub).
        + destruct s.
            -- simpl. apply I.
            -- simpl. rewrite H. simpl. apply I.
        + simpl. rewrite H. simpl. apply I.
    - simp search.
        specialize (H init (proj1 (subp_lfc_ImpL Hsub)) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H. rewrite H. simpl.
        specialize (H0 init (proj2 (subp_lfc_ImpL Hsub)) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H0. destruct H0. cbn in H0. cbn. rewrite H0. simpl. apply I.
    - inversion n ; subst.
        + rewrite search_equation_27 ; cbv zeta.
            specialize (H init (subp_rfc_Rr Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
        + rewrite search_equation_31 ; cbv zeta.
            specialize (H init (subp_rfc_Rr Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
        + rewrite search_equation_33 ; cbv zeta.
            specialize (H init (subp_rfc_Rr Hsub) Hstack_NoDup Hstack_sub). apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
    - inversion p ; inversion a ; subst ; inversion H0. subst. simp search. 
        destruct (in_dec Decidability.o_eq_dec (Atom Pos n) (pndctx_list C)).
        + simpl. apply I.
        + contradiction.
    - simp search.
        specialize (H init (proj1 (subp_rfc_AndPR Hsub)) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H. rewrite H. simpl.
        specialize (H0 init (proj2 (subp_rfc_AndPR Hsub)) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H0. destruct H0. cbn in H0. cbn. rewrite H0. simpl. apply I.
    - simp search.
        specialize (H init (subp_rfc_OrR_1 Hsub) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H. destruct H. rewrite H. simpl. apply I.
    - rewrite search_equation_32.
        specialize (H init (subp_rfc_OrR_2 Hsub) Hstack_NoDup Hstack_sub).
        apply returns_some_proof_inv in H ; destruct H.
        destruct (search init (Srfc C B1) (subp_rfc_OrR_1 Hsub) Hs Hstack_NoDup Hstack_sub).
        + destruct s.
            -- simpl. apply I.
            -- simpl. rewrite H. simpl. apply I.
        + simpl. rewrite H. simpl. apply I.
    - simp search. simpl. apply I.
Qed.
