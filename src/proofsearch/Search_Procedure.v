From Stdlib Require Import List PeanoNat SetoidList Lia.
From LJF Require Import SharedLogic Decidability
    Predicates Subformula Pndctx LJFPS_Rules Sequents Measures LJFPS_Bracketable
    Termination_Measures LJFPS_Inversion Subsequent_Preservation Subsets SetoidList_Extended Focus_Decision_Set.
From Equations Require Import Equations.

Equations try_Lf {C : pndctx} {K : o}
    (try_N : forall N, In N (pndctx_list C) -> option ({lfc C N K} + {~ lfc C N K}))
    (neg_ctx : list o)
    (H_Forall : Forall (fun N => In N (pndctx_list C) /\ negative N) neg_ctx)
    : option ({ ept C nil K } + { Forall (fun N => ~ lfc C N K) neg_ctx }) :=

    try_Lf try_N nil _ := Some (right (Forall_nil (fun N => ~ lfc C N K))) ;

    try_Lf try_N (N :: neg_rest) H_Forall
      with try_N N (proj1 (Forall_inv H_Forall)) := {
        | Some (left H1)    =>
            let Hin := proj1 (Forall_inv H_Forall) in
            let Hbr := LJFPS_bracketable_goal_lfc H1 in
            let Hne := proj2 (Forall_inv H_Forall) in
            Some (left (ept_Lf N Hin Hbr Hne H1)) ;
        | Some (right H1)   with try_Lf try_N neg_rest (Forall_inv_tail H_Forall) := {
            | Some (left H2)    => Some (left H2) ;
            | Some (right H2)   => Some (right (Forall_cons N H1 H2)) ;
            | None              => None
            }
        | None              with try_Lf try_N neg_rest (Forall_inv_tail H_Forall) := {
            | Some (left H2)    => Some (left H2) ;
            | _                 => None
            }
        }.

Lemma filter_neg_forall (C : pndctx) :
  Forall (fun N => In N (pndctx_list C) /\ negative N) (filter negative_b (pndctx_list C)).
Proof.
  apply Forall_forall. intros N HN.
  apply filter_In in HN as [Hin Hb].
  split.
  - apply Hin.
  - apply negative_b_iff. apply Hb.
Qed.

Definition try_Lf_wrapper {C : pndctx} {K : o}
    (try_N : forall N, In N (pndctx_list C) -> option ({lfc C N K} + {~ lfc C N K}))
    : option ({ ept C nil K } + { Forall (fun N => ~ lfc C N K) (filter negative_b (pndctx_list C)) }) :=
  try_Lf try_N (filter negative_b (pndctx_list C)) (filter_neg_forall C).

Equations search 
    (init seq : sequent)
    (Hsub : subsequent seq init)
    (stack : list (pndctx * o))
    (Hstack_NoDup : NoDupA pndctx_o_eq stack)
    (Hstack_sub : Forall (fun e => subsequent (Sept (fst e) nil (snd e)) init) stack)
    : option ({sequent_derivable seq} + {~ sequent_derivable seq})
    by wf
        (length (get_all_focus_decision init) - length stack , phase_ranking seq, phase_measure seq)
        (lexprod _ _ (lexprod _ _ lt lt) lt) :=
    
    search init (Sept C nil K) Hsub stack Hstack_NoDup Hstack_sub with InA_dec pndctx_o_eq_dec (C, K) stack := {
        | left Hin      => None
        | right Hin     with positive_dec K := {
            | left Hpk  with search init (Srfc C K) (subp_ept_Rf Hsub) ((C, K) :: stack) (NoDupA_cons Hin Hstack_NoDup) (Forall_cons (C, K) Hsub Hstack_sub) := {
                | Some (left H1)    => Some (left (ept_Rf Hpk H1))
                | Some (right H1)   with try_Lf_wrapper 
                    (fun N (HinN : In N (pndctx_list C)) => search init (Slfc C N K) (subp_ept_Lf HinN Hsub) ((C, K) :: stack) (NoDupA_cons Hin Hstack_NoDup) (Forall_cons (C, K) Hsub Hstack_sub)) := {
                        | Some (left H2)    => Some (left H2)
                        | Some (right H2)   => Some (right (ept_nil_disproof_pos Hpk H1 H2))
                        | None              => None
                    }
                | None              with try_Lf_wrapper 
                    (fun N (HinN : In N (pndctx_list C)) => search init (Slfc C N K) (subp_ept_Lf HinN Hsub) ((C, K) :: stack) (NoDupA_cons Hin Hstack_NoDup) (Forall_cons (C, K) Hsub Hstack_sub)) := {
                        | Some (left H2)    => Some (left H2)
                        | Some (right H2)   => None
                        | None              => None
                    }
                }
            | right Hpk     with try_Lf_wrapper
                (fun N (HinN : In N (pndctx_list C)) => search init (Slfc C N K) (subp_ept_Lf HinN Hsub) ((C, K) :: stack) (NoDupA_cons Hin Hstack_NoDup) (Forall_cons (C, K) Hsub Hstack_sub)) := {
                    | Some (left H1)    => Some (left H1)
                    | Some (right H1)   => Some (right (ept_nil_disproof_neg Hpk H1))
                    | None              => None
            }
        }
    } ;

    search init (Sept C ((Atom Pos n) :: L) K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpe := Permeable_pos_atom (Atom Pos n) (Is_atom Pos n) (Pos_atom n) in
        match search init (Sept (pndctx_insert (Atom Pos n) C) L K) (subp_ept_boxL Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (ept_boxL (LJFPS_bracketable_goal_ept H1) Hpe H1))
        | Some (right H1) => Some (right (fun H => H1 (ept_boxL_inv Hpe H)))
        | None            => None
        end ;
    
    search init (Sept C ((Atom Neg n) :: L) K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpe := Permeable_neg (Atom Neg n) (Neg_atom n) in
        match search init (Sept (pndctx_insert (Atom Neg n) C) L K) (subp_ept_boxL Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (ept_boxL (LJFPS_bracketable_goal_ept H1) Hpe H1))
        | Some (right H1) => Some (right (fun H => H1 (ept_boxL_inv Hpe H)))
        | None            => None
        end ;

    search init (Sept C ((AndN B1 B2) :: L) K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpe := Permeable_neg (AndN B1 B2) (Neg_and B1 B2) in
        match search init (Sept (pndctx_insert (AndN B1 B2) C) L K) (subp_ept_boxL Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (ept_boxL (LJFPS_bracketable_goal_ept H1) Hpe H1))
        | Some (right H1) => Some (right (fun H => H1 (ept_boxL_inv Hpe H)))
        | None            => None
        end ;

    search init (Sept C ((Imp B1 B2) :: L) K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpe := Permeable_neg (Imp B1 B2) (Neg_imp B1 B2) in
        match search init (Sept (pndctx_insert (Imp B1 B2) C) L K) (subp_ept_boxL Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (ept_boxL (LJFPS_bracketable_goal_ept H1) Hpe H1))
        | Some (right H1) => Some (right (fun H => H1 (ept_boxL_inv Hpe H)))
        | None            => None
        end ;

    search init (Sept C (AndP B1 B2 :: L) K) Hsub stack Hstack_NoDup Hstack_sub 
    with search init (Sept C (B2 :: B1 :: L) K) (subp_ept_AndPL Hsub) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    => Some (left (ept_AndPL (LJFPS_bracketable_goal_ept H1) H1)) ;
        | Some (right H1)   => Some (right (fun H => H1 (ept_AndPL_inv H))) ;
        | None              => None
    } ;

    search init (Sept C (Or B1 B2 :: L) K) Hsub stack Hstack_NoDup Hstack_sub 
    with search init (Sept C (B1 :: L) K) (proj1 (subp_ept_OrL Hsub)) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    with search init (Sept C (B2 :: L) K) (proj2 (subp_ept_OrL Hsub)) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => Some (left (ept_OrL (LJFPS_bracketable_goal_ept H1) H1 H2)) ;
            | Some (right H2)   => Some (right (fun H => H2 (proj2 (ept_OrL_inv H)))) ;
            | None              => None
            }
        | Some (right H1)   => Some (right (fun H => H1 (proj1 (ept_OrL_inv H)))) ;
        | None              with search init (Sept C (B2 :: L) K) (proj2 (subp_ept_OrL Hsub)) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => None
            | Some (right H2)   => Some (right (fun H => H2 (proj2 (ept_OrL_inv H)))) ;
            | None              => None
            }
    } ;

    search init (Sept C (TT :: L) K) Hsub stack Hstack_NoDup Hstack_sub 
    with search init (Sept C L K) (subp_ept_TrueL Hsub) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    => Some (left (ept_TrueL (LJFPS_bracketable_goal_ept H1) H1)) ;
        | Some (right H1)   => Some (right (fun H => H1 (ept_TrueL_inv H))) ;
        | None              => None
    } ;

    search init (Sept C (FF :: L) K) Hsub stack Hstack_NoDup Hstack_sub
    with bracketable_dec K := {
        | left Hbr      => Some (left (ept_FalseL Hbr)) ;
        | right Hbr     => Some (right (fun H => Hbr (LJFPS_bracketable_goal_ept H)))
    } ;

    search init (Sbct C L (Atom Pos n)) Hsub stack Hstack_NoDup Hstack_sub := 
        let Hbr := Bracketable_pos (Atom Pos n) (Pos_atom n) in
        match search init (Sept C L (Atom Pos n)) (subp_bct_boxR Hbr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (bct_boxR Hbr H1))
        | Some (right H1) => Some (right (fun H => H1 (bct_boxR_inv Hbr H)))
        | None            => None
        end ;
    
    search init (Sbct C L (Atom Neg n)) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hbr := Bracketable_neg_atom (Atom Neg n) (Is_atom Neg n) (Neg_atom n) in
        match search init (Sept C L (Atom Neg n)) (subp_bct_boxR Hbr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (bct_boxR Hbr H1))
        | Some (right H1) => Some (right (fun H => H1 (bct_boxR_inv Hbr H)))
        | None            => None
        end ;

    search init (Sbct C L TT) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hbr := Bracketable_pos TT Pos_true in
        match search init (Sept C L TT) (subp_bct_boxR Hbr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (bct_boxR Hbr H1))
        | Some (right H1) => Some (right (fun H => H1 (bct_boxR_inv Hbr H)))
        | None            => None
        end ;

    search init (Sbct C L FF) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hbr := Bracketable_pos FF Pos_false in
        match search init (Sept C L FF) (subp_bct_boxR Hbr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (bct_boxR Hbr H1))
        | Some (right H1) => Some (right (fun H => H1 (bct_boxR_inv Hbr H)))
        | None            => None
        end ;

    search init (Sbct C L (AndP B1 B2)) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hbr := Bracketable_pos (AndP B1 B2) (Pos_and B1 B2) in
        match search init (Sept C L (AndP B1 B2)) (subp_bct_boxR Hbr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (bct_boxR Hbr H1))
        | Some (right H1) => Some (right (fun H => H1 (bct_boxR_inv Hbr H)))
        | None            => None
        end ;

    search init (Sbct C L (Or B1 B2)) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hbr := Bracketable_pos (Or B1 B2) (Pos_or B1 B2) in
        match search init (Sept C L (Or B1 B2)) (subp_bct_boxR Hbr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (bct_boxR Hbr H1))
        | Some (right H1) => Some (right (fun H => H1 (bct_boxR_inv Hbr H)))
        | None            => None
        end ;
    
    search init (Sbct C L (AndN B1 B2)) Hsub stack Hstack_NoDup Hstack_sub 
    with search init (Sbct C L B1) (proj1 (subp_bct_AndNR Hsub)) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    with search init (Sbct C L B2) (proj2 (subp_bct_AndNR Hsub)) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => Some (left (bct_AndNR H1 H2))
            | Some (right H2)   => Some (right (fun H => H2 (proj2 (bct_AndNR_inv H))))
            | None              => None
            }
        | Some (right H1)   => Some (right (fun H => H1 (proj1 (bct_AndNR_inv H))))
        | None              with search init (Sbct C L B2) (proj2 (subp_bct_AndNR Hsub)) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => None
            | Some (right H2)   => Some (right (fun H => H2 (proj2 (bct_AndNR_inv H))))
            | None              => None
            }
    } ;
    
    search init (Sbct C L (Imp B1 B2)) Hsub stack Hstack_NoDup Hstack_sub 
    with search init (Sbct C (B1 :: L) B2) (subp_bct_ImpR Hsub) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    => Some (left (bct_ImpR H1))
        | Some (right H1)   => Some (right (fun H => H1 (bct_ImpR_inv H)))
        | None              => None
    } ;

    search init (Slfc C (Atom Pos n) K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpos := Pos_atom n in
        match search init (Sept C ((Atom Pos n) :: nil) K) (subp_lfc_Rl Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)    => Some (left (lfc_Rl (LJFPS_bracketable_goal_ept H1) Hpos H1))
        | Some (right H1)   => Some (right (fun H => H1 (lfc_Rl_inv Hpos H)))
        | None              => None
        end ;

    search init (Slfc C TT K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpos := Pos_true in
        match search init (Sept C (TT :: nil) K) (subp_lfc_Rl Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (lfc_Rl (LJFPS_bracketable_goal_ept H1) Hpos H1))
        | Some (right H1) => Some (right (fun H => H1 (lfc_Rl_inv Hpos H)))
        | None            => None
        end ;

    search init (Slfc C FF K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpos := Pos_false in
        match search init (Sept C (FF :: nil) K) (subp_lfc_Rl Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (lfc_Rl (LJFPS_bracketable_goal_ept H1) Hpos H1))
        | Some (right H1) => Some (right (fun H => H1 (lfc_Rl_inv Hpos H)))
        | None            => None
        end ;

    search init (Slfc C (AndP B1 B2) K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpos := Pos_and B1 B2 in
        match search init (Sept C ((AndP B1 B2) :: nil) K) (subp_lfc_Rl Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (lfc_Rl (LJFPS_bracketable_goal_ept H1) Hpos H1))
        | Some (right H1) => Some (right (fun H => H1 (lfc_Rl_inv Hpos H)))
        | None            => None
        end ;

    search init (Slfc C (Or B1 B2) K) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hpos := Pos_or B1 B2 in
        match search init (Sept C ((Or B1 B2) :: nil) K) (subp_lfc_Rl Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (lfc_Rl (LJFPS_bracketable_goal_ept H1) Hpos H1))
        | Some (right H1) => Some (right (fun H => H1 (lfc_Rl_inv Hpos H)))
        | None            => None
        end ;

    search init (Slfc C (Atom Neg n) K) Hsub stack Hstack_NoDup Hstack_sub
    with o_eq_dec (Atom Neg n) K := {
        | left Heq  => Some (left
            (match Heq in (_ = K) return lfc C (Atom Neg n) K with
                | eq_refl => lfc_Il (Neg_atom n) (Is_atom Neg n)
                end)) ;
        | right Heq => Some (right (fun H => Heq (lfc_Il_NK_eq (Is_atom Neg n) (Neg_atom n) H)))
    } ;

    search init (Slfc C (AndN B1 B2) K) Hsub stack Hstack_NoDup Hstack_sub
    with search init (Slfc C B1 K) (subp_lfc_AndNL_1 Hsub) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    => Some (left (lfc_AndNL_1 (LJFPS_bracketable_goal_lfc H1) H1))
        | Some (right H1)   with search init (Slfc C B2 K) (subp_lfc_AndNL_2 Hsub) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => Some (left (lfc_AndNL_2 (LJFPS_bracketable_goal_lfc H2) H2))
            | Some (right H2)   => Some (right (fun H => match lfc_AndNL_inv H with
                | or_introl H3      => H1 H3
                | or_intror H3      => H2 H3
                end ))
            | None              => None
            }
        | None              with search init (Slfc C B2 K) (subp_lfc_AndNL_2 Hsub) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => Some (left (lfc_AndNL_2 (LJFPS_bracketable_goal_lfc H2) H2))
            | Some (right H2)   => None
            | None              => None                
            }
    } ;

    search init (Slfc C (Imp B1 B2) K) Hsub stack Hstack_NoDup Hstack_sub
    with search init (Srfc C B1) (proj1 (subp_lfc_ImpL Hsub)) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    with search init (Slfc C B2 K) (proj2 (subp_lfc_ImpL Hsub)) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => Some (left (lfc_ImpL (LJFPS_bracketable_goal_lfc H2) H1 H2))
            | Some (right H2)   => Some (right (fun H => H2 (proj2 (lfc_ImpL_inv H))))
            | None              => None
            }
        | Some (right H1)   => Some (right (fun H => H1 (proj1 (lfc_ImpL_inv H))))
        | None              with search init (Slfc C B2 K) (proj2 (subp_lfc_ImpL Hsub)) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => None
            | Some (right H2)   => Some (right (fun H => H2 (proj2 (lfc_ImpL_inv H))))
            | None              => None
            }
    } ;

    search init (Srfc C (Atom Neg n)) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hneg := Neg_atom n in 
        match search init (Sbct C nil (Atom Neg n)) (subp_rfc_Rr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)    => Some (left (rfc_Rr Hneg H1))
        | Some (right H1)   => Some (right (fun H => H1 (rfc_Rr_inv Hneg H)))
        | None              => None
        end ; 

    search init (Srfc C (AndN B1 B2)) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hneg := Neg_and B1 B2 in
        match search init (Sbct C nil (AndN B1 B2)) (subp_rfc_Rr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (rfc_Rr Hneg H1))
        | Some (right H1) => Some (right (fun H => H1 (rfc_Rr_inv Hneg H)))
        | None            => None
        end ;

    search init (Srfc C (Imp B1 B2)) Hsub stack Hstack_NoDup Hstack_sub :=
        let Hneg := Neg_imp B1 B2 in
        match search init (Sbct C nil (Imp B1 B2)) (subp_rfc_Rr Hsub) stack Hstack_NoDup Hstack_sub with
        | Some (left H1)  => Some (left (rfc_Rr Hneg H1))
        | Some (right H1) => Some (right (fun H => H1 (rfc_Rr_inv Hneg H)))
        | None            => None
        end ;

    search init (Srfc C (Atom Pos n)) Hsub stack Hstack_NoDup Hstack_sub
    with in_dec o_eq_dec (Atom Pos n) (pndctx_list C) := {
        | left Hin  => Some (left (rfc_Ir Hin (Pos_atom n) (Is_atom Pos n)))
        | right Hin => Some (right (fun H => Hin (rfc_Ir_inv (Pos_atom n) (Is_atom Pos n) H)))
    } ;

    search init (Srfc C (AndP B1 B2)) Hsub stack Hstack_NoDup Hstack_sub 
    with search init (Srfc C B1) (proj1 (subp_rfc_AndPR Hsub)) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    with search init (Srfc C B2) (proj2 (subp_rfc_AndPR Hsub)) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => Some (left (rfc_AndPR H1 H2))
            | Some (right H2)   => Some (right (fun H => H2 (proj2 (rfc_AndPR_inv H))))
            | None              => None
            }
        | Some (right H1)   => Some (right (fun H => H1 (proj1 (rfc_AndPR_inv H))))
        | None              with search init (Srfc C B2) (proj2 (subp_rfc_AndPR Hsub)) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => None
            | Some (right H2)   => Some (right (fun H => H2 (proj2 (rfc_AndPR_inv H))))
            | None              => None
            }
    } ;

    search init (Srfc C (Or B1 B2)) Hsub stack Hstack_NoDup Hstack_sub 
    with search init (Srfc C B1) (subp_rfc_OrR_1 Hsub) stack Hstack_NoDup Hstack_sub := {
        | Some (left H1)    => Some (left (rfc_OrR_1 H1))
        | Some (right H1)   with search init (Srfc C B2) (subp_rfc_OrR_2 Hsub) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => Some (left (rfc_OrR_2 H2))
            | Some (right H2)   => Some (right (fun H => match rfc_OrR_inv H with
                | or_introl H3  => H1 H3
                | or_intror H3  => H2 H3
                end ))
            | None              => None
            }
        | None              with search init (Srfc C B2) (subp_rfc_OrR_2 Hsub) stack Hstack_NoDup Hstack_sub := {
            | Some (left H2)    => Some (left (rfc_OrR_2 H2))
            | Some (right H2)   => None
            | None              => None
            }
    } ;

    search init (Srfc C TT) Hsub stack Hstack_NoDup Hstack_sub := Some (left (rfc_TrueR)) ;

    search init (Srfc C FF) Hsub stack Hstack_NoDup Hstack_sub := Some (right (rfc_FF_unprovable)).

Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    left. left.
    assert (subsequent (Sept C nil K) init). repeat split. apply H. apply H0. apply H1.
    specialize (stack_length_bound init C K H2 stack Hstack_NoDup Hstack_sub Hin) ; intro.
    lia.
Qed.
Next Obligation.
    left. left.
    assert (subsequent (Sept C nil K) init). repeat split. apply H. apply H0. apply H2. 
    specialize (stack_length_bound init C K H3 stack Hstack_NoDup Hstack_sub Hin) ; intro.
    lia.
Qed.
Next Obligation.
    left. left.
    assert (subsequent (Sept C nil K) init). repeat split. apply H. apply H0. apply H1. 
    specialize (stack_length_bound init C K H2 stack Hstack_NoDup Hstack_sub Hin) ; intro.
    lia.
Qed.
Next Obligation.
    left. left.
    assert (subsequent (Sept C nil K) init). repeat split. apply H. apply H0. apply H1. 
    specialize (stack_length_bound init C K H2 stack Hstack_NoDup Hstack_sub Hin) ; intro.
    lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    left. right. lia.
Qed.
Next Obligation.
    left. right. lia.
Qed.
Next Obligation.
    left. right. lia.
Qed.
Next Obligation.
    left. right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed. 
Next Obligation.
    left. right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.
Next Obligation.
    right. lia.
Qed.