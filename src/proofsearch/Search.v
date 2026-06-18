From Stdlib Require Import List Arith.PeanoNat Lia.
From LJF Require Import SharedLogic Decidability
    Predicates Subformula Pndctx LJFPS_Rules Sequents Measures LJFPS_Bracketable
    Termination_Measures LJFPS_Inversion.
From Equations Require Import Equations.

Equations try_Lf {C : pndctx} {K : o}
    (try_one : forall N, option ({lfc C N K} + {~ lfc C N K}))
    (negs : list o)
    (HAll : Forall (fun N => In N (pndctx_list C) /\ negative N) negs)
    : option ({ept C nil K} + {Forall (fun N => ~ lfc C N K) negs}) :=

    try_Lf try_one nil _ := Some (right (Forall_nil (fun N => ~ lfc C N K))) ;
    
    try_Lf try_one (N :: negs') HAll with try_one N := {
        | Some (left H1)   => Some (left (ept_Lf N (proj1 (Forall_inv HAll))
                              (LJFPS_bracketable_goal_lfc H1)
                              (proj2 (Forall_inv HAll)) H1))
        | Some (right H1 ) with try_Lf try_one negs' (Forall_inv_tail HAll) := {
            | Some (left H2)    => Some (left H2)
            | Some (right H2)   => Some (right (Forall_cons N H1 H2))
            | None              => None
            }
        | None             with try_Lf try_one negs' (Forall_inv_tail HAll) := {
            | Some (left H2)    => Some (left H2)
            | Some (right H2)   => None
            | None              => None
            }
        }
.

Lemma filter_neg_Forall : forall (C : pndctx),
    Forall (fun N => In N (pndctx_list C) /\ negative N)
           (filter negative_b (pndctx_list C)).
Proof.
  intros. apply Forall_forall. intros.
  apply filter_In in H. destruct H. split.
  - apply H.
  - apply negative_b_iff. apply H0. 
Qed.

Equations search 
    (initial S: sequent)  
    (visited : list (pndctx * o))
    (Hsub : subsequent S initial)
    (Hwf  : visited_wf initial visited)
    : option ({sequent_derivable S} + {~ sequent_derivable S})
    by wf
        (number_focus_decision initial - length visited, phase_ranking S, phase_measure S)
        (lexprod _ _ (lexprod _ _ lt lt) lt) :=
    
    search initial (Sept C nil K) visited with Exists_dec (visited_eq (C, K)) visited (visited_eq_dec (C, K)) := {
        | left Hexists  => None
        | right Hexists with positive_dec K := {
            | left PosK     with search initial (Srfc C K) ((C, K) :: visited) := {
                | Some (left H1)    => Some (left (ept_Rf PosK H1))
                | Some (right H1)   with try_Lf 
                        (fun N => search initial (Slfc C N K) ((C, K) :: visited))
                        (filter negative_b (pndctx_list C))
                        (filter_neg_Forall C) := {
                            | Some (left H2)    => Some (left H2)
                            | Some (right H2)   => Some (right (ept_nil_disproof_pos PosK H1 H2))
                            | None              => None
                            }
                | None              with try_Lf 
                        (fun N => search initial (Slfc C N K) ((C, K) :: visited))
                        (filter negative_b (pndctx_list C))
                        (filter_neg_Forall C) := {
                            | Some (left H2)    => Some (left H2)
                            | Some (right H2)   => None
                            | None              => None
                            }
                }
            | right PosK    with try_Lf
                    (fun N => search initial (Slfc C N K) ((C, K) :: visited))
                    (filter negative_b (pndctx_list C))
                    (filter_neg_Forall C) := {
                        | Some (left H2)    => Some (left H2)
                        | Some (right H2)   => Some (right (ept_nil_disproof_neg PosK H2))
                        | None              => None
                        }
            }
        } .
(*
    search initial (Sept C (B :: L) K) visited with permeable_dec B := {
        | left Pb   with search initial (Sept (pndctx_insert B C) L K) visited := {
            | Some (left H1)    => Some (left (ept_boxL (LJFPS_bracketable_goal_ept H1) Pb H1))
            | Some (right H1)   => Some (right (fun H => H1 (ept_boxL_inv Pb H)))
            | None              => None
            }
        | right PrB  with B := {
            | Atom Pos n    => False_rect _ (PrB (Permeable_pos_atom (Atom Pos n) (Is_atom Pos n) (Pos_atom n)))
            | Atom Neg n    => False_rect _ (PrB (Permeable_neg (Atom Neg n) (Neg_atom n)))
            | AndN B1 B2    => False_rect _ (PrB (Permeable_neg (AndN B1 B2) (Neg_and B1 B2)))
            | Imp B1 B2     => False_rect _ (PrB (Permeable_neg (Imp B1 B2) (Neg_imp B1 B2)))
            | TT            with search initial (Sept C L K) visited := {
                | Some (left H1)    => Some (left (ept_TrueL (LJFPS_bracketable_goal_ept H1) H1))
                | Some (right H1)   => Some (right (fun H => H1 (ept_TrueL_inv H)))
                | None              => None
                }
            | FF            with bracketable_dec K := {
                | left BrK  => Some (left (ept_FalseL BrK))
                | right BrK => Some (right (fun H => BrK (LJFPS_bracketable_goal_ept H)))
                }
            | AndP B1 B2    with search initial (Sept C (B2 :: B1 :: L) K) visited := {
                | Some (left H1)    => Some (left (ept_AndPL (LJFPS_bracketable_goal_ept H1) H1))
                | Some (right H1)   => Some (right (fun H => H1 (ept_AndPL_inv H)))
                | None              => None
                }
            | Or B1 B2      with search initial (Sept C (B1 :: L) K) visited := {
                | Some (left H1)    with search initial (Sept C (B2 :: L) K) visited := {
                    | Some (left H2)    => Some (left (ept_OrL (LJFPS_bracketable_goal_ept H1) H1 H2))
                    | Some (right H2)   => Some (right (fun H => H2 (proj2 (ept_OrL_inv H))))
                    | None              => None
                    }
                | Some (right H1)   => Some (right (fun H => H1 (proj1 (ept_OrL_inv H))))
                | None              => None
                }
            }
        } ; 

    search initial (Sbct C L K) visited with bracketable_dec K := {
        | left BrK  with search initial (Sept C L K) visited := {
            | Some (left H1)    => Some (left (bct_boxR BrK H1))
            | Some (right H1)   => Some (right (fun H => H1 (bct_boxR_inv BrK H)))
            | None              => None
            }
        | right BrK with K := {
            | Atom Pos n => False_rect _ (BrK (Bracketable_pos (Atom Pos n) (Pos_atom n)))
            | Atom Neg n => False_rect _ (BrK (Bracketable_neg_atom (Atom Neg n) (Is_atom Neg n) (Neg_atom n)))
            | TT         => False_rect _ (BrK (Bracketable_pos TT Pos_true))
            | FF         => False_rect _ (BrK (Bracketable_pos FF Pos_false))
            | AndP B1 B2 => False_rect _ (BrK (Bracketable_pos (AndP B1 B2) (Pos_and B1 B2)))
            | Or B1 B2   => False_rect _ (BrK (Bracketable_pos (Or B1 B2) (Pos_or B1 B2)))
            | AndN B1 B2 with search initial (Sbct C L B1) visited := {
                | Some (left H1)    with search initial (Sbct C L B2) visited := {
                    | Some (left H2)    => Some (left (bct_AndNR H1 H2))
                    | Some (right H2)   => Some (right (fun H => H2 (proj2 (bct_AndNR_inv H))))
                    | None              => None
                    }
                | Some (right H1)   => Some (right (fun H => H1 (proj1 (bct_AndNR_inv H))))
                | None              => None
                }
            | Imp B1 B2 with search initial (Sbct C (B1 :: L) B2) visited := {
                | Some (left H1)    => Some (left (bct_ImpR H1))
                | Some (right H1)   => Some (right (fun H => H1 (bct_ImpR_inv H)))
                | None              => None  
                }
            }
        } ; 
        
    search initial (Slfc C N K) visited with positive_dec N := {
        | left PN   with search initial (Sept C (N :: nil) K) visited := {
            | Some (left H1)    => Some (left (lfc_Rl (LJFPS_bracketable_goal_ept H1) PN H1))
            | Some (right H1)   => Some (right (fun H => H1 (lfc_Rl_inv PN H)))
            | None              => None
            }
        | right PN  with N := {
            | Atom Pos n => False_rect _ (PN (Pos_atom n))
            | TT         => False_rect _ (PN Pos_true)
            | FF         => False_rect _ (PN Pos_false)
            | AndP B1 B2 => False_rect _ (PN (Pos_and B1 B2))
            | Or B1 B2   => False_rect _ (PN (Pos_or B1 B2))
            | Atom Neg n with o_eq_dec (Atom Neg n) K := {
                | left EK   => Some (left (eq_ind (Atom Neg n)
                                (fun x => lfc C (Atom Neg n) x)
                                (lfc_Il (Neg_atom n) (Is_atom Neg n))
                                K EK))
                | right EK  => Some (right (fun H => EK (lfc_Il_NK_eq (Is_atom Neg n) (Neg_atom n) H)))
                }
            | AndN B1 B2 with search initial (Slfc C B1 K) visited := {
                | Some (left H1)    => Some (left (lfc_AndNL_1 (LJFPS_bracketable_goal_lfc H1) H1))
                | Some (right H1)   with search initial (Slfc C B2 K) visited := {
                    | Some (left H2)    => Some (left (lfc_AndNL_2 (LJFPS_bracketable_goal_lfc H2) H2))
                    | Some (right H2)   => Some (right (fun H => match lfc_AndNL_inv H with
                        | or_introl HO  => H1 HO
                        | or_intror HO  => H2 HO
                        end))
                    | None              => None
                    }
                | None              with search initial (Slfc C B2 K) visited := {
                    | Some (left H2)    => Some (left (lfc_AndNL_2 (LJFPS_bracketable_goal_lfc H2) H2))
                    | Some (right H2)   => None 
                    | None              => None
                    }
                }
            | Imp B1 B2 with search initial (Srfc C B1) visited := {
                | Some (left H1)    with search initial (Slfc C B2 K) visited := {
                    | Some (left H2)    => Some (left (lfc_ImpL (LJFPS_bracketable_goal_lfc H2) H1 H2))
                    | Some (right H2)   => Some (right (fun H => H2 (proj2 (lfc_ImpL_inv H))))
                    | None              => None
                    }
                | Some (right H1)   => Some (right (fun H => H1 (proj1 (lfc_ImpL_inv H))))
                | None              with search initial (Slfc C B2 K) visited := {
                    | Some (left H2)    => None
                    | Some (right H2)   => Some (right (fun H => H2 (proj2 (lfc_ImpL_inv H))))
                    | None              => None
                    }
                }
            }
        } ;

    search initial (Srfc C K) visited with negative_dec K := {
        | left NK with search initial (Sbct C nil K) visited := {
            | Some (left H1)    => Some (left (rfc_Rr NK H1))
            | Some (right H1)   => Some (right (fun H => H1 (rfc_Rr_inv NK H)))
            | None              => None
            }
        | right NK with K := {
            | Atom Neg n    => False_rect _ (NK (Neg_atom n))
            | AndN B1 B2    => False_rect _ (NK (Neg_and B1 B2))
            | Imp B1 B2     => False_rect _ (NK (Neg_imp B1 B2))
            | Atom Pos n    with in_dec o_eq_dec (Atom Pos n) (pndctx_list C) := {
                | left IP   => Some (left (rfc_Ir IP (Pos_atom n) (Is_atom Pos n)))
                | right IP  => Some (right (fun H => IP (rfc_Ir_inv (Pos_atom n) (Is_atom Pos n) H)))
                }
            | TT            => Some (left rfc_TrueR)
            | FF            => Some (right rfc_FF_unprovable)
            | AndP B1 B2    with search initial (Srfc C B1) visited := {
                | Some (left H1)    with search initial (Srfc C B2) visited := {
                    | Some (left H2)    => Some (left (rfc_AndPR H1 H2))
                    | Some (right H2)   => Some (right (fun H => H2 (proj2 (rfc_AndPR_inv H))))
                    | None              => None
                    }
                | Some (right H1)  => Some (right (fun H => H1 (proj1 (rfc_AndPR_inv H))))
                | None              with search initial (Srfc C B2) visited := {
                    | Some (left H2)    => None
                    | Some (right H2)   => Some (right (fun H => H2 (proj2 (rfc_AndPR_inv H))))
                    | None              => None
                    }
                }
            | Or B1 B2      with search initial (Srfc C B1) visited := {
                | Some (left H1)    => Some (left (rfc_OrR_1 H1))
                | Some (right H1)   with search initial (Srfc C B2) visited := {
                    | Some (left H2)    => Some (left (rfc_OrR_2 H2))
                    | Some (right H2)   => Some (right (fun H => match rfc_OrR_inv H with 
                        | or_introl HO  => H1 HO
                        | or_intror HO  => H2 HO
                        end))
                    | None              => None
                    }
                | None              with search initial (Srfc C B2) visited := {
                    | Some (left H2)    => Some (left (rfc_OrR_2 H2))
                    | Some (right H2)   => None
                    | None              => None
                    }
                }
            }
        } .

Next Obligation.
    right. apply Nat.lt_succ_r. apply Nat.le_add_r.
Qed.
Next Obligation.
    right. apply Nat.lt_succ_r. apply Nat.le_add_l.
Qed.
Next Obligation.
    right. apply Nat.lt_succ_r. apply Nat.le_add_l.
Qed.


*)