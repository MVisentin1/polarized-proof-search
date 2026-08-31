From Stdlib Require Import List PeanoNat Wf_nat.
From LJF Require Import SharedLogic Predicates Decidability Sequents Pndctx LJFn_Rules LJFn_Inversion LJFn_Bracketable LJFn_Monotone.
From Equations Require Import Equations.


Definition min_height_eptn (m: nat) (C: pndctx) (K: o) :=
    eptn m C nil K /\ forall (n: nat), n < m -> ~ (eptn n C nil K).

Variant nsequent : Type :=
| Sbctn : nat -> pndctx -> octx -> o -> nsequent
| Septn : nat -> pndctx -> octx -> o -> nsequent
| Slfcn : nat -> pndctx -> o -> o -> nsequent
| Srfcn : nat -> pndctx -> o -> nsequent
.

Definition nsequent_derivable (seq : nsequent) : Prop :=
    match seq with
    | Sbctn n C L K => bctn n C L K
    | Septn n C L K => eptn n C L K
    | Slfcn n C N K => lfcn n C N K
    | Srfcn n C K   => rfcn n C K
    end
.

Definition nsequent_height (seq : nsequent) : nat :=
    match seq with
    | Sbctn n _ _ _ => n
    | Septn n _ _ _ => n
    | Slfcn n _ _ _ => n
    | Srfcn n _ _   => n
    end
.

Definition nsequent_map (n: nat) (seq : sequent) : nsequent :=
    match seq with
    | Sbct C L K => Sbctn n C L K
    | Sept C L K => Septn n C L K
    | Slfc C N K => Slfcn n C N K
    | Srfc C K   => Srfcn n C K
    end
.

Definition min_height (m: nat) (seq : sequent) :=
    nsequent_derivable (nsequent_map m seq)  /\ forall (n: nat), n < m -> ~ nsequent_derivable (nsequent_map n seq).

Lemma LJFn_unprovable_at_0_height :
    (forall (C: pndctx)  (L: octx)(K: o), ~ bctn 0 C L K) /\
    (forall (C: pndctx) (L: octx) (K: o), ~ eptn 0 C L K) /\
    (forall (C: pndctx) (N K: o), ~ lfcn 0 C N K) /\
    (forall (C: pndctx) (K: o), ~ rfcn 0 C K ).
Proof. repeat split ; intros ; intro ; inversion H. Qed.

Lemma LJFn_unprovable_at_0_height_bctn : forall (C: pndctx) (L: octx) (K: o), ~ bctn 0 C L K.
Proof. destruct LJFn_unprovable_at_0_height as [H [H0 [H1 H2]]]. apply H. Qed.

Lemma LJFn_unprovable_at_0_height_eptn : forall (C: pndctx) (L: octx) (K: o), ~ eptn 0 C L K.
Proof. destruct LJFn_unprovable_at_0_height as [H [H0 [H1 H2]]]. apply H0. Qed.

Lemma LJFn_unprovable_at_0_height_lfcn : forall (C: pndctx) (N K: o), ~ lfcn 0 C N K.
Proof. destruct LJFn_unprovable_at_0_height as [H [H0 [H1 H2]]]. apply H1. Qed.

Lemma LJFn_unprovable_at_0_height_rfcn : forall (C: pndctx) (K: o), ~ rfcn 0 C K.
Proof. destruct LJFn_unprovable_at_0_height as [H [H0 [H1 H2]]]. apply H2. Qed.

Equations LJFn_try_Lf {n : nat} {C: pndctx} {K: o}
    (try_N : forall N, In N (pndctx_list C) -> {nsequent_derivable (Slfcn n C N K)} + {~ nsequent_derivable (Slfcn n C N K)})
    (neg_ctx : list o)
    (H_Forall : Forall (fun N => In N (pndctx_list C) /\ negative N) neg_ctx)
    : {nsequent_derivable (Septn (S n) C nil K)} + {Forall (fun N => ~ nsequent_derivable (Slfcn n C N K)) neg_ctx} :=

    LJFn_try_Lf try_N nil _     := right (Forall_nil (fun N => ~ nsequent_derivable (Slfcn n C N K))) ;

    LJFn_try_Lf try_N (N :: rest) H_Forall 
    with try_N N (proj1 (Forall_inv H_Forall)) := {
        | left H1   => left (eptn_Lf N (proj1 (Forall_inv H_Forall)) (LJFn_bracketable_goal_lfc H1) (proj2 (Forall_inv H_Forall)) H1)
        | right H1  with LJFn_try_Lf try_N rest (Forall_inv_tail H_Forall) := {
            | left H2   => left H2
            | right H2  => right (Forall_cons N H1 H2)
        } 
    }
.

Lemma LJFn_filter_neg_forall (C : pndctx) :
  Forall (fun N => In N (pndctx_list C) /\ negative N) (filter negative_b (pndctx_list C)).
Proof.
  apply Forall_forall. intros N HN.
  apply filter_In in HN as [Hin Hb].
  split.
  - apply Hin.
  - apply negative_b_iff. apply Hb.
Qed.

Equations LJFn_decider (seq : nsequent) : {nsequent_derivable seq} + {~ nsequent_derivable seq}
    by wf (nsequent_height seq) lt :=
    LJFn_decider (Sbctn 0 C L K)    := right (LJFn_unprovable_at_0_height_bctn C L K) ;
    LJFn_decider (Septn 0 C L K)    := right (LJFn_unprovable_at_0_height_eptn C L K) ;
    LJFn_decider (Slfcn 0 C N K)    := right (LJFn_unprovable_at_0_height_lfcn C N K) ;
    LJFn_decider (Srfcn 0 C K)      := right (LJFn_unprovable_at_0_height_rfcn C K) ;
    
    (*--------------------------------------------------------------------------*)
    (*---------------------------------- bct -----------------------------------*)
    (*--------------------------------------------------------------------------*)

    LJFn_decider (Sbctn (S n) C L (Atom Pos m)) :=
        let Hbr := Bracketable_pos (Atom Pos m) (Pos_atom m) in 
        match LJFn_decider (Septn n C L (Atom Pos m)) with 
        | left H1    => left (bctn_boxR Hbr H1) 
        | right H1   => right (fun H => H1 (bctn_boxR_inv Hbr H))
        end ;

    LJFn_decider (Sbctn (S n) C L (Atom Neg m)) :=
        let Hbr := Bracketable_neg_atom (Atom Neg m) (Is_atom Neg m) (Neg_atom m) in
        match LJFn_decider (Septn n C L (Atom Neg m)) with 
        | left H1    => left (bctn_boxR Hbr H1) 
        | right H1   => right (fun H => H1 (bctn_boxR_inv Hbr H))
        end ;

    LJFn_decider (Sbctn (S n) C L TT) :=
        let Hbr := Bracketable_pos TT Pos_true in
        match LJFn_decider (Septn n C L TT) with 
        | left H1    => left (bctn_boxR Hbr H1) 
        | right H1   => right (fun H => H1 (bctn_boxR_inv Hbr H))
        end ;

    LJFn_decider (Sbctn (S n) C L FF) :=
        let Hbr := Bracketable_pos FF Pos_false in
        match LJFn_decider (Septn n C L FF) with 
        | left H1    => left (bctn_boxR Hbr H1) 
        | right H1   => right (fun H => H1 (bctn_boxR_inv Hbr H))
        end ;

    LJFn_decider (Sbctn (S n) C L (AndP B1 B2)) :=
        let Hbr := Bracketable_pos (AndP B1 B2) (Pos_and B1 B2) in
        match LJFn_decider (Septn n C L (AndP B1 B2)) with 
        | left H1    => left (bctn_boxR Hbr H1) 
        | right H1   => right (fun H => H1 (bctn_boxR_inv Hbr H))
        end ;

    LJFn_decider (Sbctn (S n) C L (Or B1 B2)) :=
        let Hbr := Bracketable_pos (Or B1 B2) (Pos_or B1 B2) in
        match LJFn_decider (Septn n C L (Or B1 B2)) with 
        | left H1    => left (bctn_boxR Hbr H1) 
        | right H1   => right (fun H => H1 (bctn_boxR_inv Hbr H))
        end ;

    LJFn_decider (Sbctn (S n) C L (AndN B1 B2)) 
    with LJFn_decider (Sbctn n C L B1) := {
        | left H1   with LJFn_decider (Sbctn n C L B2) := {
            | left H2   => left (bctn_AndNR H1 H2)
            | right H2  => right (fun H => H2 (proj2 (bctn_AndNR_inv H)))
        }
        | right H1  => right (fun H => H1 (proj1 (bctn_AndNR_inv H)))
    } ;

    LJFn_decider (Sbctn (S n) C L (Imp B1 B2)) 
    with LJFn_decider (Sbctn n C (B1 :: L) B2) := {
        | left H1   => left (bctn_ImpR H1)
        | right H1  => right (fun H => H1 (bctn_ImpR_inv H))
    } ;

    (*--------------------------------------------------------------------------*)
    (*---------------------------------- ept nil -------------------------------*)
    (*--------------------------------------------------------------------------*)

    LJFn_decider (Septn (S n) C nil K) 
    with positive_dec K := {
        | left Hpos     with LJFn_decider (Srfcn n C K) := {
            | left H1   => left (eptn_Rf Hpos H1)
            | right H1  with LJFn_try_Lf
                (fun N (Hin : In N (pndctx_list C)) => LJFn_decider (Slfcn n C N K))
                (filter negative_b (pndctx_list C))
                (LJFn_filter_neg_forall C) := {
                    | left H2   => left H2
                    | right H2  => right (eptn_nil_disproof_pos Hpos H1 H2)
                }   
        }
        | right Hpos    with LJFn_try_Lf
            (fun N (Hin : In N (pndctx_list C)) => LJFn_decider (Slfcn n C N K))
            (filter negative_b (pndctx_list C))
            (LJFn_filter_neg_forall C) := {
                | left H1   => left H1
                | right H1  => right (eptn_nil_disproof_neg Hpos H1)
            }
    } ;
    (*--------------------------------------------------------------------------*)
    (*---------------------------------- ept :: --------------------------------*)
    (*--------------------------------------------------------------------------*)

    LJFn_decider (Septn (S n) C ((Atom Pos m) :: L) K) := 
        let Hpe := Permeable_pos_atom (Atom Pos m) (Is_atom Pos m) (Pos_atom m) in
        match LJFn_decider (Septn n (pndctx_insert (Atom Pos m) C) L K) with
        | left H1   => left (eptn_boxL (LJFn_bracketable_goal_ept H1) Hpe H1)
        | right H1  => right (fun H => H1 (eptn_boxL_inv Hpe H))
        end ;
    
    LJFn_decider (Septn (S n) C ((Atom Neg m) :: L) K) := 
        let Hpe := Permeable_neg (Atom Neg m) (Neg_atom m) in
        match LJFn_decider (Septn n (pndctx_insert (Atom Neg m) C) L K) with
        | left H1   => left (eptn_boxL (LJFn_bracketable_goal_ept H1) Hpe H1)
        | right H1  => right (fun H => H1 (eptn_boxL_inv Hpe H))
        end ;    
    
    LJFn_decider (Septn (S n) C ((AndN B1 B2) :: L) K) := 
        let Hpe := Permeable_neg (AndN B1 B2) (Neg_and B1 B2) in
        match LJFn_decider (Septn n (pndctx_insert (AndN B1 B2) C) L K) with
        | left H1   => left (eptn_boxL (LJFn_bracketable_goal_ept H1) Hpe H1)
        | right H1  => right (fun H => H1 (eptn_boxL_inv Hpe H))
        end ;   

    LJFn_decider (Septn (S n) C ((Imp B1 B2) :: L) K) := 
        let Hpe := Permeable_neg (Imp B1 B2) (Neg_imp B1 B2) in
        match LJFn_decider (Septn n (pndctx_insert (Imp B1 B2) C) L K) with
        | left H1   => left (eptn_boxL (LJFn_bracketable_goal_ept H1) Hpe H1)
        | right H1  => right (fun H => H1 (eptn_boxL_inv Hpe H))
        end ;
    
    LJFn_decider (Septn (S n) C (TT :: L) K) 
    with LJFn_decider (Septn n C L K) := {
        | left H1   => left (eptn_TrueL (LJFn_bracketable_goal_ept H1) H1)
        | right H1  => right (fun H => H1 (eptn_TrueL_inv H))
    } ;

    LJFn_decider (Septn (S n) C (FF :: L) K) 
    with bracketable_dec K := {
        | left H1   => left (eptn_FalseL n H1)
        | right H1  => right (fun H => H1 (LJFn_bracketable_goal_ept H))
    } ;
    
    LJFn_decider (Septn (S n) C ((AndP B1 B2) :: L) K) 
    with LJFn_decider (Septn n C (B2 :: B1 :: L) K) := {
        | left H1   => left (eptn_AndPL (LJFn_bracketable_goal_ept H1) H1)
        | right H1  => right (fun H => H1 (eptn_AndPL_inv H))
    } ;

    LJFn_decider (Septn (S n) C ((Or B1 B2) :: L) K) 
    with LJFn_decider (Septn n C (B1 :: L) K) := {
        | left H1   with LJFn_decider (Septn n C (B2 :: L) K) := {
            | left H2   => left (eptn_OrL (LJFn_bracketable_goal_ept H1) H1 H2)
            | right H2  => right (fun H => H2 (proj2 (eptn_OrL_inv H)))
        }
        | right H1  => right (fun H => H1 (proj1 (eptn_OrL_inv H)))
    } ;

    (*--------------------------------------------------------------------------*)
    (*---------------------------------- lfc -----------------------------------*)
    (*--------------------------------------------------------------------------*)

    LJFn_decider (Slfcn (S n) C (Atom Pos m) K) := 
        let Hpos := Pos_atom m in
        match LJFn_decider (Septn n C ((Atom Pos m) :: nil) K) with 
        | left H1   => left (lfcn_Rl (LJFn_bracketable_goal_ept H1) Hpos H1)
        | right H1  => right (fun H => H1 (lfcn_Rl_inv Hpos H))
        end ;
    
    LJFn_decider (Slfcn (S n) C TT K) := 
        let Hpos := Pos_true in
        match LJFn_decider (Septn n C (TT :: nil) K) with 
        | left H1   => left (lfcn_Rl (LJFn_bracketable_goal_ept H1) Hpos H1)
        | right H1  => right (fun H => H1 (lfcn_Rl_inv Hpos H))
        end ;
    
    LJFn_decider (Slfcn (S n) C FF K) := 
        let Hpos := Pos_false in
        match LJFn_decider (Septn n C (FF :: nil) K) with 
        | left H1   => left (lfcn_Rl (LJFn_bracketable_goal_ept H1) Hpos H1)
        | right H1  => right (fun H => H1 (lfcn_Rl_inv Hpos H))
        end ;

    LJFn_decider (Slfcn (S n) C (AndP B1 B2) K) := 
        let Hpos := Pos_and B1 B2 in
        match LJFn_decider (Septn n C ((AndP B1 B2) :: nil) K) with 
        | left H1   => left (lfcn_Rl (LJFn_bracketable_goal_ept H1) Hpos H1)
        | right H1  => right (fun H => H1 (lfcn_Rl_inv Hpos H))
        end ;

    LJFn_decider (Slfcn (S n) C (Or B1 B2) K) := 
        let Hpos := Pos_or B1 B2 in
        match LJFn_decider (Septn n C ((Or B1 B2) :: nil) K) with 
        | left H1   => left (lfcn_Rl (LJFn_bracketable_goal_ept H1) Hpos H1)
        | right H1  => right (fun H => H1 (lfcn_Rl_inv Hpos H))
        end ;

    LJFn_decider (Slfcn (S n) C (Atom Neg m) K)
    with o_eq_dec (Atom Neg m) K := {
        | left H1   => left (match H1 in (_ = k) return lfcn (S n) C (Atom Neg m) k with
                             | eq_refl => lfcn_Il n (Neg_atom m) (Is_atom Neg m)
                             end)
        | right H1  => right (fun H => H1 (lfcn_Il_NK_eq (Is_atom Neg m) (Neg_atom m) H))
    } ;

    LJFn_decider (Slfcn (S n) C (AndN B1 B2) K)
    with LJFn_decider (Slfcn n C B1 K) := {
        | left H1   => left (lfcn_AndNL_1 (LJFn_bracketable_goal_lfc H1) H1)
        | right H1  with LJFn_decider (Slfcn n C B2 K) := {
            | left H2   => left (lfcn_AndNL_2 (LJFn_bracketable_goal_lfc H2) H2)
            | right H2  => right (fun H => match lfcn_AndNL_inv H with 
                | or_introl H3  => H1 H3
                | or_intror H3  => H2 H3
                end)
        }
    } ;

    LJFn_decider (Slfcn (S n) C (Imp B1 B2) K)
    with LJFn_decider (Srfcn n C B1) := {
        | left H1   with LJFn_decider (Slfcn n C B2 K) := {
            | left H2   => left (lfcn_ImpL (LJFn_bracketable_goal_lfc H2) H1 H2)
            | right H2  => right (fun H => H2 (proj2 (lfcn_ImpL_inv H)))
        }
        | right H1  => right (fun H => H1 (proj1 (lfcn_ImpL_inv H)))
    } ;

    (*--------------------------------------------------------------------------*)
    (*---------------------------------- rfc -----------------------------------*)
    (*--------------------------------------------------------------------------*)

    LJFn_decider (Srfcn (S n) C (Atom Neg m)) := 
        let Hneg := Neg_atom m in
        match LJFn_decider (Sbctn n C nil (Atom Neg m)) with 
        | left H1   => left (rfcn_Rr Hneg H1)
        | right H1  => right (fun H => H1 (rfcn_Rr_inv Hneg H))
        end ;

    LJFn_decider (Srfcn (S n) C (AndN B1 B2)) := 
        let Hneg := Neg_and B1 B2 in
        match LJFn_decider (Sbctn n C nil (AndN B1 B2)) with 
        | left H1   => left (rfcn_Rr Hneg H1)
        | right H1  => right (fun H => H1 (rfcn_Rr_inv Hneg H))
        end ;

    LJFn_decider (Srfcn (S n) C (Imp B1 B2)) := 
        let Hneg := Neg_imp B1 B2 in
        match LJFn_decider (Sbctn n C nil (Imp B1 B2)) with 
        | left H1   => left (rfcn_Rr Hneg H1)
        | right H1  => right (fun H => H1 (rfcn_Rr_inv Hneg H))
        end ;
    
    LJFn_decider (Srfcn (S n) C (Atom Pos m)) 
    with in_dec o_eq_dec (Atom Pos m) (pndctx_list C) := {
        | left H1   => left (rfcn_Ir n H1 (Pos_atom m) (Is_atom Pos m))
        | right H1  => right (fun H => H1 (rfcn_Ir_inv (Pos_atom m) (Is_atom Pos m) H))
    } ;

    LJFn_decider (Srfcn (S n) C TT) := left (rfcn_TrueR n) ;

    LJFn_decider (Srfcn (S n) C FF) := right (rfcn_FF_unprovable) ;

    LJFn_decider (Srfcn (S n) C (AndP B1 B2)) 
    with LJFn_decider (Srfcn n C B1) := {
        | left H1   with LJFn_decider (Srfcn n C B2) := {
            | left H2   => left (rfcn_AndPR H1 H2)
            | right H2  => right (fun H => H2 (proj2 (rfcn_AndPR_inv H)))
        }
        | right H1  => right (fun H => H1 (proj1 (rfcn_AndPR_inv H)))
    } ;

    LJFn_decider (Srfcn (S n) C (Or B1 B2)) 
    with LJFn_decider (Srfcn n C B1) := {
        | left H1   => left (rfcn_OrR_1 H1)
        | right H1  with LJFn_decider (Srfcn n C B2) := {
            | left H2   => left (rfcn_OrR_2 H2)
            | right H2  => right (fun H => match rfcn_OrR_inv H with 
                | or_introl H3  => H1 H3
                | or_intror H3  => H2 H3
                end )
        }
    }.

Lemma nsequent_derivable_monotone : forall (m n : nat) (seq : sequent),
    m <= n ->
    nsequent_derivable (nsequent_map m seq) ->
    nsequent_derivable (nsequent_map n seq).
Proof.
    intros m n seq Hmn H. destruct seq ; simpl in *.
    - exact (LJFn_monotone_bctn H Hmn).
    - exact (LJFn_monotone_eptn H Hmn).
    - exact (LJFn_monotone_lfcn H Hmn).
    - exact (LJFn_monotone_rfcn H Hmn).
Qed.

Equations LJFn_find_min_height (m: nat) (seq : sequent)
    (Hd : nsequent_derivable (nsequent_map m seq)) : {n: nat | n <= m /\ min_height n seq}
    by wf m lt :=

    LJFn_find_min_height 0 seq Hd :=
        False_rect _
          (match seq as s return nsequent_derivable (nsequent_map 0 s) -> False with
           | Sbct C L K => fun h => LJFn_unprovable_at_0_height_bctn C L K h
           | Sept C L K => fun h => LJFn_unprovable_at_0_height_eptn C L K h
           | Slfc C N K => fun h => LJFn_unprovable_at_0_height_lfcn C N K h
           | Srfc C K   => fun h => LJFn_unprovable_at_0_height_rfcn C K h
           end Hd) ;

    LJFn_find_min_height (S m) seq Hd with LJFn_decider (nsequent_map m seq) := {
        | left H1   with LJFn_find_min_height m seq H1 := {
            | exist _ n (conj Hle Hmin) => exist _ n (conj (le_S n m Hle) Hmin)
        }
        | right H1  =>
            exist _ (S m)
              (conj (le_n (S m))
                    (conj Hd
                          (fun n Hn Hderiv =>
                             H1 (nsequent_derivable_monotone n m seq (le_S_n n m Hn) Hderiv))))
    }
.


Lemma min_height_exists : forall (m: nat) (C: pndctx) (K: o),
  eptn m C nil K -> exists (n: nat), n <= m /\ min_height_eptn n C K.
Proof.
    intros m C K H. destruct (LJFn_find_min_height m (Sept C nil K) H).
    eexists x. apply a.
Qed.
