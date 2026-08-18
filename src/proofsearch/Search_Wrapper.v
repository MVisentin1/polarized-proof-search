From Stdlib Require Import List SetoidList.
From LJF Require Import Decidability Sequents Search_Procedure LJFPS_Bracketable ProofTerms.

Definition try_decide_sequent  (seq : sequent) : option ({p : pterm | verify p seq} + ~ sequent_derivable seq) :=
  match seq as s return option ({p : pterm | verify p s} + ~ sequent_derivable s) with
  | Sbct C L K => search (Sbct C L K) (Sbct C L K) (subsequent_refl (Sbct C L K) I) nil (NoDupA_nil _) (Forall_nil _)
  | Srfc C K   => search (Srfc C K) (Srfc C K) (subsequent_refl (Srfc C K) I) nil (NoDupA_nil _) (Forall_nil _)
  | Sept C L K =>
      match bracketable_dec K with
      | left Hbr  => search (Sept C L K) (Sept C L K) (subsequent_refl (Sept C L K) Hbr) nil (NoDupA_nil _) (Forall_nil _)
      | right Hbr => Some (inr (fun H => Hbr (LJFPS_bracketable_goal_ept H)))
      end
  | Slfc C N K =>
      match bracketable_dec K with
      | left Hbr  => search (Slfc C N K) (Slfc C N K) (subsequent_refl (Slfc C N K) Hbr) nil (NoDupA_nil _) (Forall_nil _)
      | right Hbr => Some (inr (fun H => Hbr (LJFPS_bracketable_goal_lfc H)))
      end
  end.