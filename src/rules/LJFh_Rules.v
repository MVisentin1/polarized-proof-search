From Stdlib Require Import List Permutation SetoidList.
From LJF Require Import SharedLogic Pndctx.

Notation hist := (list (pndctx * o)).

Inductive bcth : hist -> pndctx -> octx -> o -> Prop :=
| bcth_boxR :
  forall {Hs: hist} {C: pndctx} {L: octx} {D: o},
    bracketable D ->
    epth Hs C L D ->
    bcth Hs C L D
| bcth_AndNR :
  forall {Hs: hist} {C: pndctx} {L: octx} {B1 B2: o},
    bcth Hs C L B1 ->
    bcth Hs C L B2 ->
    bcth Hs C L (AndN B1 B2)
| bcth_ImpR :
  forall {Hs: hist} {C: pndctx} {L: octx} {B1 B2: o},
    bcth Hs C (B1 :: L) B2 ->
    bcth Hs C L (Imp B1 B2)
with epth : hist -> pndctx -> octx -> o -> Prop :=
| epth_Lf :
  forall {Hs: hist} {C: pndctx} (N : o) {K : o},
    ~ InA pndctx_o_eq (C, K) Hs ->
    In N (pndctx_list C) ->
    bracketable K ->
    negative N ->
    lfch ((C, K) :: Hs) C N K ->
    epth Hs C nil K
| epth_Rf :
  forall {Hs: hist} {C: pndctx} {P: o},
    ~ InA pndctx_o_eq (C, P) Hs ->
    positive P ->
    rfch ((C, P) :: Hs) C P ->
    epth Hs C nil P
| epth_boxL :
  forall {Hs: hist} {C: pndctx} {L: octx} {B: o} {K: o},
    bracketable K ->
    permeable B ->
    epth Hs (pndctx_insert B C) L K ->
    epth Hs C (B :: L) K
| epth_AndPL :
  forall {Hs: hist} {C: pndctx} {L: octx} {B1 B2 : o} {K: o},
    bracketable K ->
    epth Hs C (B2 :: B1 :: L) K ->
    epth Hs C ((AndP B1 B2) :: L) K
| epth_OrL :
  forall {Hs: hist} {C: pndctx} {L: octx} {B1 B2 : o}  {K: o},
    bracketable K ->
    epth Hs C (B1 :: L) K ->
    epth Hs C (B2 :: L) K ->
    epth Hs C ((Or B1 B2) :: L) K
| epth_TrueL :
  forall {Hs: hist} {C: pndctx} {L: octx} {K: o},
    bracketable K ->
    epth Hs C L K ->
    epth Hs C (TT :: L) K
| epth_FalseL :
  forall {Hs: hist} {C: pndctx} {L: octx} {K: o},
    bracketable K ->
    epth Hs C (FF :: L) K
with lfch : hist -> pndctx -> o -> o -> Prop :=
| lfch_Rl :
  forall {Hs: hist} {C: pndctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    epth Hs C (P :: nil) K ->
    lfch Hs C P K
| lfch_Il :
  forall {Hs: hist} {C: pndctx} {N : o},
    negative N ->
    atomic N ->
    lfch Hs C N N
| lfch_AndNL_1 :
  forall {Hs: hist} {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfch Hs C B1 K ->
    lfch Hs C (AndN B1 B2) K
| lfch_AndNL_2 :
  forall {Hs: hist} {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfch Hs C B2 K ->
    lfch Hs C (AndN B1 B2) K
| lfch_ImpL :
  forall {Hs: hist} {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfch Hs C B1 ->
    lfch Hs C B2 K ->
    lfch Hs C (Imp B1 B2) K
with rfch : hist -> pndctx -> o -> Prop :=
| rfch_Rr :
  forall {Hs: hist} {C: pndctx} {N: o},
    negative N ->
    bcth Hs C nil N ->
    rfch Hs C N
| rfch_Ir :
  forall {Hs: hist} {C: pndctx} {P: o},
    In P (pndctx_list C) ->
    positive P ->
    atomic P ->
    rfch Hs C P
| rfch_AndPR :
  forall {Hs: hist} {C: pndctx} {B1 B2: o},
    rfch Hs C B1 ->
    rfch Hs C B2 ->
    rfch Hs C (AndP B1 B2)
| rfch_OrR_1 :
  forall {Hs: hist} {C: pndctx} {B1 B2: o},
    rfch Hs C B1 ->
    rfch Hs C (Or B1 B2)
| rfch_OrR_2 :
  forall {Hs: hist} {C: pndctx} {B1 B2: o},
    rfch Hs C B2 ->
    rfch Hs C (Or B1 B2)
| rfch_TrueR :
  forall {Hs: hist} {C: pndctx},
    rfch Hs C TT
.