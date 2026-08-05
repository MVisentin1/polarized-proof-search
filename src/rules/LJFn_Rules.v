From Stdlib Require Import List Permutation ProofIrrelevance.
From LJF Require Import SharedLogic Pndctx.

Inductive bctn : nat -> pndctx -> octx -> o -> Prop :=
| bctn_boxR :
  forall {n: nat} {C: pndctx} {L: octx} {D: o},
    bracketable D ->
    eptn n C L D ->
    bctn (S n) C L D
| bctn_AndNR :
  forall {n: nat} {C: pndctx} {L: octx} {B1 B2: o},
    bctn n C L B1 ->
    bctn n C L B2 ->
    bctn (S n) C L (AndN B1 B2)
| bctn_ImpR :
  forall {n: nat} {C: pndctx} {L: octx} {B1 B2: o},
    bctn n C (B1 :: L) B2 ->
    bctn (S n) C L (Imp B1 B2)
with eptn : nat -> pndctx -> octx -> o -> Prop :=
| eptn_Lf :
  forall {n: nat} {C: pndctx} (N : o) {K : o},
    In N (pndctx_list C) ->
    bracketable K ->
    negative N ->
    lfcn n C N K ->
    eptn (S n) C nil K
| eptn_Rf :
  forall {n: nat} {C: pndctx} {P: o},
    positive P ->
    rfcn n C P ->
    eptn (S n) C nil P
| eptn_boxL :
  forall {n: nat} {C: pndctx} {L: octx} {B: o} {K: o},
    bracketable K ->
    permeable B ->
    eptn n (pndctx_insert B C) L K ->
    eptn (S n) C (B :: L) K
| eptn_AndPL :
  forall {n: nat} {C: pndctx} {L: octx} {B1 B2 : o} {K: o},
    bracketable K ->
    eptn n C (B2 :: B1 :: L) K ->
    eptn (S n) C ((AndP B1 B2) :: L) K
| eptn_OrL :
  forall {n: nat} {C: pndctx} {L: octx} {B1 B2 : o}  {K: o},
    bracketable K ->
    eptn n C (B1 :: L) K ->
    eptn n C (B2 :: L) K ->
    eptn (S n) C ((Or B1 B2) :: L) K
| eptn_TrueL :
  forall {n: nat} {C: pndctx} {L: octx} {K: o},
    bracketable K ->
    eptn n C L K ->
    eptn (S n) C (TT :: L) K
| eptn_FalseL :
  forall {n: nat} {C: pndctx} {L: octx} {K: o},
    bracketable K ->
    eptn (S n) C (FF :: L) K
with lfcn : nat -> pndctx -> o -> o -> Prop :=
| lfcn_Rl :
  forall {n: nat} {C: pndctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    eptn n C (P :: nil) K ->
    lfcn (S n) C P K
| lfcn_Il :
  forall {n: nat} {C: pndctx} {N : o},
    negative N ->
    atomic N ->
    lfcn (S n) C N N
| lfcn_AndNL_1 :
  forall {n: nat} {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfcn n C B1 K ->
    lfcn (S n) C (AndN B1 B2) K
| lfcn_AndNL_2 :
  forall {n: nat} {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfcn n C B2 K ->
    lfcn (S n) C (AndN B1 B2) K
| lfcn_ImpL :
  forall {n: nat} {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfcn n C B1 ->
    lfcn n C B2 K ->
    lfcn (S n) C (Imp B1 B2) K
with rfcn : nat -> pndctx -> o -> Prop :=
| rfcn_Rr :
  forall {n: nat} {C: pndctx} {N: o},
    negative N ->
    bctn n C nil N ->
    rfcn (S n) C N
| rfcn_Ir :
  forall {n: nat} {C: pndctx} {P: o},
    In P (pndctx_list C) ->
    positive P ->
    atomic P ->
    rfcn (S n) C P
| rfcn_AndPR :
  forall {n: nat} {C: pndctx} {B1 B2: o},
    rfcn n C B1 ->
    rfcn n C B2 ->
    rfcn (S n) C (AndP B1 B2)
| rfcn_OrR_1 :
  forall {n: nat} {C: pndctx} {B1 B2: o},
    rfcn n C B1 ->
    rfcn (S n) C (Or B1 B2)
| rfcn_OrR_2 :
  forall {n: nat} {C: pndctx} {B1 B2: o},
    rfcn n C B2 ->
    rfcn (S n) C (Or B1 B2)
| rfcn_TrueR :
  forall {n: nat} {C: pndctx},
    rfcn (S n) C TT
.