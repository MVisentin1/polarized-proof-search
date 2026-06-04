From Stdlib Require Import List Permutation ProofIrrelevance.
From LJF Require Import SharedLogic Pndctx.

Inductive bct : pndctx -> octx -> o -> Prop :=
| bct_boxR :
  forall {C: pndctx} {L: octx} {D: o},
    bracketable D ->
    ept C L D ->
    bct C L D
| bct_AndNR :
  forall {C: pndctx} {L: octx} {B1 B2: o},
    bct C L B1 ->
    bct C L B2 ->
    bct C L (AndN B1 B2)
| bct_ImpR :
  forall {C: pndctx} {L: octx} {B1 B2: o},
    bct C (B1 :: L) B2 ->
    bct C L (Imp B1 B2)
with ept : pndctx -> octx -> o -> Prop :=
| ept_Lf :
  forall {C: pndctx} (N : o) {K : o},
    In N (pndctx_list C) ->
    bracketable K ->
    negative N ->
    lfc C N K ->
    ept C nil K
| ept_Rf :
  forall {C: pndctx} {P: o},
    positive P ->
    rfc C P ->
    ept C nil P
| ept_boxL :
  forall {C: pndctx} {L: octx} (B: o) {K: o},
    bracketable K ->
    permeable B ->
    ept (pndctx_insert B C) L K ->
    ept C (B :: L) K
| ept_AndPL :
  forall {C: pndctx} {L: octx} (B1 B2 : o) {K: o},
    bracketable K ->
    ept C (B2 :: B1 :: L) K ->
    ept C ((AndP B1 B2) :: L) K
| ept_OrL :
  forall {C: pndctx} {L: octx} (B1 B2 : o)  {K: o},
    bracketable K ->
    ept C (B1 :: L) K ->
    ept C (B2 :: L) K ->
    ept C ((Or B1 B2) :: L) K
| ept_TrueL :
  forall {C: pndctx} {L: octx} {K: o},
    bracketable K ->
    ept C L K ->
    ept C (TT :: L) K
| ept_FalseL :
  forall {C: pndctx} {L: octx} {K: o},
    bracketable K ->
    ept C (FF :: L) K
with lfc : pndctx -> o -> o -> Prop :=
| lfc_Rl :
  forall {C : pndctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    ept C (P :: nil) K ->
    lfc C P K
| lfc_Il :
  forall {C: pndctx} {N : o},
    negative N ->
    atomic N ->
    lfc C N N
| lfc_AndNL_1 :
  forall {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfc C B1 K ->
    lfc C (AndN B1 B2) K
| lfc_AndNL_2 :
  forall {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfc C B2 K ->
    lfc C (AndN B1 B2) K
| lfc_ImpL :
  forall {C: pndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfc C B1 ->
    lfc C B2 K ->
    lfc C (Imp B1 B2) K
with rfc : pndctx -> o -> Prop :=
| rfc_Rr :
  forall {C: pndctx} {N: o},
    negative N ->
    bct C nil N ->
    rfc C N
| rfc_Ir :
  forall {C: pndctx} {P: o},
    In P (pndctx_list C) ->
    positive P ->
    atomic P ->
    rfc C P
| rfc_AndPR :
  forall {C: pndctx} {B1 B2: o},
    rfc C B1 ->
    rfc C B2 ->
    rfc C (AndP B1 B2)
| rfc_OrR_1 :
  forall {C: pndctx} {B1 B2: o},
    rfc C B1 ->
    rfc C (Or B1 B2)
| rfc_OrR_2 :
  forall {C: pndctx} {B1 B2: o},
    rfc C B2 ->
    rfc C (Or B1 B2)
| rfc_TrueR :
  forall {C: pndctx},
    rfc C TT
.