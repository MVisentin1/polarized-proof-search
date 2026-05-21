From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic.

Inductive bct : sctx -> octx -> o -> Prop :=
| bct_boxR :
  forall {C: sctx} {L: octx} {D: o},
    bracketable D ->
    ept C L D ->
    bct C L D
| bct_AndNR :
  forall {C: sctx} {L: octx} {B1 B2: o},
    bct C L B1 ->
    bct C L B2 ->
    bct C L (AndN B1 B2)
| bct_ImpR :
  forall {C: sctx} {L: octx} {B1 B2: o},
    bct C (B1 :: L) B2 ->
    bct C L (Imp B1 B2) 
with ept : sctx -> octx -> o -> Prop :=
| ept_Lf :
  forall {C: sctx} (N : o) {K : o},
    In N C ->
    bracketable K ->
    negative N ->
    lfc C N K ->
    ept C nil K
| ept_Rf :
  forall {C: sctx} {P: o},
    positive P ->
    rfc C P ->
    ept C nil P 
| ept_boxL :
  forall {C: sctx} {L: octx} (B: o) {K: o},
    bracketable K ->
    permeable B ->
    ept (B :: C) L K ->
    ept C (B :: L) K 
| ept_AndPL :
  forall {C: sctx} {L: octx} (B1 B2 : o) {K: o},
    bracketable K ->
    ept C (B2 :: B1 :: L) K ->
    ept C ((AndP B1 B2) :: L) K 
| ept_OrL :
  forall {C: sctx} {L: octx} (B1 B2 : o)  {K: o},
    bracketable K ->
    ept C (B1 :: L) K ->
    ept C (B2 :: L) K ->
    ept C ((Or B1 B2) :: L) K 
| ept_TrueL :
  forall {C: sctx} {L: octx} {K: o},
    bracketable K ->
    ept C L K ->
    ept C (TT :: L) K 
| ept_FalseL :
  forall {C: sctx} {L: octx} {K: o},
    bracketable K ->
    ept C (FF :: L) K 
with lfc : sctx -> o -> o -> Prop :=
| lfc_Rl :
  forall {C : sctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    ept C (P :: nil) K ->
    lfc C P K
| lfc_Il :
  forall {C: sctx} {N : o},
    negative N ->
    atomic N ->
    lfc C N N
| lfc_AndNL_1 :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfc C B1 K ->
    lfc C (AndN B1 B2) K
| lfc_AndNL_2 :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfc C B2 K ->
    lfc C (AndN B1 B2) K
| lfc_ImpL :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfc C B1 ->
    lfc C B2 K ->
    lfc C (Imp B1 B2) K
with rfc : sctx -> o -> Prop :=
| rfc_Rr :
  forall {C: sctx} {N: o},
    negative N ->
    bct C nil N ->
    rfc C N
| rfc_Ir :
  forall {C: sctx} {P: o},
    In P C ->
    positive P ->
    atomic P ->
    rfc C P
| rfc_AndPR :
  forall {C: sctx} {B1 B2: o},
    rfc C B1 ->
    rfc C B2 ->
    rfc C (AndP B1 B2)
| rfc_OrR_1 :
  forall {C: sctx} {B1 B2: o},
    rfc C B1 ->
    rfc C (Or B1 B2)
| rfc_OrR_2 :
  forall {C: sctx} {B1 B2: o},
    rfc C B2 ->
    rfc C (Or B1 B2)
| rfc_TrueR :
  forall {C: sctx},
    rfc C TT
.
