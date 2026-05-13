From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic.


Inductive bct4 : sctx -> octx -> o -> Prop :=
| bct4_boxR :
  forall {C: sctx} {L: lctx} {D: o},
    bracketable D ->
    ept4 C L D ->
    bct4 C L D
| bct4_AndNR :
  forall {C: sctx} {L: lctx} {B1 B2: o},
    bct4 C L B1 ->
    bct4 C L B2 ->
    bct4 C L (AndN B1 B2)
| bct4_ImpR :
  forall {C: sctx} {L: lctx} {B1 B2: o},
    bct4 C (B1 :: L) B2 ->
    bct4 C L (Imp B1 B2) 
with ept4 : sctx -> octx -> o -> Prop :=
| ept4_Lf :
  forall {C: sctx} (N : o) {K : o},
    In N C ->
    bracketable K ->
    negative N ->
    lfc4 C N K ->
    ept4 C nil K
| ept4_Rf :
  forall {C: sctx} {P: o},
    positive P ->
    rfc4 C P ->
    ept4 C nil P 
| ept4_boxL :
  forall {C: sctx} {L L1: lctx} (B: o) {K: o},
    Permutation L (B :: L1) ->
    bracketable K ->
    permeable B ->
    ept4 (B :: C) L1 K ->
    ept4 C L K 
| ept4_AndPL :
  forall {C: sctx} {L L1: lctx} (B1 B2 : o) {K: o},
    Permutation L ((AndP B1 B2) :: L1) ->
    bracketable K ->
    ept4 C (B2 :: B1 :: L1) K ->
    ept4 C L K 
| ept4_OrL :
  forall {C: sctx} {L L1: lctx} (B1 B2 : o)  {K: o},
    Permutation L ((Or B1 B2) :: L1) ->
    bracketable K ->
    ept4 C (B1 :: L1) K ->
    ept4 C (B2 :: L1) K ->
    ept4 C L K 
| ept4_TrueL :
  forall {C: sctx} {L L1: lctx} {K: o},
    Permutation L (TT :: L1) ->
    bracketable K ->
    ept4 C L1 K ->
    ept4 C L K 
| ept4_FalseL :
  forall {C: sctx} {L: lctx} {K: o},
    In FF L ->
    bracketable K ->
    ept4 C L K 
with lfc4 : sctx -> o -> o -> Prop :=
| lfc4_Rl :
  forall {C : sctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    ept4 C (P :: nil) K ->
    lfc4 C P K
| lfc4_Il :
  forall {C: sctx} {N : o},
    negative N ->
    atomic N ->
    lfc4 C N N
| lfc4_AndNL_1 :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfc4 C B1 K ->
    lfc4 C (AndN B1 B2) K
| lfc4_AndNL_2 :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfc4 C B2 K ->
    lfc4 C (AndN B1 B2) K
| lfc4_ImpL :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfc4 C B1 ->
    lfc4 C B2 K ->
    lfc4 C (Imp B1 B2) K
with rfc4 : sctx -> o -> Prop :=
| rfc4_Rr :
  forall {C: sctx} {N: o},
    negative N ->
    bct4 C nil N ->
    rfc4 C N
| rfc4_Ir :
  forall {C: sctx} {P: o},
    In P C ->
    positive P ->
    atomic P ->
    rfc4 C P
| rfc4_AndPR :
  forall {C: sctx} {B1 B2: o},
    rfc4 C B1 ->
    rfc4 C B2 ->
    rfc4 C (AndP B1 B2)
| rfc4_OrR_1 :
  forall {C: sctx} {B1 B2: o},
    rfc4 C B1 ->
    rfc4 C (Or B1 B2)
| rfc4_OrR_2 :
  forall {C: sctx} {B1 B2: o},
    rfc4 C B2 ->
    rfc4 C (Or B1 B2)
| rfc4_TrueR :
  forall {C: sctx},
    rfc4 C TT
.
