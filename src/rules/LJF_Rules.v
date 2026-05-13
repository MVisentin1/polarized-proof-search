From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic.

Variant state : Type :=
  | Bracketed : state
  | Unbracketed : state
.

Inductive ufcL : sctx -> octx -> o -> state -> Prop :=
| ufcL_Lf :
  forall {C: sctx} (N : o) {K : o},
    In N C ->
    bracketable K ->
    negative N ->
    lfcL C N K ->
    ufcL C nil K Bracketed
| ufcL_Rf :
  forall {C: sctx} {P: o},
    positive P ->
    rfcL C P ->
    ufcL C nil P Bracketed
| ufcL_boxL :
  forall {C: sctx} {L L1: lctx} (B: o) {K: o},
    Permutation L (B :: L1) ->
    bracketable K ->
    permeable B ->
    ufcL (B :: C) L1 K Bracketed ->
    ufcL C L K Bracketed
| ufcL_boxL_star :
  forall {C: sctx} {L L1: lctx} (B: o) {K: o},
    Permutation L (B :: L1) ->
    permeable B ->
    ufcL (B :: C) L1 K Unbracketed ->
    ufcL C L K Unbracketed
| ufcL_boxR :
  forall {C: sctx} {L: lctx} {D: o},
    bracketable D ->
    ufcL C L D Bracketed ->
    ufcL C L D Unbracketed
| ufcL_AndPL :
  forall {C: sctx} {L L1: lctx} (B1 B2 : o) {K: o},
    Permutation L ((AndP B1 B2) :: L1) ->
    bracketable K ->
    ufcL C (B2 :: B1 :: L1) K Bracketed ->
    ufcL C L K Bracketed
| ufcL_AndPL_star :
  forall {C: sctx} {L L1: lctx} (B1 B2 : o) {K: o},
    Permutation L ((AndP B1 B2) :: L1) ->
    ufcL C (B2 :: B1 :: L1) K Unbracketed ->
    ufcL C L K Unbracketed
| ufcL_AndNR :
  forall {C: sctx} {L: lctx} {B1 B2: o},
    ufcL C L B1 Unbracketed ->
    ufcL C L B2 Unbracketed->
    ufcL C L (AndN B1 B2) Unbracketed
| ufcL_OrL :
  forall {C: sctx} {L L1: lctx} (B1 B2 : o)  {K: o},
    Permutation L ((Or B1 B2) :: L1) ->
    bracketable K ->
    ufcL C (B1 :: L1) K Bracketed ->
    ufcL C (B2 :: L1) K Bracketed ->
    ufcL C L K Bracketed
| ufcL_OrL_star :
  forall {C: sctx} {L L1: lctx} (B1 B2 : o)  {K: o},
    Permutation L ((Or B1 B2) :: L1) ->
    ufcL C (B1 :: L1) K Unbracketed ->
    ufcL C (B2 :: L1) K Unbracketed ->
    ufcL C L K Unbracketed
| ufcL_ImpR :
  forall {C: sctx} {L: lctx} {B1 B2: o},
    ufcL C (B1 :: L) B2 Unbracketed ->
    ufcL C L (Imp B1 B2) Unbracketed
| ufcL_TrueL :
  forall {C: sctx} {L L1: lctx} {K: o},
    Permutation L (TT :: L1) ->
    bracketable K ->
    ufcL C L1 K Bracketed ->
    ufcL C L K Bracketed
| ufcL_TrueL_star :
  forall {C: sctx} {L L1: lctx} {K: o},
    Permutation L (TT :: L1) ->
    ufcL C L1 K Unbracketed ->
    ufcL C L K Unbracketed
| ufcL_FalseL :
  forall {C: sctx} {L: lctx} {K: o},
    In FF L ->
    bracketable K ->
    ufcL C L K Bracketed
| ufcL_FalseL_star :
  forall {C: sctx} {L: lctx} {K: o},
    In FF L ->
    ufcL C L K Unbracketed
with lfcL : sctx -> o -> o -> Prop :=
| lfcL_Rl :
  forall {C : sctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    ufcL C (P :: nil) K Bracketed ->
    lfcL C P K
| lfcL_Il :
  forall {C: sctx} {N : o},
    negative N ->
    atomic N ->
    lfcL C N N
| lfcL_AndNL_1 :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfcL C B1 K ->
    lfcL C (AndN B1 B2) K
| lfcL_AndNL_2 :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfcL C B2 K ->
    lfcL C (AndN B1 B2) K
| lfcL_ImpL :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfcL C B1 ->
    lfcL C B2 K ->
    lfcL C (Imp B1 B2) K
with rfcL : sctx -> o -> Prop :=
| rfcL_Rr :
  forall {C: sctx} {N: o},
    negative N ->
    ufcL C nil N Unbracketed ->
    rfcL C N
| rfcL_Ir :
  forall {C: sctx} {P: o},
    In P C ->
    positive P ->
    atomic P ->
    rfcL C P
| rfcL_AndPR :
  forall {C: sctx} {B1 B2: o},
    rfcL C B1 ->
    rfcL C B2 ->
    rfcL C (AndP B1 B2)
| rfcL_OrR_1 :
  forall {C: sctx} {B1 B2: o},
    rfcL C B1 ->
    rfcL C (Or B1 B2)
| rfcL_OrR_2 :
  forall {C: sctx} {B1 B2: o},
    rfcL C B2 ->
    rfcL C (Or B1 B2)
| rfcL_TrueR :
  forall {C: sctx},
    rfcL C TT
.
