From Stdlib Require Import List.

From LJF Require Import SharedLogic.

Inductive bctO : sctx -> octx -> o -> Prop :=
| bctO_boxR :
  forall {C: sctx} {L: octx} {D: o},
    bracketable D ->
    eptO C L D ->
    bctO C L D
| bctO_AndNR :
  forall {C: sctx} {L: octx} {B1 B2: o},
    bctO C L B1 ->
    bctO C L B2 ->
    bctO C L (AndN B1 B2)
| bctO_ImpR :
  forall {C: sctx} {L: octx} {B1 B2: o},
    bctO C (B1 :: L) B2 ->
    bctO C L (Imp B1 B2) 
with eptO : sctx -> octx -> o -> Prop :=
| eptO_Lf :
  forall {C: sctx} (N : o) {K : o},
    In N C ->
    bracketable K ->
    negative N ->
    lfcO C N K ->
    eptO C nil K
| eptO_Rf :
  forall {C: sctx} {P: o},
    positive P ->
    rfcO C P ->
    eptO C nil P 
| eptO_boxL :
  forall {C: sctx} {L: octx} (B: o) {K: o},
    bracketable K ->
    permeable B ->
    eptO (B :: C) L K ->
    eptO C (B :: L) K 
| eptO_AndPL :
  forall {C: sctx} {L: octx} (B1 B2 : o) {K: o},
    bracketable K ->
    eptO C (B2 :: B1 :: L) K ->
    eptO C ((AndP B1 B2) :: L) K 
| eptO_OrL :
  forall {C: sctx} {L: octx} (B1 B2 : o)  {K: o},
    bracketable K ->
    eptO C (B1 :: L) K ->
    eptO C (B2 :: L) K ->
    eptO C ((Or B1 B2) :: L) K 
| eptO_TrueL :
  forall {C: sctx} {L: octx} {K: o},
    bracketable K ->
    eptO C L K ->
    eptO C (TT :: L) K 
| eptO_FalseL :
  forall {C: sctx} {L: octx} {K: o},
    bracketable K ->
    eptO C (FF :: L) K 
with lfcO : sctx -> o -> o -> Prop :=
| lfcO_Rl :
  forall {C : sctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    eptO C (P :: nil) K ->
    lfcO C P K
| lfcO_Il :
  forall {C: sctx} {N : o},
    negative N ->
    atomic N ->
    lfcO C N N
| lfcO_AndNL_1 :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfcO C B1 K ->
    lfcO C (AndN B1 B2) K
| lfcO_AndNL_2 :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfcO C B2 K ->
    lfcO C (AndN B1 B2) K
| lfcO_ImpL :
  forall {C: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfcO C B1 ->
    lfcO C B2 K ->
    lfcO C (Imp B1 B2) K
with rfcO : sctx -> o -> Prop :=
| rfcO_Rr :
  forall {C: sctx} {N: o},
    negative N ->
    bctO C nil N ->
    rfcO C N
| rfcO_Ir :
  forall {C: sctx} {P: o},
    In P C ->
    positive P ->
    atomic P ->
    rfcO C P
| rfcO_AndPR :
  forall {C: sctx} {B1 B2: o},
    rfcO C B1 ->
    rfcO C B2 ->
    rfcO C (AndP B1 B2)
| rfcO_OrR_1 :
  forall {C: sctx} {B1 B2: o},
    rfcO C B1 ->
    rfcO C (Or B1 B2)
| rfcO_OrR_2 :
  forall {C: sctx} {B1 B2: o},
    rfcO C B2 ->
    rfcO C (Or B1 B2)
| rfcO_TrueR :
  forall {C: sctx},
    rfcO C TT
.
