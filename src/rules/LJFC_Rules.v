From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic.

Definition ndctx := list o.
Definition ndctx_insert (A : o) (C : ndctx) : ndctx :=
  if in_dec o_eq_dec A C then C else A :: C.

Lemma ndctx_insert_nodup :
  forall {A: o} {C: ndctx},
  NoDup C ->
  NoDup (ndctx_insert A C).
Proof.
  intros. unfold ndctx_insert. destruct (in_dec o_eq_dec A C).
  - apply H.
  - apply NoDup_cons. apply n. apply H.
Qed.

Inductive bctC : ndctx -> octx -> o -> Prop :=
| bctC_boxR :
  forall {C: ndctx} {L: octx} {D: o},
    NoDup C ->
    bracketable D ->
    eptC C L D ->
    bctC C L D
| bctC_AndNR :
  forall {C: ndctx} {L: octx} {B1 B2: o},
    NoDup C ->
    bctC C L B1 ->
    bctC C L B2 ->
    bctC C L (AndN B1 B2)
| bctC_ImpR :
  forall {C: ndctx} {L: octx} {B1 B2: o},
    NoDup C ->
    bctC C (B1 :: L) B2 ->
    bctC C L (Imp B1 B2) 
with eptC : ndctx -> octx -> o -> Prop :=
| eptC_Lf :
  forall {C: ndctx} (N : o) {K : o},
    NoDup C ->
    In N C ->
    bracketable K ->
    negative N ->
    lfcC C N K ->
    eptC C nil K
| eptC_Rf :
  forall {C: ndctx} {P: o},
    NoDup C ->
    positive P ->
    rfcC C P ->
    eptC C nil P 
| eptC_boxL :
  forall {C: ndctx} {L: octx} (B: o) {K: o},
    NoDup C ->
    bracketable K ->
    permeable B ->
    eptC (ndctx_insert B C) L K ->
    eptC C (B :: L) K 
| eptC_AndPL :
  forall {C: ndctx} {L: octx} (B1 B2 : o) {K: o},
    NoDup C ->
    bracketable K ->
    eptC C (B2 :: B1 :: L) K ->
    eptC C ((AndP B1 B2) :: L) K 
| eptC_OrL :
  forall {C: ndctx} {L: octx} (B1 B2 : o)  {K: o},
    NoDup C ->
    bracketable K ->
    eptC C (B1 :: L) K ->
    eptC C (B2 :: L) K ->
    eptC C ((Or B1 B2) :: L) K 
| eptC_TrueL :
  forall {C: ndctx} {L: octx} {K: o},
    NoDup C ->
    bracketable K ->
    eptC C L K ->
    eptC C (TT :: L) K 
| eptC_FalseL :
  forall {C: ndctx} {L: octx} {K: o},
    NoDup C ->
    bracketable K ->
    eptC C (FF :: L) K 
with lfcC : ndctx -> o -> o -> Prop :=
| lfcC_Rl :
  forall {C : ndctx} {P : o}  {K : o},
    NoDup C ->
    bracketable K ->
    positive P ->
    eptC C (P :: nil) K ->
    lfcC C P K
| lfcC_Il :
  forall {C: ndctx} {N : o},
    NoDup C ->
    negative N ->
    atomic N ->
    lfcC C N N
| lfcC_AndNL_1 :
  forall {C: ndctx} {B1 B2 : o}  {K : o},
    NoDup C ->
    bracketable K ->
    lfcC C B1 K ->
    lfcC C (AndN B1 B2) K
| lfcC_AndNL_2 :
  forall {C: ndctx} {B1 B2 : o}  {K : o},
    NoDup C ->
    bracketable K ->
    lfcC C B2 K ->
    lfcC C (AndN B1 B2) K
| lfcC_ImpL :
  forall {C: ndctx} {B1 B2 : o}  {K : o},
    NoDup C ->
    bracketable K ->
    rfcC C B1 ->
    lfcC C B2 K ->
    lfcC C (Imp B1 B2) K
with rfcC : ndctx -> o -> Prop :=
| rfcC_Rr :
  forall {C: ndctx} {N: o},
    NoDup C ->
    negative N ->
    bctC C nil N ->
    rfcC C N
| rfcC_Ir :
  forall {C: ndctx} {P: o},
    NoDup C ->
    In P C ->
    positive P ->
    atomic P ->
    rfcC C P
| rfcC_AndPR :
  forall {C: ndctx} {B1 B2: o},
    NoDup C ->
    rfcC C B1 ->
    rfcC C B2 ->
    rfcC C (AndP B1 B2)
| rfcC_OrR_1 :
  forall {C: ndctx} {B1 B2: o},
    NoDup C ->
    rfcC C B1 ->
    rfcC C (Or B1 B2)
| rfcC_OrR_2 :
  forall {C: ndctx} {B1 B2: o},
    NoDup C ->
    rfcC C B2 ->
    rfcC C (Or B1 B2)
| rfcC_TrueR :
  forall {C: ndctx},
    NoDup C ->
    rfcC C TT
.
