From Stdlib Require Import List.

From CARVe Require Import contexts.list.
From CARVe Require Import algebras.structural.


From LJF Require Import SharedLogic.

(* structural context -> ordered linear context -> right side formula*)
Inductive bct : sctx -> octx -> o -> Prop :=
| bct_R_box :
  forall {S: sctx} {O: octx} {D: o},
    bracketable D ->
    ept S O D->
    bct S O D
| bct_R_AndN :
  forall {S: sctx} {O: octx} {B1 B2: o},
    bct S O B1 ->
    bct S O B2 ->
    bct S O (AndN B1 B2)
| bct_R_Impl :
  forall {S : sctx} {O: octx} {B1 B2: o},
    bct S (B1 :: O) B2 ->
    bct S O (Impl B1 B2)
(* structural context -> ordered linear context -> right side formula*)
with ept : sctx -> octx -> o -> Prop := 
| ept_L_f :
  forall {S: sctx} (N: o) {K: o},
    bracketable K ->
    has_entry S (N, tt) ->
    negative N ->
    lfc S N K ->
    ept S nil K
| ept_R_f :
  forall {S: sctx} {P: o},
    positive P ->
    rfc S P ->
    ept S nil P
| ept_L_box :
  forall {S: sctx} {O: octx} {B : o} {K : o},
    bracketable K ->
    permeable B ->
    ept ((B, tt) :: S) O K ->
    ept S (B :: O) K
| ept_L_AndP :
  forall {S: sctx} {O: octx} {B1 B2 : o} {K: o},
    bracketable K ->
    ept S (B2 :: (B1 :: O)) K ->
    ept S ((AndP B1 B2) :: O) K
| ept_L_Or :
  forall {S: sctx} {O: octx} {B1 B2 : o}  {K: o},
    bracketable K ->
    ept S (B1 :: O) K ->
    ept S (B2 :: O) K ->
    ept S ((Or B1 B2) :: O) K
| ept_L_True :
  forall {S: sctx} {O: octx}  {K: o},
    bracketable K ->
    ept S O K ->
    ept S (TT :: O) K
| ept_L_False :
  forall {S: sctx} {O: octx} {K: o},
    bracketable K ->
    ept S (FF :: O) K
(* structural context -> focused formula -> right side formula*)
with lfc : sctx -> o -> o -> Prop :=
| lfc_R_l :
  forall {S : sctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    ept S (P :: nil) K ->
    lfc S P K
| lfc_I_l :
  forall {S: sctx} {N : o},
    negative N ->
    atomic N ->
    lfc S N N
| lfc_L_AndN_1 :
  forall {S: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfc S B1 K ->
    lfc S (AndN B1 B2) K
| lfc_L_AndN_2 :
  forall {S: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfc S B2 K ->
    lfc S (AndN B1 B2) K
| lfc_L_Impl :
  forall {S: sctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfc S B1 ->
    lfc S B2 K ->
    lfc S (Impl B1 B2) K
(* structural context -> focused formula*)
with rfc : sctx -> o -> Prop :=
| rfc_R_r :
  forall {S: sctx} {N: o},
    negative N ->
    bct S nil N ->
    rfc S N
| rfc_I_r :
  forall {S: sctx} {P: o},
    positive P ->
    atomic P ->
    has_entry S (P, tt) ->
    rfc S P
| rfc_R_AndP :
  forall {S: sctx} {B1 B2: o},
    rfc S B1 ->
    rfc S B2 ->
    rfc S (AndP B1 B2)
| rfc_R_Or_1 :
  forall {S: sctx} {B1 B2: o},
    rfc S B1 ->
    rfc S (Or B1 B2)
| rfc_R_Or_2 :
  forall {S: sctx} {B1 B2: o},
    rfc S B2 ->
    rfc S (Or B1 B2)
| rfc_R_True :
  forall {S: sctx}, 
    rfc S TT
.