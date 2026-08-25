
type __ = Obj.t

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

val sig_of_sig2 : 'a1 sig2 -> 'a1



module Nat :
 sig
 end

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val forall_dec : ('a1 -> bool) -> 'a1 list -> bool

type polarity =
| Pos
| Neg

type o =
| Atom of polarity * int
| TT
| FF
| AndP of o * o
| AndN of o * o
| Or of o * o
| Imp of o * o

val polarity_eq_dec : polarity -> polarity -> bool

val o_eq_dec : o -> o -> bool

val permeable_dec : o -> bool

val bracketable_dec : o -> bool

val positive_dec : o -> bool

val negative_b : o -> bool

val inA_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val equivlistA_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val raw_insert : o -> o list -> o list

type pndctx = o list sig2

val pndctx_list : pndctx -> o list

val pndctx_insert : o -> pndctx -> pndctx

val pndctx_set_eq_dec : pndctx -> pndctx -> bool

val pndctx_o_eq_dec : (pndctx * o) -> (pndctx * o) -> bool

type sequent =
| Sbct of pndctx * o list * o
| Sept of pndctx * o list * o
| Slfc of pndctx * o * o
| Srfc of pndctx * o

type pterm =
| Pbct_boxR of pterm
| Pbct_AndNR of pterm * pterm
| Pbct_ImpR of pterm
| Pept_Lf of o * pterm
| Pept_Rf of pterm
| Pept_boxL of pterm
| Pept_AndPL of pterm
| Pept_OrL of pterm * pterm
| Pept_TrueL of pterm
| Pept_FalseL
| Plfc_Rl of pterm
| Plfc_Il
| Plfc_AndNL_1 of pterm
| Plfc_AndNL_2 of pterm
| Plfc_ImpL of pterm * pterm
| Prfc_Rr of pterm
| Prfc_Ir
| Prfc_AndPR of pterm * pterm
| Prfc_OrR_1 of pterm
| Prfc_OrR_2 of pterm
| Prfc_TrueR

val try_Lf :
  pndctx -> o -> (o -> __ -> (pterm, __) sum option) -> o list -> (pterm, __)
  sum option

val try_Lf_wrapper :
  pndctx -> o -> (o -> __ -> (pterm, __) sum option) -> (pterm, __) sum option

val search : sequent -> sequent -> (pndctx * o) list -> (pterm, __) sum option

val try_decide_sequent : sequent -> (pterm, __) sum option
