
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

(** val sig_of_sig2 : 'a1 sig2 -> 'a1 **)

let sig_of_sig2 x =
  x



module Nat =
 struct
 end

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val forall_dec : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forall_dec pdec = function
| [] -> true
| y :: l0 -> if forall_dec pdec l0 then pdec y else false

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

(** val polarity_eq_dec : polarity -> polarity -> bool **)

let polarity_eq_dec p1 p2 =
  match p1 with
  | Pos -> (match p2 with
            | Pos -> true
            | Neg -> false)
  | Neg -> (match p2 with
            | Pos -> false
            | Neg -> true)

(** val o_eq_dec : o -> o -> bool **)

let rec o_eq_dec o0 x =
  match o0 with
  | Atom (p, n) ->
    (match x with
     | Atom (p0, n0) -> if polarity_eq_dec p p0 then (=) n n0 else false
     | _ -> false)
  | TT -> (match x with
           | TT -> true
           | _ -> false)
  | FF -> (match x with
           | FF -> true
           | _ -> false)
  | AndP (o1, o2) ->
    (match x with
     | AndP (o3, o4) -> if o_eq_dec o1 o3 then o_eq_dec o2 o4 else false
     | _ -> false)
  | AndN (o1, o2) ->
    (match x with
     | AndN (o3, o4) -> if o_eq_dec o1 o3 then o_eq_dec o2 o4 else false
     | _ -> false)
  | Or (o1, o2) ->
    (match x with
     | Or (o3, o4) -> if o_eq_dec o1 o3 then o_eq_dec o2 o4 else false
     | _ -> false)
  | Imp (o1, o2) ->
    (match x with
     | Imp (o3, o4) -> if o_eq_dec o1 o3 then o_eq_dec o2 o4 else false
     | _ -> false)

(** val permeable_dec : o -> bool **)

let permeable_dec = function
| Atom (_, _) -> true
| AndN (_, _) -> true
| Imp (_, _) -> true
| _ -> false

(** val bracketable_dec : o -> bool **)

let bracketable_dec = function
| AndN (_, _) -> false
| Imp (_, _) -> false
| _ -> true

(** val positive_dec : o -> bool **)

let positive_dec = function
| Atom (p, _) -> (match p with
                  | Pos -> true
                  | Neg -> false)
| AndN (_, _) -> false
| Imp (_, _) -> false
| _ -> true

(** val negative_b : o -> bool **)

let negative_b = function
| Atom (p, _) -> (match p with
                  | Pos -> false
                  | Neg -> true)
| AndN (_, _) -> true
| Imp (_, _) -> true
| _ -> false

(** val inA_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec inA_dec eqA_dec x = function
| [] -> false
| y :: l0 -> let s = eqA_dec x y in if s then true else inA_dec eqA_dec x l0

(** val equivlistA_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let equivlistA_dec eqA_dec l l' =
  let s = forall_dec (fun a -> inA_dec eqA_dec a l') l in
  if s then forall_dec (fun a -> inA_dec eqA_dec a l) l' else false

(** val raw_insert : o -> o list -> o list **)

let raw_insert a c =
  if permeable_dec a then if in_dec o_eq_dec a c then c else a :: c else c

type pndctx = o list sig2

(** val pndctx_list : pndctx -> o list **)

let pndctx_list =
  sig_of_sig2

(** val pndctx_insert : o -> pndctx -> pndctx **)

let pndctx_insert a c =
  raw_insert a (pndctx_list c)

(** val pndctx_set_eq_dec : pndctx -> pndctx -> bool **)

let pndctx_set_eq_dec c1 c2 =
  equivlistA_dec o_eq_dec (pndctx_list c1) (pndctx_list c2)

(** val pndctx_o_eq_dec : (pndctx * o) -> (pndctx * o) -> bool **)

let pndctx_o_eq_dec p1 p2 =
  let (p, o0) = p1 in
  let (p0, o1) = p2 in
  let s = pndctx_set_eq_dec p p0 in if s then o_eq_dec o0 o1 else false

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

(** val try_Lf :
    pndctx -> o -> (o -> __ -> (pterm, __) sum option) -> o list -> (pterm,
    __) sum option **)

let rec try_Lf c k try_N = function
| [] -> Some (Inr __)
| o0 :: l ->
  (match try_N o0 __ with
   | Some s ->
     (match s with
      | Inl s0 -> Some (Inl (Pept_Lf (o0, s0)))
      | Inr _ ->
        (match try_Lf c k try_N l with
         | Some s0 ->
           (match s0 with
            | Inl s1 -> Some (Inl s1)
            | Inr _ -> Some (Inr __))
         | None -> None))
   | None ->
     (match try_Lf c k try_N l with
      | Some s -> (match s with
                   | Inl s0 -> Some (Inl s0)
                   | Inr _ -> None)
      | None -> None))

(** val try_Lf_wrapper :
    pndctx -> o -> (o -> __ -> (pterm, __) sum option) -> (pterm, __) sum
    option **)

let try_Lf_wrapper c k try_N =
  try_Lf c k try_N (filter negative_b (pndctx_list c))

(** val search :
    sequent -> sequent -> (pndctx * o) list -> (pterm, __) sum option **)

let search a a0 a1 =
  let rec fix_F x =
    let init = let pr1,_ = x in pr1 in
    let stack =
      let pr1,_ = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
      in
      pr1
    in
    let search0 = fun a2 a3 a4 ->
      let y = a2,(a3,(__,(a4,(__,__)))) in (fun _ -> fix_F y)
    in
    (match let pr1,_ = let _,pr2 = x in pr2 in pr1 with
     | Sbct (p, l, o0) ->
       (match o0 with
        | AndN (o1, o2) ->
          (match search0 init (Sbct (p, l, o1)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 ->
                (match search0 init (Sbct (p, l, o2)) stack __ with
                 | Some s1 ->
                   (match s1 with
                    | Inl s2 -> Some (Inl (Pbct_AndNR (s0, s2)))
                    | Inr _ -> Some (Inr __))
                 | None -> None)
              | Inr _ -> Some (Inr __))
           | None ->
             (match search0 init (Sbct (p, l, o2)) stack __ with
              | Some s ->
                (match s with
                 | Inl _ -> None
                 | Inr _ -> Some (Inr __))
              | None -> None))
        | Imp (o1, o2) ->
          (match search0 init (Sbct (p, (o1 :: l), o2)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 -> Some (Inl (Pbct_ImpR s0))
              | Inr _ -> Some (Inr __))
           | None -> None)
        | x0 ->
          (match search0 init (Sept (p, l, x0)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 -> Some (Inl (Pbct_boxR s0))
              | Inr _ -> Some (Inr __))
           | None -> None))
     | Sept (p, l, o0) ->
       (match l with
        | [] ->
          if inA_dec pndctx_o_eq_dec (p, o0) stack
          then None
          else if positive_dec o0
               then (match search0 init (Srfc (p, o0)) ((p, o0) :: stack) __ with
                     | Some s ->
                       (match s with
                        | Inl s0 -> Some (Inl (Pept_Rf s0))
                        | Inr _ ->
                          (match try_Lf_wrapper p o0 (fun n _ ->
                                   search0 init (Slfc (p, n, o0)) ((p,
                                     o0) :: stack) __) with
                           | Some s0 ->
                             (match s0 with
                              | Inl s1 -> Some (Inl s1)
                              | Inr _ -> Some (Inr __))
                           | None -> None))
                     | None ->
                       (match try_Lf_wrapper p o0 (fun n _ ->
                                search0 init (Slfc (p, n, o0)) ((p,
                                  o0) :: stack) __) with
                        | Some s ->
                          (match s with
                           | Inl s0 -> Some (Inl s0)
                           | Inr _ -> None)
                        | None -> None))
               else (match try_Lf_wrapper p o0 (fun n _ ->
                             search0 init (Slfc (p, n, o0)) ((p,
                               o0) :: stack) __) with
                     | Some s ->
                       (match s with
                        | Inl s0 -> Some (Inl s0)
                        | Inr _ -> Some (Inr __))
                     | None -> None)
        | o1 :: l0 ->
          (match o1 with
           | TT ->
             (match search0 init (Sept (p, l0, o0)) stack __ with
              | Some s ->
                (match s with
                 | Inl s0 -> Some (Inl (Pept_TrueL s0))
                 | Inr _ -> Some (Inr __))
              | None -> None)
           | FF ->
             if bracketable_dec o0
             then Some (Inl Pept_FalseL)
             else Some (Inr __)
           | AndP (o2, o3) ->
             (match search0 init (Sept (p, (o3 :: (o2 :: l0)), o0)) stack __ with
              | Some s ->
                (match s with
                 | Inl s0 -> Some (Inl (Pept_AndPL s0))
                 | Inr _ -> Some (Inr __))
              | None -> None)
           | Or (o2, o3) ->
             (match search0 init (Sept (p, (o2 :: l0), o0)) stack __ with
              | Some s ->
                (match s with
                 | Inl s0 ->
                   (match search0 init (Sept (p, (o3 :: l0), o0)) stack __ with
                    | Some s1 ->
                      (match s1 with
                       | Inl s2 -> Some (Inl (Pept_OrL (s0, s2)))
                       | Inr _ -> Some (Inr __))
                    | None -> None)
                 | Inr _ -> Some (Inr __))
              | None ->
                (match search0 init (Sept (p, (o3 :: l0), o0)) stack __ with
                 | Some s ->
                   (match s with
                    | Inl _ -> None
                    | Inr _ -> Some (Inr __))
                 | None -> None))
           | x0 ->
             (match search0 init (Sept ((pndctx_insert x0 p), l0, o0)) stack
                      __ with
              | Some s ->
                (match s with
                 | Inl s0 -> Some (Inl (Pept_boxL s0))
                 | Inr _ -> Some (Inr __))
              | None -> None)))
     | Slfc (p, o0, o1) ->
       (match o0 with
        | Atom (p0, n) ->
          (match p0 with
           | Pos ->
             (match search0 init (Sept (p, ((Atom (Pos, n)) :: []), o1))
                      stack __ with
              | Some s ->
                (match s with
                 | Inl s0 -> Some (Inl (Plfc_Rl s0))
                 | Inr _ -> Some (Inr __))
              | None -> None)
           | Neg ->
             if o_eq_dec (Atom (Neg, n)) o1
             then Some (Inl Plfc_Il)
             else Some (Inr __))
        | AndN (o2, o3) ->
          (match search0 init (Slfc (p, o2, o1)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 -> Some (Inl (Plfc_AndNL_1 s0))
              | Inr _ ->
                (match search0 init (Slfc (p, o3, o1)) stack __ with
                 | Some s0 ->
                   (match s0 with
                    | Inl s1 -> Some (Inl (Plfc_AndNL_2 s1))
                    | Inr _ -> Some (Inr __))
                 | None -> None))
           | None ->
             (match search0 init (Slfc (p, o3, o1)) stack __ with
              | Some s ->
                (match s with
                 | Inl s0 -> Some (Inl (Plfc_AndNL_2 s0))
                 | Inr _ -> None)
              | None -> None))
        | Imp (o2, o3) ->
          (match search0 init (Srfc (p, o2)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 ->
                (match search0 init (Slfc (p, o3, o1)) stack __ with
                 | Some s1 ->
                   (match s1 with
                    | Inl s2 -> Some (Inl (Plfc_ImpL (s0, s2)))
                    | Inr _ -> Some (Inr __))
                 | None -> None)
              | Inr _ -> Some (Inr __))
           | None ->
             (match search0 init (Slfc (p, o3, o1)) stack __ with
              | Some s ->
                (match s with
                 | Inl _ -> None
                 | Inr _ -> Some (Inr __))
              | None -> None))
        | x0 ->
          (match search0 init (Sept (p, (x0 :: []), o1)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 -> Some (Inl (Plfc_Rl s0))
              | Inr _ -> Some (Inr __))
           | None -> None))
     | Srfc (p, o0) ->
       (match o0 with
        | Atom (p0, n) ->
          (match p0 with
           | Pos ->
             if in_dec o_eq_dec (Atom (Pos, n)) (pndctx_list p)
             then Some (Inl Prfc_Ir)
             else Some (Inr __)
           | Neg ->
             (match search0 init (Sbct (p, [], (Atom (Neg, n)))) stack __ with
              | Some s ->
                (match s with
                 | Inl s0 -> Some (Inl (Prfc_Rr s0))
                 | Inr _ -> Some (Inr __))
              | None -> None))
        | TT -> Some (Inl Prfc_TrueR)
        | FF -> Some (Inr __)
        | AndP (o1, o2) ->
          (match search0 init (Srfc (p, o1)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 ->
                (match search0 init (Srfc (p, o2)) stack __ with
                 | Some s1 ->
                   (match s1 with
                    | Inl s2 -> Some (Inl (Prfc_AndPR (s0, s2)))
                    | Inr _ -> Some (Inr __))
                 | None -> None)
              | Inr _ -> Some (Inr __))
           | None ->
             (match search0 init (Srfc (p, o2)) stack __ with
              | Some s ->
                (match s with
                 | Inl _ -> None
                 | Inr _ -> Some (Inr __))
              | None -> None))
        | Or (o1, o2) ->
          (match search0 init (Srfc (p, o1)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 -> Some (Inl (Prfc_OrR_1 s0))
              | Inr _ ->
                (match search0 init (Srfc (p, o2)) stack __ with
                 | Some s0 ->
                   (match s0 with
                    | Inl s1 -> Some (Inl (Prfc_OrR_2 s1))
                    | Inr _ -> Some (Inr __))
                 | None -> None))
           | None ->
             (match search0 init (Srfc (p, o2)) stack __ with
              | Some s ->
                (match s with
                 | Inl s0 -> Some (Inl (Prfc_OrR_2 s0))
                 | Inr _ -> None)
              | None -> None))
        | x0 ->
          (match search0 init (Sbct (p, [], x0)) stack __ with
           | Some s ->
             (match s with
              | Inl s0 -> Some (Inl (Prfc_Rr s0))
              | Inr _ -> Some (Inr __))
           | None -> None)))
  in fix_F (a,(a0,(__,(a1,(__,__)))))

(** val try_decide_sequent : sequent -> (pterm, __) sum option **)

let try_decide_sequent = function
| Sept (c, l, k) ->
  if bracketable_dec k
  then search (Sept (c, l, k)) (Sept (c, l, k)) []
  else Some (Inr __)
| Slfc (c, n, k) ->
  if bracketable_dec k
  then search (Slfc (c, n, k)) (Slfc (c, n, k)) []
  else Some (Inr __)
| x -> search x x []
