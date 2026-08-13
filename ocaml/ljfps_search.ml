
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val try_Lf :
    pndctx -> o -> (o -> __ -> bool option) -> o list -> bool option **)

let rec try_Lf c k try_N = function
| [] -> Some false
| o0 :: l ->
  (match try_N o0 __ with
   | Some s -> if s then Some true else try_Lf c k try_N l
   | None ->
     (match try_Lf c k try_N l with
      | Some s -> if s then Some true else None
      | None -> None))

(** val try_Lf_wrapper :
    pndctx -> o -> (o -> __ -> bool option) -> bool option **)

let try_Lf_wrapper c k try_N =
  try_Lf c k try_N (filter negative_b (pndctx_list c))

(** val search : sequent -> sequent -> (pndctx * o) list -> bool option **)

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
             if s then search0 init (Sbct (p, l, o2)) stack __ else Some false
           | None ->
             (match search0 init (Sbct (p, l, o2)) stack __ with
              | Some s -> if s then None else Some false
              | None -> None))
        | Imp (o1, o2) -> search0 init (Sbct (p, (o1 :: l), o2)) stack __
        | x0 -> search0 init (Sept (p, l, x0)) stack __)
     | Sept (p, l, o0) ->
       (match l with
        | [] ->
          if inA_dec pndctx_o_eq_dec (p, o0) stack
          then None
          else if positive_dec o0
               then (match search0 init (Srfc (p, o0)) ((p, o0) :: stack) __ with
                     | Some s ->
                       if s
                       then Some true
                       else try_Lf_wrapper p o0 (fun n _ ->
                              search0 init (Slfc (p, n, o0)) ((p,
                                o0) :: stack) __)
                     | None ->
                       (match try_Lf_wrapper p o0 (fun n _ ->
                                search0 init (Slfc (p, n, o0)) ((p,
                                  o0) :: stack) __) with
                        | Some s -> if s then Some true else None
                        | None -> None))
               else try_Lf_wrapper p o0 (fun n _ ->
                      search0 init (Slfc (p, n, o0)) ((p, o0) :: stack) __)
        | o1 :: l0 ->
          (match o1 with
           | TT -> search0 init (Sept (p, l0, o0)) stack __
           | FF -> Some (bracketable_dec o0)
           | AndP (o2, o3) ->
             search0 init (Sept (p, (o3 :: (o2 :: l0)), o0)) stack __
           | Or (o2, o3) ->
             (match search0 init (Sept (p, (o2 :: l0), o0)) stack __ with
              | Some s ->
                if s
                then search0 init (Sept (p, (o3 :: l0), o0)) stack __
                else Some false
              | None ->
                (match search0 init (Sept (p, (o3 :: l0), o0)) stack __ with
                 | Some s -> if s then None else Some false
                 | None -> None))
           | x0 -> search0 init (Sept ((pndctx_insert x0 p), l0, o0)) stack __))
     | Slfc (p, o0, o1) ->
       (match o0 with
        | Atom (p0, n) ->
          (match p0 with
           | Pos ->
             search0 init (Sept (p, ((Atom (Pos, n)) :: []), o1)) stack __
           | Neg -> Some (o_eq_dec (Atom (Neg, n)) o1))
        | AndN (o2, o3) ->
          (match search0 init (Slfc (p, o2, o1)) stack __ with
           | Some s ->
             if s then Some true else search0 init (Slfc (p, o3, o1)) stack __
           | None ->
             (match search0 init (Slfc (p, o3, o1)) stack __ with
              | Some s -> if s then Some true else None
              | None -> None))
        | Imp (o2, o3) ->
          (match search0 init (Srfc (p, o2)) stack __ with
           | Some s ->
             if s
             then search0 init (Slfc (p, o3, o1)) stack __
             else Some false
           | None ->
             (match search0 init (Slfc (p, o3, o1)) stack __ with
              | Some s -> if s then None else Some false
              | None -> None))
        | x0 -> search0 init (Sept (p, (x0 :: []), o1)) stack __)
     | Srfc (p, o0) ->
       (match o0 with
        | Atom (p0, n) ->
          (match p0 with
           | Pos -> Some (in_dec o_eq_dec (Atom (Pos, n)) (pndctx_list p))
           | Neg -> search0 init (Sbct (p, [], (Atom (Neg, n)))) stack __)
        | TT -> Some true
        | FF -> Some false
        | AndP (o1, o2) ->
          (match search0 init (Srfc (p, o1)) stack __ with
           | Some s ->
             if s then search0 init (Srfc (p, o2)) stack __ else Some false
           | None ->
             (match search0 init (Srfc (p, o2)) stack __ with
              | Some s -> if s then None else Some false
              | None -> None))
        | Or (o1, o2) ->
          (match search0 init (Srfc (p, o1)) stack __ with
           | Some s ->
             if s then Some true else search0 init (Srfc (p, o2)) stack __
           | None ->
             (match search0 init (Srfc (p, o2)) stack __ with
              | Some s -> if s then Some true else None
              | None -> None))
        | x0 -> search0 init (Sbct (p, [], x0)) stack __))
  in fix_F (a,(a0,(__,(a1,(__,__)))))

(** val try_decide_sequent : sequent -> bool option **)

let try_decide_sequent = function
| Sept (c, l, k) ->
  if bracketable_dec k
  then search (Sept (c, l, k)) (Sept (c, l, k)) []
  else Some false
| Slfc (c, n, k) ->
  if bracketable_dec k
  then search (Slfc (c, n, k)) (Slfc (c, n, k)) []
  else Some false
| x -> search x x []
