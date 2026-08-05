open Ljfps_search

let empty_ctx : pndctx = []

let a = Atom (Pos, 0)
let b = Atom (Pos, 1)
let c = Atom (Neg, 2)

let seq = Sbct (empty_ctx, [a; Imp (a, b)], c)

let show name seq =
  match decide_sequent seq with
  | Some true  -> Printf.printf "%s: Derivable\n" name
  | Some false -> Printf.printf "%s: Not derivable\n" name
  | None       -> Printf.printf "%s: None\n" name

let () =
  show "seq" seq;
