From Stdlib Require Import List.
From LJF Require Import SharedLogic Sequents Pndctx Search_Procedure Search_Wrapper.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Extraction.
Extraction Language OCaml.
Extraction "ocaml/ljfps_search.ml" try_decide_sequent.