From Stdlib Require Import List.
From LJF Require Import SharedLogic Sequents Pndctx Search_Procedure Search_Wrapper.

From Stdlib Require Import ExtrOcamlNatInt.

Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "ocaml/ljfps_search.ml" try_decide_sequent.