# File map

Every `.v` file, in the compile order of
[`_RocqProject`](../_RocqProject) (dependencies first). Logical library name is
`LJF` (`-R src LJF`), so imports read `From LJF Require Import …`.

Everything listed in `_RocqProject` is on the dependency path to
[`src/Global_Results.v`](../src/Global_Results.v). A few files exist on disk but
are **not** on the build path and are imported by nothing — see
[§ Not on the build path](#not-on-the-build-path) at the end.

## `src/stdLib/` — generic list / setoid lemmas

| File | Role |
|---|---|
| [`SetoidList_Extended.v`](../src/stdLib/SetoidList_Extended.v) | `equivlistA_dec`, `NoDupA_inclA_length_lt`, `removeA_*` — setoid-list counting used by the termination bound |
| [`Subsets.v`](../src/stdLib/Subsets.v) | `get_all_subsets`, `prepend_all`, `inclA_iff_get_all_subsets` — powerset of a list up to `equivlistA` |

## `src/definitions/` — syntax and basic decidability

| File | Role |
|---|---|
| [`SharedLogic.v`](../src/definitions/SharedLogic.v) | formula syntax `o` (`Atom`, `TT`, `FF`, `AndP`, `AndN`, `Or`, `Imp`), `polarity`, predicates `atomic` / `positive` / `negative` / `bracketable` / `permeable`, context notations `sctx` / `lctx` / `octx` |
| [`Decidability.v`](../src/definitions/Decidability.v) | `o_eq_dec`, `polarity_eq_dec`, and `*_dec` for each predicate |
| [`Measures.v`](../src/definitions/Measures.v) | `osize` (formula size), `octx_size` (linear-context size) |
| [`Predicates.v`](../src/definitions/Predicates.v) | boolean `positive_b` / `negative_b` / `permeable_b` / `bracketable_b` with `_iff` correctness lemmas |
| [`Pndctx.v`](../src/definitions/Pndctx.v) | **`pndctx`** = `{ C : sctx \| NoDup C & permeable_ctx C }`; `raw_insert` / `pndctx_insert`, `pndctx_empty`, `mk_pndctx`, `pndctx_set_eq`, `pndctx_o_eq` and their algebra (`pndctx_insert_swap`, `pndctx_list_mk_commute`, …) |

## `src/tactics/`

| File | Role |
|---|---|
| [`SharedLogic_tactics.v`](../src/tactics/SharedLogic_tactics.v) | `T_atomic`, `T_positive`, `T_negative`, `T_permeable`, `T_bracketable` — discharge polarity side conditions (used by `Predicates.v`) |

(`src/tactics/LJFPS_Prover.v` — the unverified team-phase `Ltac` prover — is kept
for reference but is **not** on the build path; see
[§ Not on the build path](#not-on-the-build-path).)

## `src/rules/` — the calculi

| File | Judgments | Notes |
|---|---|---|
| [`LJF_Rules.v`](../src/rules/LJF_Rules.v) | `ufcL C L K state`, `lfcL`, `rfcL` | the specification; `state ∈ {Bracketed, Unbracketed}`, `Permutation` left rules, `_star` duplicates. The context `C` carries no `permeable_ctx` condition in any judgment (paper does — see [ARCHITECTURE.md](ARCHITECTURE.md) rung 0) |
| [`LJF4_Rules.v`](../src/rules/LJF4_Rules.v) | `bct4`, `ept4`, `lfc4`, `rfc4` | the `state` split into two judgments; no `_star` |
| [`LJFO_Rules.v`](../src/rules/LJFO_Rules.v) | `bctO`, `eptO`, `lfcO`, `rfcO` | linear context processed head-first (`octx`), no `Permutation` |
| [`LJFPS_Rules.v`](../src/rules/LJFPS_Rules.v) | `bct`, `ept`, `lfc`, `rfc` | context is `pndctx`; `ept_boxL` uses `pndctx_insert` |
| [`LJFn_Rules.v`](../src/rules/LJFn_Rules.v) | `bctn n`, `eptn n`, `lfcn n`, `rfcn n` | explicit `nat` derivation-height index |
| [`LJFh_Rules.v`](../src/rules/LJFh_Rules.v) | `bcth Hs`, `epth Hs`, `lfch Hs`, `rfch Hs` | `hist` of visited focus points; `epth_Lf` / `epth_Rf` forbid repeats |

## `src/metatheory/`

| File | Key results |
|---|---|
| [`Schemes.v`](../src/metatheory/Schemes.v) | `Combined Scheme` mutual-induction principles for every calculus (`LJF_mutind_all`, …, `LJFh_mutind_all`; plus `_async`, `_bracketable` variants) |
| **LJF4** | |
| [`LJF4/LJF4_Exchange.v`](../src/metatheory/LJF4/LJF4_Exchange.v) | `LJF4_exchange_structural` (unrestricted ctx), `LJF4_exchange_linear` (linear ctx) |
| [`LJF4/LJF4_Soundness.v`](../src/metatheory/LJF4/LJF4_Soundness.v) | `LJF4_soundness` : `bct4/ept4/lfc4/rfc4 ⇒ ufcL/lfcL/rfcL` |
| [`LJF4/LJF4_Completeness.v`](../src/metatheory/LJF4/LJF4_Completeness.v) | `LJF4_completeness` : `ufcL ⇒ bct4/ept4` (by state); `admissibility_*_star` lemmas |
| **LJFO** | |
| [`LJFO/LJFO_Exchange.v`](../src/metatheory/LJFO/LJFO_Exchange.v) | `LJFO_exchange_structural` / `_ordered`; `eager_boxL/AndPL/OrL/TrueL/FalseL`; `LJFO_inversion_boxL` |
| [`LJFO/LJFO_Completeness.v`](../src/metatheory/LJFO/LJFO_Completeness.v) | `LJFO_completeness` : `bct4/ept4/… ⇒ bctO/eptO/…` |
| [`LJFO/LJFO_Soundness.v`](../src/metatheory/LJFO/LJFO_Soundness.v) | `LJFO_soundness` : `bctO/eptO/… ⇒ bct4/ept4/…` |
| [`LJFO/LJFO_Weakening.v`](../src/metatheory/LJFO/LJFO_Weakening.v) | `LJFO_structural_cons_weakening` (add any formula to the unrestricted ctx) |
| **LJFPS** | |
| [`LJFPS/LJFPS_Completeness.v`](../src/metatheory/LJFPS/LJFPS_Completeness.v) | `LJFPS_completeness` : `bctO C ⇒ bct (mk_pndctx C)`, … |
| [`LJFPS/LJFPS_Soundness.v`](../src/metatheory/LJFPS/LJFPS_Soundness.v) | `LJFPS_soundness` : `bct C ⇒ bctO (pndctx_list C)`, … |
| [`LJFPS/LJFPS_Bracketable.v`](../src/metatheory/LJFPS/LJFPS_Bracketable.v) | `LJFPS_bracketable_goal_ept` / `_lfc` : `ept`/`lfc` goals are `bracketable` |
| [`LJFPS/LJFPS_Inversion.v`](../src/metatheory/LJFPS/LJFPS_Inversion.v) | one inversion lemma per rule (`bct_boxR_inv`, `ept_boxL_inv`, `lfc_ImpL_inv`, … , `rfc_FF_unprovable`) |
| **LJFn** | |
| [`LJFn/LJFn_Monotone.v`](../src/metatheory/LJFn/LJFn_Monotone.v) | `LJFn_monotone_*` : derivable at height `m` ⇒ derivable at any `n ≥ m` |
| [`LJFn/LJFn_Completeness.v`](../src/metatheory/LJFn/LJFn_Completeness.v) | `LJFn_completeness` : `bct C L K ⇒ ∃ n, bctn n C L K`, … |
| [`LJFn/LJFn_MinimalHeight.v`](../src/metatheory/LJFn/LJFn_MinimalHeight.v) | `LJFn_decider` (Equations, wf on height), `LJFn_find_min_height`, `min_height_exists` |
| [`LJFn/LJFn_Exchange.v`](../src/metatheory/LJFn/LJFn_Exchange.v) | `LJFn_exchange_structural_eptn` : permutation preserves the height |
| [`LJFn/LJFn_Inversion.v`](../src/metatheory/LJFn/LJFn_Inversion.v) | height-indexed inversion + disproof lemmas (`eptn_nil_disproof_pos/neg`, `rfcn_FF_unprovable`) |
| [`LJFn/LJFn_Bracketable.v`](../src/metatheory/LJFn/LJFn_Bracketable.v) | height-indexed `bracketable`-goal lemma |
| **LJFh** | |
| [`LJFh/LJFh_Completeness.v`](../src/metatheory/LJFh/LJFh_Completeness.v) | `LJFh_completeness` / `_alt` : `eptn n …` + `hist_height_bound Hs n` ⇒ `epth Hs …`; `hist_height_bound_*` helpers |

## `src/proofsearch/` — the decision procedure

| File | Role |
|---|---|
| [`Subformula.v`](../src/proofsearch/Subformula.v) | `subformula` relation, `subformulas` list, transitivity |
| [`Sequents.v`](../src/proofsearch/Sequents.v) | `sequent` = `Sbct`/`Sept`/`Slfc`/`Srfc`; `sequent_derivable`; `sequent_subformulas(_positive/_negative/_permeable/_bracketable)`; `subsequent`, `subsequent_refl` |
| [`Subsequent_Preservation.v`](../src/proofsearch/Subsequent_Preservation.v) | `subp_*` — every recursive search call is still a `subsequent` of `init` |
| [`Termination_Measures.v`](../src/proofsearch/Termination_Measures.v) | `phase_ranking`, `phase_measure` |
| [`Focus_Decision_Set.v`](../src/proofsearch/Focus_Decision_Set.v) | `get_all_focus_decision`, `stack_length_bound` (the dominating termination component) |
| [`ProofTerms.v`](../src/proofsearch/ProofTerms.v) | `pterm` syntax, `verify : pterm → sequent → Prop` |
| [`ProofTerms_Soundness.v`](../src/proofsearch/ProofTerms_Soundness.v) | `verify_soundness` : `verify p seq → sequent_derivable seq` |
| [`ProofTerms_Completeness.v`](../src/proofsearch/ProofTerms_Completeness.v) | `verify_completeness` : every LJFPS derivation has a `verify`-able `pterm` |
| [`Search_Procedure.v`](../src/proofsearch/Search_Procedure.v) | `search` (Equations, wf on the lexicographic triple), `try_Lf` / `try_Lf_wrapper` |
| [`Search_Wrapper.v`](../src/proofsearch/Search_Wrapper.v) | `try_decide_sequent` — entry point |
| [`Search_Completeness.v`](../src/proofsearch/Search_Completeness.v) | `search_complete` : LJFh derivability ⇒ `search` returns `Some (inl _)`; `returns_some_proof` / `returns_some_disproof` / `returns_none` |

## Top level

| File | Role |
|---|---|
| [`src/Global_Results.v`](../src/Global_Results.v) | the four headline theorems; each followed by `Print Assumptions` — see [KEY_RESULTS.md](KEY_RESULTS.md) |

## `ocaml/`

| File | Role |
|---|---|
| [`ocaml/ljfps_search.ml`](../ocaml/ljfps_search.ml) / `.mli` | extraction output, committed in-tree so the procedure builds without Rocq |
| [`ocaml/driver.ml`](../ocaml/driver.ml) | pretty-prints sequents, renders the returned `pterm` as a rule tree; `dune exec ./driver.exe` |
| `ocaml/dune`, `ocaml/dune-project` | build glue |

## Not on the build path

These `.v` files are in the tree but absent from [`_RocqProject`](../_RocqProject),
so `make` never compiles them, and no compiled file imports them.

| File | Status |
|---|---|
| [`src/examples/LJFPS_Search.v`](../src/examples/LJFPS_Search.v) | **intentional.** The extraction entry point (`Extraction "ocaml/ljfps_search.ml" try_decide_sequent`); run by hand after `make` — see [BUILDING.md](BUILDING.md). Keeping it off the path stops every `make` from re-extracting. |
| [`src/tactics/LJFPS_Prover.v`](../src/tactics/LJFPS_Prover.v) | **kept for reference.** An *unverified* `Ltac` proof procedure over the LJFPS rules — its own `T_*` polarity tactics, a `paths` accumulator for loop detection, and phase tactics `T_bct` / `T_ept` / `T_lfc` / `T_rfc`. It descends from the COMP 527 team solver, adapted from LJF4 to LJFPS ([Acknowledgements](../README.md#acknowledgements)); no termination or correctness proof, and the verified `search` supersedes it. Self-contained on `LJFPS_Rules` (the `has_entry` comment inside is stale). |
| [`src/metatheory/LJFPS/LJFPS_Exchange.v`](../src/metatheory/LJFPS/LJFPS_Exchange.v) | **spare metatheory.** `LJFPS_exchange_structural` (permuting `pndctx_list` preserves derivability). Self-contained and true, but the search-completeness chain uses `LJFn_exchange_structural_eptn` instead, so it is currently unused. |
| [`src/metatheory/LJFO/LJFO_Contraction.v`](../src/metatheory/LJFO/LJFO_Contraction.v) | **spare metatheory.** `LJFO_structural_cons_contraction` (a duplicate in the unrestricted context is redundant). The LJFPS soundness bridge only needs weakening, so this is currently unused. |
| [`src/metatheory/LJFn/LJFn_Soundness.v`](../src/metatheory/LJFn/LJFn_Soundness.v) | **not needed.** `LJFn_soundness` : `bctn n C L K ⇒ bct C L K` (height erasure). True and provable, but no result in `Global_Results.v` uses it — the LJFn → LJFh → `search` chain runs completeness-only, and the procedure's soundness is `verify_soundness`. Dropped from `_RocqProject`. |

`SharedLogic_tactics.v` *is* on the build path and *is* used ­— `Predicates.v`
imports it for the `T_*` polarity tactics — so it is not in this list.
