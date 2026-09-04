# Architecture: the calculus chain

The development is organised as a ladder of sequent calculi. The top rung is the
specification (a rendering of Liang & Miller's **LJF**); the bottom rung matches
an executable function. Rungs 0–3 (LJF … LJFPS) are each proved **sound**
(implied by the rung above) and **complete** (implies the rung above) on
derivability, so those four systems prove exactly the same sequents. LJFn and
LJFh (rungs 4–5) are used **only in the completeness direction** — they re-express
LJFPS derivability under successively finer invariants to drive
`search_complete`. No soundness leg runs back through them, and none is needed:
end-to-end soundness of the procedure is delivered by `verify_soundness`, which
re-checks the emitted `pterm` against the LJFPS rules directly.

```
        LJF_Rules.v          ufcL / lfcL / rfcL           the spec (Liang–Miller LJF)
           │                  ▲  
           | LJF4_Soundness   |   LJF4_Completeness
           ▼                  |
        LJF4_Rules.v          bct4 / ept4 / lfc4 / rfc4   split the async phase into two judgments
           │                  ▲  
           | LJFO_Soundness   |   LJFO_Completeness
           ▼                  |
        LJFO_Rules.v          bctO / eptO / lfcO / rfcO   process the linear context in list order
           │                  ▲  
           | LJFPS_Soundness  |   LJFPS_Completeness
           ▼                  |
        LJFPS_Rules.v         bct  / ept  / lfc  / rfc    unrestricted context = a finite dedup'd set
                              ▲  
                              | LJFn_Completeness        (completeness only — no soundness needed, proven regardless)
                              |
        LJFn_Rules.v          bctn / eptn / lfcn / rfcn   add an explicit derivation-height index
                              ▲ 
                              | LJFPS_Completeness        (completeness only — no soundness needed)
                              |
        LJFh_Rules.v          bcth / epth / lfch / rfch   carry a history; forbid revisiting a focus point
                              ▲  
                              | Search_Completeness
                              |
        Search_Procedure.v    search / try_decide_sequent an Equations function on a well-founded measure
                              |
                              │  ProofTerms_Soundness (verify_soundness)   ← the only soundness leg below LJFPS
                              ▼
                              back to LJFPS derivability
```

The four judgments carried through every layer:

| Judgment | Reads as | Phase |
|---|---|---|
| `bct C L K` | from `C` (unrestricted) and `L` (linear), goal `K` is provable | asynchronous, unbracketed
| `ept C L K` | same, but `K` is `bracketable` and we are past the `boxR` boundary | asynchronous, bracketed |
| `lfc C N K` | with left focus on `N ∈ C`, reach `K` | focused (left) |
| `rfc C K` | with right focus on `K` | focused (right) |

In the LJF spec these are a single relation `ufcL C L K state` with
`state ∈ {Bracketed, Unbracketed}` plus `lfcL`, `rfcL`. `ept` corresponds to
`ufcL … Bracketed`, `bct` to `ufcL … Unbracketed`.

See [GLOSSARY.md](GLOSSARY.md) for `bracketable`, `permeable`, `box`, `_star`.

---

## Rung 0 — LJF, the specification

**File:** [`src/rules/LJF_Rules.v`](../src/rules/LJF_Rules.v)

`ufcL : sctx → octx → o → state → Prop` mutually with `lfcL`, `rfcL`, over a
plain `sctx = list o` context. Left rules permute the linear context
(`Permutation L (B :: L1)`). The `state` flag threads the bracket discipline
through the asynchronous phase; because the async rules run in *both* states,
each left rule appears twice — once ending in `Bracketed` and once as a
`…_star` rule ending in `Unbracketed`. `ufcL_boxR` crosses from `Unbracketed`
to `Bracketed` once the goal is `bracketable`; `ufcL_boxL` / `ufcL_boxL_star`
move a `permeable` linear formula into the unrestricted context.

This file is what the whole development is verified *against*. It is deliberately
close to the paper and makes no concession to executability.

> **Known imprecision — the unrestricted context is unconstrained.** On-paper
> LJF maintains, as a standing well-formedness condition, that the unrestricted
> zone holds only *permeable* formulas (negative formulas and positive atoms).
> This repo's LJF formalization does **not** carry that condition anywhere: in
> all three judgments — `ufcL`, `lfcL`, `rfcL` — the context is a bare
> `sctx = list o`, with no side condition and no well-formedness index.
> Permeability is checked only *dynamically*, at the moment a formula is stored
> (`ufcL_boxL` / `ufcL_boxL_star` require `permeable B`); nothing rules out a
> non-permeable formula (`TT`, `FF`, a positive `∧⁺` / `∨`) being in `C` from
> the start, and no lemma here establishes that the `C` of a derivable
> `ufcL` / `lfcL` / `rfcL` is permeable.
>
> This changes none of the results, because no rule ever *reads* a non-permeable
> member of `C`: `ufcL_Lf` focuses only on *negative* members, `rfcL_Ir` only on
> *positive atoms*. Non-permeable entries are inert — adding or deleting them
> cannot change derivability — so on well-formed inputs the formalization still
> captures exactly LJF provability. It is nonetheless a discrepancy with the
> paper; the clean fix is to thread `permeable_ctx C` through the LJF judgments
> (as a hypothesis or a well-formedness index).
>
> **LJFPS closes it downstream** (rung 3): its context type `pndctx` bundles the
> `NoDup` and `permeable_ctx` proofs, so an ill-formed context is simply
> *unrepresentable* — no user of LJFPS or of the decision procedure can
> construct one, and no proof can either. The imprecision is confined to the
> spec layer.

## Rung 1 — LJF4: separate the two async modes

**File:** [`src/rules/LJF4_Rules.v`](../src/rules/LJF4_Rules.v) ·
**bridges:** [`LJF4_Soundness.v`](../src/metatheory/LJF4/LJF4_Soundness.v),
[`LJF4_Completeness.v`](../src/metatheory/LJF4/LJF4_Completeness.v)

`4` = *4 judgments*. Replace the `state` parameter by two separate mutually-inductive judgments:
`bct4` (was `Unbracketed`) and `ept4` (was `Bracketed`). The `…_star`
duplicates disappear. `LJF4_soundness` erases the split back to `ufcL`;
`LJF4_completeness` rebuilds it and needs the `admissibility_*_star` lemmas
(that each left rule is admissible in `bct4`) together with the linear/structural
exchange lemmas in [`LJF4_Exchange.v`](../src/metatheory/LJF4/LJF4_Exchange.v).

## Rung 2 — LJFO: fix the order of the linear context

**File:** [`src/rules/LJFO_Rules.v`](../src/rules/LJFO_Rules.v) ·
**bridges:** [`LJFO_Soundness.v`](../src/metatheory/LJFO/LJFO_Soundness.v),
[`LJFO_Completeness.v`](../src/metatheory/LJFO/LJFO_Completeness.v)

`O` = *ordered*. Every left rule now pattern-matches on the **head** of the
linear context (`eptO C (AndP B1 B2 :: L) K → …`) instead of permuting it.
Soundness is immediate (`Permutation_refl`). Completeness — that committing to
one processing order loses nothing — is the real work: the `eager_*` lemmas in
[`LJFO_Exchange.v`](../src/metatheory/LJFO/LJFO_Exchange.v) show each linear
connective can be decomposed first, and `LJFO_exchange_ordered` moves the
conclusion along a permutation.
[`LJFO_Weakening.v`](../src/metatheory/LJFO/LJFO_Weakening.v) supplies
`LJFO_structural_cons_weakening`, used by the LJFPS soundness bridge.
(`LJFO_Contraction.v` proves the two contraction lemma but is not currently on
the build path — see [FILE_MAP.md](FILE_MAP.md#not-on-the-build-path).)

## Rung 3 — LJFPS: the unrestricted context becomes a finite set

**File:** [`src/rules/LJFPS_Rules.v`](../src/rules/LJFPS_Rules.v) ·
**bridges:** [`LJFPS_Soundness.v`](../src/metatheory/LJFPS/LJFPS_Soundness.v),
[`LJFPS_Completeness.v`](../src/metatheory/LJFPS/LJFPS_Completeness.v)

`PS` = *proof search*. The context type changes from `sctx` to
**`pndctx`** — a `list o` bundled with proofs that it has **no duplicates** and
contains only **permeable** formulas (see [`Pndctx.v`](../src/definitions/Pndctx.v)).
`ept_boxL` adds a formula with `pndctx_insert` (dedup + permeability filter)
rather than `::`. Consequently, the unrestricted context can only ever be extended 
with permeable subformulas of the goal, and holds each at most once — so it ranges over a **finite** set.

Because `pndctx` bundles the `NoDup` and `permeable_ctx` proofs into the type,
**a non-permeable or duplicate-bearing context cannot be constructed at all** —
rung 0's imprecision is not merely closed by an obligation, it is unrepresentable
from here on. One practical upshot: **you cannot pre-load an arbitrary hypothesis
into the context.** To ask whether `K` follows from
hypotheses `A₁ … Aₙ` in LJ, start in the `bct` phase with the `Aᵢ` in the
**linear context**: `Sbct pndctx_empty [A₁; …; Aₙ] K`, or fold them into the
goal as `A₁ → ⋯ → Aₙ → K`. The asynchronous `bct` / `ept` phase then decomposes
them and `boxL`s the permeable parts into `C` itself — which is exactly the
paper's intended entry point.

`LJFPS_soundness` maps `pndctx` back to its underlying list and repairs the
possibly-dropped `pndctx_insert` with `LJFO_structural_cons_weakening`.
`LJFPS_completeness` goes the other way through `mk_pndctx = filter permeable_b ∘ nodup`.
[`LJFPS_Inversion.v`](../src/metatheory/LJFPS/LJFPS_Inversion.v) provides one
inversion lemma per rule (`bct_boxR_inv`, `ept_boxL_inv`, …); the decider uses
them to justify its "not derivable" branches. (`LJFPS_Exchange.v` proves
permuting `pndctx_list` preserves derivability, but is not on the build path —
the search-completeness chain uses the height-indexed version instead.)

> **[`src/Global_Results.v`](../src/Global_Results.v) — result 1:**
> `LJFPS_Sound_And_Complete_To_LJF` chains rungs 1–3 in both directions to get
> `bct C L K ↔ ufcL (pndctx_list C) L K Unbracketed` and the `ept`/`lfc`/`rfc`
> analogues. This is the bridge from the search calculus back to the spec.

## Rung 4 — LJFn: index derivations by height

**File:** [`src/rules/LJFn_Rules.v`](../src/rules/LJFn_Rules.v) ·
**bridge:** [`LJFn_Completeness.v`](../src/metatheory/LJFn/LJFn_Completeness.v)

Every rule gains a leading `nat` which increases at each inference rule application,
and is set arbitrarily at the leafs. Purely a proof device.

- `LJFn_completeness`: `bct C L K → ∃ n, bctn n C L K`, via the monotonicity
  lemmas in [`LJFn_Monotone.v`](../src/metatheory/LJFn/LJFn_Monotone.v)
  (`m ≤ n → bctn m … → bctn n …`). This is the only direction used downstream.
- The erasure lemma `LJFn_soundness` (`bctn n C L K → bct C L K`) is proved in
  `LJFn_Soundness.v`, but nothing in `Global_Results.v` needs it — soundness of
  the procedure comes from `verify_soundness`, not from erasing indices — so the
  file has been dropped from the build path (see
  [FILE_MAP.md](FILE_MAP.md#not-on-the-build-path)).
- [`LJFn_MinimalHeight.v`](../src/metatheory/LJFn/LJFn_MinimalHeight.v): a
  standalone `Equations` decider `LJFn_decider` (well-founded on the height),
  `LJFn_find_min_height`, and `min_height_exists` — *every provable
  `ept C nil K` has a least height, unprovable below it*. This is exactly what
  the next rung needs. 
- Also mirrors the LJFPS inversion / disproof lemmas at indexed type
  ([`LJFn_Inversion.v`](../src/metatheory/LJFn/LJFn_Inversion.v),
  [`LJFn_Bracketable.v`](../src/metatheory/LJFn/LJFn_Bracketable.v),
  [`LJFn_Exchange.v`](../src/metatheory/LJFn/LJFn_Exchange.v)).

## Rung 5 — LJFh: forbid revisiting a focus decision

**File:** [`src/rules/LJFh_Rules.v`](../src/rules/LJFh_Rules.v) ·
**bridge:** [`LJFh_Completeness.v`](../src/metatheory/LJFh/LJFh_Completeness.v)

`h` = *history*. The judgments carry `Hs : hist = list (pndctx * o)`. The
rules that pick a new focus formula on an empty linear context — `epth_Lf`
(left focus) and `epth_Rf` (right focus) — now require
`~ InA pndctx_o_eq (C, K) Hs` and push `(C, K)` onto `Hs`. The search space
becomes finite: the same `(context, goal)` focus point cannot recur on a branch.

**The completeness argument in one sentence:** a provable sequent always has a
derivation in which no focus decision repeats, obtained by taking a
*height-minimal* sub-derivation at each focus point — a minimal derivation of
`(C, K)` cannot contain another derivation of the same `(C, K)`, since the inner
one would have strictly smaller height and contradict minimality. LJFh simply
bakes that choice in as the `~ InA pndctx_o_eq (C, K) Hs` side condition.

Mechanically, `LJFh_completeness` is a well-founded induction on the height `n`:
if `eptn n C L K` and `hist_height_bound Hs n` (every entry of `Hs` is unprovable
at height ≤ `n`) then `epth Hs C L K`. At a focus point it calls
`min_height_exists` (rung 4) for the least height `x ≤ n` at which `ept C nil K`
holds and inverts *that* derivation; `hist_height_bound_cons` then shows pushing
`(C, K)` keeps the invariant — its sub-goals sit strictly below `x`, and `(C, K)`
itself is unprovable below `x` by minimality, so it can never be re-selected
deeper on the branch. The `Hs = nil` corollary (`hist_height_bound_nil`) matches
the initial call of the procedure.

There is no `LJFh_Soundness`, and none is needed. LJFh is used only in its
completeness direction (to drive `search_complete`); soundness of the procedure
is already covered by `verify_soundness` on the returned `pterm`, so a soundness
leg from LJFh (or LJFn) back to LJFPS would be redundant.

## Rung 6 — the procedure

**Files:** [`src/proofsearch/`](../src/proofsearch/)

- [`Sequents.v`](../src/proofsearch/Sequents.v) — `sequent` (tagged union of the
  four judgment forms), `sequent_derivable`, `subsequent S S0` (all of `S`'s
  formulas are subformulas of `S0`, in the right polarity buckets).
- [`Subformula.v`](../src/proofsearch/Subformula.v) — the `subformula` relation
  and its computable `subformulas` list.
- [`Subsequent_Preservation.v`](../src/proofsearch/Subsequent_Preservation.v) —
  one `subp_*` lemma per search step: every recursive call stays a `subsequent`
  of the fixed `init`. This bounds the reachable state space.
- [`Focus_Decision_Set.v`](../src/proofsearch/Focus_Decision_Set.v) —
  `get_all_focus_decision init` = (subsets of permeable subformulas) × (bracketable
  subformulas), a finite superset of every focus point; `stack_length_bound`: a
  `NoDupA` stack of `subsequent`-`init` focus points is shorter than that list.
- [`Termination_Measures.v`](../src/proofsearch/Termination_Measures.v) —
  `phase_ranking` (ept 0 < bct 1 < rfc 2 < lfc 3) and `phase_measure` (goal /
  linear-context size).
- [`ProofTerms.v`](../src/proofsearch/ProofTerms.v) — `pterm`, a first-order
  proof-term syntax in sort **`Type`** (one constructor per LJFPS rule), and
  `verify : pterm → sequent → Prop`, a checker relation mirroring the rules.
  `verify_soundness` ([`ProofTerms_Soundness.v`](../src/proofsearch/ProofTerms_Soundness.v))
  : `verify p seq → sequent_derivable seq`; `verify_completeness`
  ([`ProofTerms_Completeness.v`](../src/proofsearch/ProofTerms_Completeness.v))
  is the converse. `pterm` sits in `Type`, not `Prop`, precisely so it survives
  extraction — see [Extraction](#extraction).
- [`Search_Procedure.v`](../src/proofsearch/Search_Procedure.v) — `search`,
  defined by `Equations` well-founded recursion on the lexicographic triple

      (|get_all_focus_decision init| − |stack|,  phase_ranking seq,  phase_measure seq)

  returning `option ({p | verify p seq} + ~ sequent_derivable seq)`.
  `Some (inl p)` = verified proof, `Some (inr _)` = verified refutation,
  `None` = a focus decision recurred (still means underivable, but no witness).
- [`Search_Wrapper.v`](../src/proofsearch/Search_Wrapper.v) — `try_decide_sequent`,
  the entry point (seeds `search` with `init = seq`, empty stack).
- [`Search_Completeness.v`](../src/proofsearch/Search_Completeness.v) —
  `search_complete`: `bcth/epth/lfch/rfch` (rung 5) ⇒ `search` returns
  `Some (inl _)`.

> **[`src/Global_Results.v`](../src/Global_Results.v) — results 2–4:**
> `Derivable_iff_Search_Returns_Some_left` composes
> `LJFn_completeness → LJFh_completeness_alt → search_complete` forward and
> `verify_soundness` backward;
> `Underivable_iff_Search_Returns_Some_Right_or_None` is the negative side; and
> `decide` packages both into `{sequent_derivable s} + {~ sequent_derivable s}`.

## Extraction

[`src/examples/LJFPS_Search.v`](../src/examples/LJFPS_Search.v) runs
`Extraction "ocaml/ljfps_search.ml" try_decide_sequent`. It is **excluded from
`_RocqProject`**, so `make` never re-extracts — see [BUILDING.md](BUILDING.md).
[`ocaml/driver.ml`](../ocaml/driver.ml) pretty-prints a sequent and renders the
returned `pterm` as a rule tree.

**Why the procedure returns a `pterm`, not an LJFPS proof.** `search`'s success
type is `{p : pterm | verify p seq}`. `pterm` is in `Type`, so it survives to
OCaml as an ordinary data structure; the `verify p seq` component and the LJFPS
derivation `sequent_derivable seq` are in `Prop`, which extraction erases. The
extracted OCaml therefore hands back only the `pterm` — the runtime-visible
skeleton of the derivation. Its correctness is **not** re-established at runtime:
`verify_soundness : verify p seq → sequent_derivable seq` is proved once, in
`Prop`, inside the development, and `Derivable_iff_Search_Returns_Some_left` ties
the returned `pterm` back to real LJFPS derivability. Returning the LJFPS `Prop`
witness directly would be pointless — extraction would erase it to `()`.
