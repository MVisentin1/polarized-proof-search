# Key results — a guided read of `Global_Results.v`

[`src/Global_Results.v`](../src/Global_Results.v) is the file to open first. It
imports the whole development and states five results, each followed by
`Print Assumptions`. There is no `Admitted` anywhere in `src/`, and no
classical-logic axioms (they were removed in commit `b677fa0`). Two axioms
remain:

```
proof_irrelevance             : forall (P : Prop) (p1 p2 : P), p1 = p2
functional_extensionality_dep : forall f g, (forall x, f x = g x) -> f = g
```

- **`proof_irrelevance`** — `From Stdlib Require Import ProofIrrelevance` in
  [`Pndctx.v`](../src/definitions/Pndctx.v), used only in `pndctx_eq`: two
  `pndctx` values with equal underlying lists are equal, i.e. the bundled
  `NoDup` and `permeable_ctx` proof components are irrelevant.
- **functional extensionality** — introduced by the `Equations` plugin. The
  well-founded-recursion definitions (`search` in
  [`Search_Procedure.v`](../src/proofsearch/Search_Procedure.v),
  `LJFn_decider` / `LJFn_find_min_height` in
  [`LJFn_MinimalHeight.v`](../src/metatheory/LJFn/LJFn_MinimalHeight.v), and the
  `try_Lf` families) generate their unfolding and functional-elimination lemmas
  using it.

Both come from the Rocq ecosystem (Stdlib and the `Equations` plugin) rather
than from anything stated in this repo. Building `src/Global_Results.v` prints
each report under a `==== Assumptions of result N: … ====` banner; as of now they
read:

| Item | Axioms reported |
|---|---|
| `try_decide_sequent` (the extracted function) | none — *Closed under the global context* |
| result 1a — `LJFPS_Sound_With_Respect_To_LJF` | to confirm on rebuild (see below) |
| result 1b — `LJFPS_Complete_With_Respect_To_LJF` | `proof_irrelevance` only (expected, through `LJFPS_Completeness.v`; confirm on rebuild) |
| result 2 — `Derivable_iff_Search_Returns_Some_left` | `functional_extensionality_dep` only |
| result 3 — `Underivable_iff_Search_Returns_Some_Right_or_None` | `functional_extensionality_dep` only |
| result 4 — `decide` | `functional_extensionality_dep` only |

Neither axiom is used everywhere: the spec-equivalence results need at most
proof irrelevance (through `pndctx_eq`, used in
[`LJFPS_Completeness.v`](../src/metatheory/LJFPS/LJFPS_Completeness.v)), and the three
procedure results need only functional extensionality (through the `Equations`
well-founded definitions). Rebuild to confirm; in particular, result 1a has
not been checked separately since the result was split, and its soundness
chain may need no axiom at all.

---

## Report ↔ mechanization

Each numbered result of the report *A Verified Proof Search Procedure for LJF*,
with its Rocq name and file. Paths are relative to `src/`.

| Report | Statement | Rocq name | File |
|---|---|---|---|
| Theorem 1 | Soundness of LJF-4 w.r.t. LJF | `LJF4_soundness` | `metatheory/LJF4/LJF4_Soundness.v` |
| Theorem 2 | Completeness of LJF-4 w.r.t. LJF | `LJF4_completeness` | `metatheory/LJF4/LJF4_Completeness.v` |
| Theorem 3 | Soundness of LJF-O w.r.t. LJF-4 | `LJFO_soundness` | `metatheory/LJFO/LJFO_Soundness.v` |
| Theorem 4 | Completeness of LJF-O w.r.t. LJF-4 | `LJFO_completeness` | `metatheory/LJFO/LJFO_Completeness.v` |
| Lemma 5 | Admissibility of `[]l` in LJF-O | `eager_boxL` | `metatheory/LJFO/LJFO_Exchange.v` |
| Theorem 6 | Exchange in LJF-O | `LJFO_exchange_ordered` | `metatheory/LJFO/LJFO_Exchange.v` |
| Theorem 7 | Soundness of LJF-PS w.r.t. LJF-O | `LJFPS_soundness` (uses `LJFO_structural_cons_weakening`) | `metatheory/LJFPS/LJFPS_Soundness.v` |
| Theorem 8 | Completeness of LJF-PS w.r.t. LJF-O | `LJFPS_completeness` | `metatheory/LJFPS/LJFPS_Completeness.v` |
| Theorem 9 | Soundness of LJF-PS w.r.t. LJF | `LJFPS_Sound_With_Respect_To_LJF` (result 1a below) | `Global_Results.v` |
| Theorem 10 | Completeness of LJF-PS w.r.t. LJF | `LJFPS_Complete_With_Respect_To_LJF` (result 1b below) | `Global_Results.v` |
| Theorem 11 | Enumeration of the search space | `get_all_focus_decision_iff_subsequent`, with `get_all_subsets` | `proofsearch/Focus_Decision_Set.v`, `stdLib/Subsets.v` |
| Definitions 12, 13; Theorem 14 | Search configuration, termination measure, termination | the `Equations … by wf` obligations of `search`, with `stack_length_bound` | `proofsearch/Search_Procedure.v`, `proofsearch/Focus_Decision_Set.v` |
| Theorem 15 | Completeness of LJF-N w.r.t. LJF-PS | `LJFn_completeness` (uses `LJFn_monotone`) | `metatheory/LJFn/LJFn_Completeness.v` |
| Theorem 16 | Minimal-height theorem | `LJFn_find_min_height`, `min_height_exists` (with the bounded decider `LJFn_decider`) | `metatheory/LJFn/LJFn_MinimalHeight.v` |
| Definition 17 | History bounded by `n` | `hist_height_bound` | `metatheory/LJFh/LJFh_Completeness.v` |
| Theorem 18 | Completeness of LJF-H w.r.t. LJF-N | `LJFh_completeness` | `metatheory/LJFh/LJFh_Completeness.v` |
| Theorem 19 | Completeness of LJF-H w.r.t. LJF-PS | `LJFh_completeness_alt` | `metatheory/LJFh/LJFh_Completeness.v` |
| Theorem 20 | Completeness of search w.r.t. LJF-H | `search_complete` | `proofsearch/Search_Completeness.v` |
| Theorem 21 | Soundness and completeness of search w.r.t. LJF-PS | `Derivable_iff_Search_Returns_Some_left` (result 2) | `Global_Results.v` |
| Theorem 22 | Contrapositive of Theorem 21 | `Underivable_iff_Search_Returns_Some_Right_or_None` (result 3) | `Global_Results.v` |
| — | Decision procedure | `decide` (result 4) | `Global_Results.v` |
| — | Type-sorted proof terms | `pterm`, `verify`, `verify_soundness` | `proofsearch/ProofTerms.v`, `proofsearch/ProofTerms_Soundness.v` |

---

## 1. `LJFPS_Sound_With_Respect_To_LJF` and `LJFPS_Complete_With_Respect_To_LJF`

```coq
(* 1a — Theorem 9 of the report *)
(forall C L K, bct C L K -> ufcL (pndctx_list C) L K Unbracketed) /\
(forall C L K, ept C L K -> ufcL (pndctx_list C) L K Bracketed)   /\
(forall C N K, lfc C N K -> lfcL (pndctx_list C) N K)             /\
(forall C K,   rfc C K   -> rfcL (pndctx_list C) K)

(* 1b — Theorem 10 of the report *)
(forall C L K, ufcL C L K Unbracketed -> bct (mk_pndctx C) L K) /\
(forall C L K, ufcL C L K Bracketed   -> ept (mk_pndctx C) L K) /\
(forall C N K, lfcL C N K -> lfc (mk_pndctx C) N K)              /\
(forall C K,   rfcL C K   -> rfc (mk_pndctx C) K)
```

Together these say the search-oriented calculus **LJFPS**
([`LJFPS_Rules.v`](../src/rules/LJFPS_Rules.v)) proves exactly what the **LJF**
specification ([`LJF_Rules.v`](../src/rules/LJF_Rules.v)) proves. Soundness
starts from a `pndctx` and reads its underlying list with `pndctx_list`;
completeness starts from a raw LJF context and builds the `pndctx` with
`mk_pndctx` (deduplicate, keep permeable formulas).

Each is assembled by composing the three rungs between them:

```
  bct C L K
     │  LJFPS_soundness      (LJFPS_Soundness.v)
  bctO (pndctx_list C) L K
     │  LJFO_soundness       (LJFO_Soundness.v)
  bct4 … L K
     │  LJF4_soundness       (LJF4_Soundness.v)
  ufcL … L K Unbracketed          ← 1a: "sound to the spec"

  ufcL C L K Unbracketed
     │  LJF4_completeness    (LJF4_Completeness.v)
  bct4 C L K
     │  LJFO_completeness    (LJFO_Completeness.v)
  bctO C L K
     │  LJFPS_completeness   (LJFPS_Completeness.v)
  bct (mk_pndctx C) L K           ← 1b: "complete w.r.t. the spec"
```

> Note the direction of the claim: LJF is the **trusted spec**. The
> LJF ↔ LJ (ordinary intuitionistic logic) equivalence is Liang & Miller's
> theorem and is *not* re-done here.

## 2. `Derivable_iff_Search_Returns_Some_left`

```coq
forall s : sequent, sequent_derivable s <-> returns_some_proof (try_decide_sequent s)
```

The extracted procedure answers "yes, with a checkable proof" **iff** the
sequent is LJFPS-derivable.

**Forward** (`sequent_derivable s` ⇒ the procedure finds a proof):

```
  bct C L K                                  (sequent_derivable)
     │  LJFn_completeness           (LJFn_Completeness.v)      — pick a height n
  bctn n C L K
     │  LJFh_completeness_alt       (LJFh_Completeness.v)      — with hist_height_bound_nil
  bcth nil C L K
     │  search_complete             (Search_Completeness.v)
  returns_some_proof (try_decide_sequent (Sbct C L K))
```

For `Sept` / `Slfc` the procedure first checks the goal is `bracketable`
(`bracketable_dec`); if not, `LJFPS_bracketable_goal_ept` / `_lfc` shows the
sequent was underivable anyway.

**Backward** (a returned proof is real): `verify_soundness`
([`ProofTerms_Soundness.v`](../src/proofsearch/ProofTerms_Soundness.v)) —
`verify p s → sequent_derivable s`. The `pterm` in `Some (inl (exist _ p V))`
comes with `V : verify p s`, so no trust in `search` itself is required — and
this is the *only* soundness leg below LJFPS: the LJFn / LJFh rungs are used
completeness-only.

## 3. `Underivable_iff_Search_Returns_Some_Right_or_None`

```coq
forall s, ~ sequent_derivable s <->
          returns_some_disproof (try_decide_sequent s) \/ returns_none (try_decide_sequent s)
```

The negative counterpart. `try_decide_sequent` has three outcomes:

| Result | Meaning |
|---|---|
| `Some (inl {p \| verify p s})` | derivable, with a checked proof term |
| `Some (inr H)` | underivable, with `H : ~ sequent_derivable s` |
| `None` | underivable, but the search revisited a focus decision before a full refutation could be assembled — no witness. Still sound by this theorem. |

## 4. `decide`

```coq
Definition decide (s : sequent) : {sequent_derivable s} + {~ sequent_derivable s}.
```

Packs results 2 and 3 into a single decision. `left` unwraps `verify_soundness`
on the returned `pterm`; `right` uses the returned refutation, or — in the
`None` case — result 2 contrapositively.

---

## Asking about LJ provability

`decide` / `try_decide_sequent` take a `sequent` whose context is a `pndctx` — a
duplicate-free list of **permeable** formulas only (negative formulas and
positive atoms). That is the paper's invariant on LJF's unrestricted zone, and
it means **hypotheses do not go in the context**. To decide whether
`A₁, …, Aₙ ⊢ K` holds in LJ, ask

```coq
decide (Sbct pndctx_empty [A₁; …; Aₙ] K)          (* hypotheses in the linear context, bct phase *)
(* or *) decide (Sbct pndctx_empty [] (A₁ → ⋯ → Aₙ → K))
```

The asynchronous `bct` / `ept` phase decomposes the `Aᵢ` and moves their
permeable parts into the context via `boxL`, exactly as LJF intends. Seeding the
`pndctx` directly only accepts permeable formulas and is not the intended
interface — see the rung-0 / rung-3 notes in [ARCHITECTURE.md](ARCHITECTURE.md).

## What the procedure actually terminates on

`search` ([`Search_Procedure.v`](../src/proofsearch/Search_Procedure.v)) recurses
by `Equations … by wf` on the lexicographic triple

```
( length (get_all_focus_decision init) - length stack ,   phase_ranking seq ,   phase_measure seq )
```

- **First component** decreases whenever a focus decision is made: `stack` grows
  by one, and `stack_length_bound`
  ([`Focus_Decision_Set.v`](../src/proofsearch/Focus_Decision_Set.v)) proves a
  `NoDupA` stack of `subsequent`-`init` focus points is strictly shorter than
  the finite set `get_all_focus_decision init`. This is where finiteness comes
  from, and it mirrors LJFh's "no revisits".
- **Second / third components** (`phase_ranking`, `phase_measure` in
  [`Termination_Measures.v`](../src/proofsearch/Termination_Measures.v)) handle
  the asynchronous/focused steps between focus decisions, where the stack is
  unchanged but the phase or the formula gets smaller.

Every recursive call is justified as still a `subsequent init` by the matching
`subp_*` lemma in
[`Subsequent_Preservation.v`](../src/proofsearch/Subsequent_Preservation.v),
which is what keeps the first component well-defined.
