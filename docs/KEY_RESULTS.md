# Key results — a guided read of `Global_Results.v`

[`src/Global_Results.v`](../src/Global_Results.v) is the file to open first. It
imports the whole development and states four theorems, each followed by
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
| result 1 — `LJFPS_Sound_And_Complete_To_LJF` | `proof_irrelevance` only |
| result 2 — `Derivable_iff_Search_Returns_Some_left` | `functional_extensionality_dep` only |
| result 3 — `Underivable_iff_Search_Returns_Some_Right_or_None` | `functional_extensionality_dep` only |
| result 4 — `decide` | `functional_extensionality_dep` only |

Neither axiom is used everywhere: the spec-equivalence result needs only proof
irrelevance (through `pndctx_eq` / `pndctx_list_mk_commute`), and the three
procedure results need only functional extensionality (through the `Equations`
well-founded definitions). Rebuild to confirm.

---

## 1. `LJFPS_Sound_And_Complete_To_LJF`

```coq
(forall C L K, bct C L K <-> ufcL (pndctx_list C) L K Unbracketed) /\
(forall C L K, ept C L K <-> ufcL (pndctx_list C) L K Bracketed)   /\
(forall C N K, lfc C N K <-> lfcL (pndctx_list C) N K)             /\
(forall C K,   rfc C K   <-> rfcL (pndctx_list C) K)
```

The search-oriented calculus **LJFPS** ([`LJFPS_Rules.v`](../src/rules/LJFPS_Rules.v))
proves exactly what the **LJF** specification
([`LJF_Rules.v`](../src/rules/LJF_Rules.v)) proves.

It is assembled by composing the three rungs between them, each direction
separately:

```
  bct C L K
     │  LJFPS_soundness      (LJFPS_Soundness.v)
  bctO (pndctx_list C) L K
     │  LJFO_soundness       (LJFO_Soundness.v)
  bct4 … L K
     │  LJF4_soundness       (LJF4_Soundness.v)
  ufcL … L K Unbracketed          ← "sound to the spec"

  ufcL … L K Unbracketed
     │  LJF4_completeness    (LJF4_Completeness.v)
  bct4 … L K
     │  LJFO_completeness    (LJFO_Completeness.v)
  bctO … L K
     │  LJFPS_completeness   (LJFPS_Completeness.v)  — via mk_pndctx
  bct C L K                       ← "complete w.r.t. the spec"
```

The completeness leg uses `pndctx_list_mk_commute` (`C = mk_pndctx (pndctx_list C)`)
to line the `pndctx` back up after `LJFPS_completeness` rebuilds it from a raw
list.

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
