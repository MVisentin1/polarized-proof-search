# polarized-proof-search

A Rocq mechanization of Liang & Miller's focused sequent calculus **LJF** for
propositional intuitionistic logic, refined step by step into a **verified,
executable decision procedure** that returns machine-checked proof terms or
refutations, and extracted to OCaml.

This repository is the mechanization accompanying the report
*A Verified Proof Search Procedure for LJF* (Matteo Visentin). The report is the
reference for the ideas and the proofs; these docs explain how the code is laid
out and point from each result in the report to its Rocq statement
([docs/KEY_RESULTS.md](docs/KEY_RESULTS.md#report--mechanization)). The report
writes the calculi as LJF-4, LJF-O, LJF-PS, LJF-N and LJF-H; in the code they
are the file and judgment suffixes `4`, `O`, `PS`, `n` and `h`.

Everything compiles with no `Admitted`. The five headline results in
[`src/Global_Results.v`](src/Global_Results.v) each end with a
`Print Assumptions`; the classical-logic axioms earlier versions relied on were
removed (commit `b677fa0`). What remains is two axioms: `proof_irrelevance`
(Stdlib `ProofIrrelevance`, used once in
[`Pndctx.v`](src/definitions/Pndctx.v) to equate two `pndctx` values with the
same underlying list) and functional extensionality, pulled in by the
`Equations` plugin for the well-founded-recursion definitions. The extracted
function and the soundness of LJF-PS with respect to LJF use no axioms at all;
completeness of LJF-PS uses only `proof_irrelevance`, and the three search
results use only functional extensionality. See
[docs/KEY_RESULTS.md](docs/KEY_RESULTS.md).

---

## What is LJF and why does it matter?

*Focusing* (Andreoli 1992) is a discipline on sequent proofs that groups rule
applications into maximal **asynchronous** phases (invertible rules, applied
eagerly, no backtracking) and **focused** phases (a single formula is chased
through a chain of non-invertible rules). It collapses huge amounts of
don't-care and don't-know nondeterminism while staying **complete** for the
underlying logic. *Polarization* assigns every connective a polarity — positive
(`∨`, `∧⁺`, `⊤⁺`, `0`, positive atoms) or negative (`→`, `∧⁻`, negative atoms) —
which fixes when it is broken down asynchronously versus under focus.

**LJF** is the intuitionistic member of the focused systems in Liang & Miller,
*"Focusing and polarization in linear, intuitionistic, and classical logics"*
(TCS 410, 2009). In that paper LJF is proved **sound and complete for
propositional intuitionistic logic LJ**.

> **This development does not re-prove the LJF ↔ LJ equivalence.** It *starts*
> from LJF as the trusted specification (the calculus in
> [`src/rules/LJF_Rules.v`](src/rules/LJF_Rules.v)) and builds a decision
> procedure for it, proving every intermediate calculus sound and complete
> against the one above it.

## The idea in one line

LJF is refined until proof search over it is syntax-directed except at the
three points where the nondeterminism is irreducible (the choice of focus, and
the choices inside `∧⁻L` and `∨R`), and that search is then written as a
total Rocq function:

- **LJF-4** splits LJF's asynchronous phase into a *bracketing* phase
  (right-asynchronous work) and an *emptying* phase (left-asynchronous work), by
  removing LJF's star rules. This came out of the earlier COMP 527 work.
- **LJF-O** orders the linear context, so the emptying phase is deterministic.
- **LJF-PS** treats the structural context as a duplicate-free set, so the
  space of focus decisions is finite.
- **LJF-N** and **LJF-H** are proof devices: a height index, then a history of
  focus decisions along a branch. They justify pruning repeated focus decisions,
  which is what makes the search terminate.

Every rule of LJF-4, LJF-O and LJF-PS is an instance of an LJF rule, so the
derivations the search returns are LJF derivations.

    LJF  ⇄  LJF4  ⇄  LJFO  ⇄  LJFPS  ──→  LJFn  ──→  LJFh  ──→  search()
                                  ▲                                 |
                                  |_________________________________|

`⇄` = a proved soundness + completeness pair on derivability, so the prefix
`LJF … LJFPS` proves the same sequents. `LJFPS ──→ LJFn ──→ LJFh ──→ search()`
uses only the **completeness** direction: LJFn and LJFh re-express LJFPS
derivability under successively finer invariants (bounded height, then a
loop-free history) to feed `search_complete`. No soundness leg runs back through
them — it isn't needed, because the return arrow `search() ──→ LJFPS` is
`verify_soundness`: every `pterm` the procedure emits is re-checked against the
LJFPS rules. So a "yes" answer is trustworthy on its own, and a "no" answer 
is backed by the completeness chain.

See **[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)** for the full tour.

## Headline results ([`src/Global_Results.v`](src/Global_Results.v))

| Theorem | Statement |
|---|---|
| `LJFPS_Sound_With_Respect_To_LJF` | every LJFPS derivation gives an LJF derivation (over `pndctx_list C`) |
| `LJFPS_Complete_With_Respect_To_LJF` | every LJF derivation gives an LJFPS derivation (over `mk_pndctx C`) |
| `Derivable_iff_Search_Returns_Some_left` | `sequent_derivable s ↔ try_decide_sequent s` returns a verified proof |
| `Underivable_iff_Search_Returns_Some_Right_or_None` | the negative side |
| `decide` | `∀ s, {sequent_derivable s} + {~ sequent_derivable s}` — full decidability |

## Documentation

| File | Contents |
|---|---|
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | the calculus chain, what each layer changes, which theorem bridges it |
| [docs/FILE_MAP.md](docs/FILE_MAP.md) | every `.v` file, one or two lines each, in compile order |
| [docs/GLOSSARY.md](docs/GLOSSARY.md) | naming conventions: `bct`/`ept`/`lfc`/`rfc`, the `4`/`O`/`n`/`h` suffixes, `pndctx`, `bracketable`, `permeable`, `box`, `_star`, `hist`, `pterm` |
| [docs/KEY_RESULTS.md](docs/KEY_RESULTS.md) | which Rocq lemma proves each numbered result of the report, and a guided read of `Global_Results.v` |
| [docs/BUILDING.md](docs/BUILDING.md) | toolchain, `make`, re-running extraction, running the OCaml driver |

## Quick start

```bash
# Rocq 9.1 + coq-equations in the current opam switch
rocq makefile -f _RocqProject -o Makefile
make -j4

# run the extracted procedure on the bundled examples
cd ocaml && dune exec ./driver.exe
```

## Status

The core development (spec ⇄ LJFPS ⇄ search, decidability) is **done**, with
no `Admitted`.

## Limitations

These follow the Limitations section of the report.

- **Decides LJF, not LJ.** The procedure decides LJF-PS provability, and hence
  LJF provability. Completeness of LJF with respect to LJ is Liang & Miller's
  theorem and is not mechanized here.
- **Derivations live in `Prop`.** Every calculus is a `Prop`-valued relation,
  which extraction erases. The search therefore returns `pterm`s, a `Type`-sorted
  mirror of the LJF-PS rules, together with an erased proof that the `pterm` is
  a derivation ([`ProofTerms.v`](src/proofsearch/ProofTerms.v)). For the same
  reason the soundness and completeness results relate *provability*, not the
  shape of derivations, even though each proof case closes with the
  corresponding rule.
- **Redundant treatment of the structural context.** `pndctx` carries a
  duplicate-free invariant, but contexts along a search path are still compared
  by set equality, so the invariant is redundant. It is also the only reason the
  development needs the `proof_irrelevance` axiom.
- **Propositional fragment only.** Termination rests on the finiteness of the
  focus-decision space, which fails for first-order logic.
- **Performance is unevaluated.** The search space is bounded by the number of
  focus decisions, which is exponential in the size of the input sequent, and no
  results are memoized.

## Future work

These follow the Future Work section of the report.

- **Drop the duplicate-free invariant** and compare multisets by set equality.
  This removes the dependent context type and the `proof_irrelevance` axiom, so
  the search could run directly over LJF-O.
- **Move the derivation relations to `Type`.** The search could then return
  LJF-PS derivations directly, the correspondence between calculi could be stated
  as a function on derivations, and height could be defined by recursion instead
  of through LJF-N.
- **First-order LJF.** The refinement chain looks like it carries over
  unchanged. Proof search would need a fuel bound or a decidable fragment, since
  first-order intuitionistic provability is undecidable.
- **Mechanize completeness of LJF with respect to LJ**, either through focused
  linear logic or through cut elimination for LJF.
- **Performance.** Cache derivations and refutations of sequents reached during
  search, and compare the two ways of comparing contexts.
- **Polarization.** Look for a direct simulation, inside LJF, between two
  polarity assignments of the same formula.

Smaller items in the code itself:

- Thread `permeable_ctx C` through the LJF judgments in `src/rules/LJF_Rules.v`
  (`ufcL` / `lfcL` / `rfcL`), matching on-paper LJF. The context currently
  carries no such condition anywhere; harmless (non-permeable entries are inert)
  but imprecise. LJFPS already enforces it via `pndctx` — see
  [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) (rung 0) and
  [docs/KEY_RESULTS.md](docs/KEY_RESULTS.md#asking-about-lj-provability).
- Five `.v` files sit outside the `_RocqProject` build path:
  `src/examples/LJFPS_Search.v` (the extraction entry point),
  `src/tactics/LJFPS_Prover.v` (an unverified `Ltac` prover kept for reference —
  see Acknowledgements), `src/metatheory/LJFn/LJFn_Soundness.v` (height erasure —
  provable but unused; the LJFn/LJFh chain runs completeness-only), and
  `src/metatheory/LJFPS/LJFPS_Exchange.v` /
  `src/metatheory/LJFO/LJFO_Contraction.v` (spare metatheory, currently unused).
  See [docs/FILE_MAP.md](docs/FILE_MAP.md#not-on-the-build-path).

## Acknowledgements

This project began as a team project for **COMP 527** (McGill), by Dean
Barry, Melvyn Depeyrot, and me, written up as *Mechanizing LJF*. That phase
introduced **LJF-4**, mechanized its rules in Rocq on top of the CARVe context
library, proved its completeness with respect to LJF on paper, and built an
unverified, tactic-based proof procedure for it. CARVe was later dropped: the
linear context of LJF is never split between premises, so CARVe's context-join
operation went unused and the library added more bookkeeping than it saved.

That earlier solver survives here, adapted from LJF4 to LJFPS, as
[`src/tactics/LJFPS_Prover.v`](src/tactics/LJFPS_Prover.v) — kept to show the
extent of the team-phase work. It is unverified, does not terminate on
many sequents, and is off the build path.

Everything past the team phase is my own. That is the verified decision procedure with its
`pterm` / `verify` certificates, the further intermediate calculi (LJFO, LJFPS,
LJFn, LJFh) and their metatheory, the termination measures, and the soundness / completeness proofs
linking every rung.
