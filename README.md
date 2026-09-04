# polarized-proof-search

A Rocq mechanization of Liang & Miller's focused sequent calculus **LJF** for
propositional intuitionistic logic, refined step by step into a **verified,
executable decision procedure** that returns machine-checked proof terms or
refutations, and extracted to OCaml.

Everything compiles with no `Admitted`. The four headline results in
[`src/Global_Results.v`](src/Global_Results.v) each end with a
`Print Assumptions`; the classical-logic axioms earlier versions relied on were
removed (commit `b677fa0`). What remains is two axioms: `proof_irrelevance`
(Stdlib `ProofIrrelevance`, used once in
[`Pndctx.v`](src/definitions/Pndctx.v) to equate two `pndctx` values with the
same underlying list) and functional extensionality, pulled in by the
`Equations` plugin for the well-founded-recursion definitions. See
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

    LJF  ⇄  LJF4  ⇄  LJFO  ⇄  LJFPS  ──→  LJFn  ──→  LJFh  ──→  search()
            split    fix      finite    +height   +history     │
            state    ctx      ctx set   index     (no revisit)  │ verify
            out      order                                      ▼
                                                              LJFPS

`⇄` = a proved soundness + completeness pair on derivability, so the prefix
`LJF … LJFPS` proves the same sequents. `LJFPS ──→ LJFn ──→ LJFh ──→ search()`
uses only the **completeness** direction: LJFn and LJFh re-express LJFPS
derivability under successively finer invariants (bounded height, then a
loop-free history) to feed `search_complete`. No soundness leg runs back through
them — it isn't needed, because the return arrow `search() ──→ LJFPS` is
`verify_soundness`: every `pterm` the procedure emits is re-checked against the
LJFPS rules. (`LJFn_Soundness.v` proves the height-erasure lemma but is unused
and off the build path; there is no `LJFh_Soundness`.) So a "yes" answer is
trustworthy on its own, and a "no" answer is backed by the completeness chain.

See **[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)** for the full tour.

## Headline results ([`src/Global_Results.v`](src/Global_Results.v))

| Theorem | Statement |
|---|---|
| `LJFPS_Sound_And_Complete_To_LJF` | the search-oriented calculus LJFPS is inter-derivable with the LJF spec |
| `Derivable_iff_Search_Returns_Some_left` | `sequent_derivable s ↔ try_decide_sequent s` returns a verified proof |
| `Underivable_iff_Search_Returns_Some_Right_or_None` | the negative side |
| `decide` | `∀ s, {sequent_derivable s} + {~ sequent_derivable s}` — full decidability |

## Documentation

| File | Contents |
|---|---|
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | the calculus chain, what each layer changes, which theorem bridges it |
| [docs/FILE_MAP.md](docs/FILE_MAP.md) | every `.v` file, one or two lines each, in compile order |
| [docs/GLOSSARY.md](docs/GLOSSARY.md) | naming conventions: `bct`/`ept`/`lfc`/`rfc`, the `4`/`O`/`n`/`h` suffixes, `pndctx`, `bracketable`, `permeable`, `box`, `_star`, `hist`, `pterm` |
| [docs/KEY_RESULTS.md](docs/KEY_RESULTS.md) | a guided read of `Global_Results.v` — how the lemmas compose |
| [docs/BUILDING.md](docs/BUILDING.md) | toolchain, `make`, re-running extraction, running the OCaml driver |

## Quick start

```bash
# Rocq 9.1 + coq-equations in the current opam switch
rocq makefile -f _RocqProject -o Makefile
make -j4

# run the extracted procedure on the bundled examples
cd ocaml && dune exec ./driver.exe
```

## Status / roadmap

- Core development (spec ⇄ LJFPS ⇄ search, decidability) — **done**.
- Polarity metatheory (e.g. polarity-assignment invariance, adequacy-style
  lemmas about `positive`/`negative`) — planned.
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

This project began as a team assignment for **COMP 527** (McGill), by Dean
Barry, Melvyn Depeyrot, and the author. That phase built an unverified,
tactic-based proof procedure for a focused intuitionistic calculus — in the same
spirit as the extracted `search` here — carried the calculus chain as far as
**LJF4**, and was written up in a course paper. No metatheory was mechanized at
that stage.

- This repository is a fork of the team repository; everything below is the
  author's own work.
- That earlier solver survives here, adapted from LJF4 to LJFPS, as
  [`src/tactics/LJFPS_Prover.v`](src/tactics/LJFPS_Prover.v) — kept to show the
  extent of the team-phase work. It is unverified, does not terminate on
  many sequents, and is off the build path.

Everything past the team phase is my own. That is the verified decision procedure with its
`pterm` / `verify` certificates, the further intermediate calculi (LJFO, LJFPS,
LJFn, LJFh) and their metatheory, the termination measures, and the soundness / completeness proofs
linking every rung.
