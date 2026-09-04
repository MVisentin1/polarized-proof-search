# Building, extracting, running

## Toolchain

| Component | Version used |
|---|---|
| Rocq (Coq) | **9.1.0** (the generated `Makefile` header and `Makefile.conf` record this) |
| OCaml / opam switch | 5.3.0 |
| `coq-equations` | required — every decision procedure is written with `Equations` |
| `dune` | to build and run the extracted OCaml driver |

Install into the current opam switch:

```bash
opam install coq-equations
# Rocq 9.1 itself: opam install rocq-prover.9.1.0   (or your distro's package)
```

`shell.nix` is **not** a build environment — it only launches `vscode-fhs`.
Ignore it unless you use that workflow.

## Build the Rocq library

The `Makefile`, `Makefile.conf` and `.Makefile.d` are **generated** (they are in
`.gitignore`). Regenerate and build:

```bash
rocq makefile -f _RocqProject -o Makefile
make -j4
```

[`_RocqProject`](../_RocqProject) maps `src/` to the logical name `LJF`
(`-R src LJF`) and lists the `.v` files in dependency order. Building
`src/Global_Results.v` (the last entry) exercises the whole development and
prints the four `Print Assumptions` reports.

`src/examples/LJFPS_Search.v` is deliberately **omitted** from `_RocqProject`, so
`make` never re-runs extraction.

## Re-run extraction

After changing anything under `src/`, regenerate the OCaml (two steps, in order):

```bash
make -j4                                              # 1. recompile the library
rocq compile -R src LJF src/examples/LJFPS_Search.v   # 2. re-extract
```

Step 2 writes [`ocaml/ljfps_search.ml`](../ocaml/ljfps_search.ml) and `.mli`
(via `Extraction "ocaml/ljfps_search.ml" try_decide_sequent` with
`ExtrOcamlNatInt`, so Rocq `nat` becomes OCaml `int`). Those two files are
committed in-tree so the procedure can be built and run without a Rocq install.

## Run the procedure

```bash
cd ocaml
dune exec ./driver.exe
```

[`ocaml/driver.ml`](../ocaml/driver.ml) builds sequents by hand, calls
`try_decide_sequent`, pretty-prints the sequent, and renders the returned
`pterm` as a rule tree (`bct_boxR`, `ept_Lf (focus on …)`, …). The OCaml value
you get on success is a `pterm` and nothing else: it is in sort `Type` so it
survives extraction, whereas the `verify p seq` proof and the LJFPS derivation
are in `Prop` and are erased. Correctness was settled in Rocq
(`verify_soundness`), not at runtime — see the "Extraction" note in
[ARCHITECTURE.md](ARCHITECTURE.md). 

Add your own
cases at the bottom of `driver.ml`; the constructors are `Atom (Pos, n)`,
`AndP`, `AndN`, `Or`, `Imp`, `TT`, `FF`, and sequents `Sbct/Sept/Slfc/Srfc`.
Start from `Sbct` with an **empty context** and your hypotheses in the linear
list (or folded into the goal as `Imp`s): the context is a `pndctx`, which only
holds permeable formulas, so it is not where hypotheses go — the `bct` phase
stores them itself. See "Asking about LJ provability" in
[KEY_RESULTS.md](KEY_RESULTS.md).

Output legend:

| Printed | Meaning |
|---|---|
| `=> derivable  (verified pterm):` + tree | `Some (Inl p)`, `verify p seq` holds |
| `=> not derivable  (verified refutation, no witness)` | `Some (Inr _)` |
| `=> not derivable  (search revisited a focus decision, no witness)` | `None` |
