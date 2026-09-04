# Glossary and naming conventions

Once you know the naming scheme the development reads quickly: a name is
**judgment root + calculus suffix**, and there is one file per (calculus,
concern) pair.

## The four judgment roots

| Root | Mnemonic | Meaning |
|---|---|---|
| `bct` | *bracket* | asynchronous phase, goal not yet bracket-checked (the `Unbracketed` mode of the spec). Right rules for negative connectives, `boxR` to enter `ept`. |
| `ept` | *expand* | asynchronous phase past the `boxR` boundary; the goal is `bracketable`. Left rules decompose the linear context; `boxL` moves permeable formulas into the unrestricted context; once the linear context is empty, ends by choosing a focus (`Lf`/`Rf`). |
| `lfc` | *left focus* | focus is on a chosen formula of the unrestricted context; chase it through negative connectives until it matches the goal or releases. |
| `rfc` | *right focus* | focus is on the goal; chase it through positive connectives until it matches the context or releases. |

(`lfc` / `rfc` are unambiguous; `bct` / `ept` are the author's abbreviations for
the two asynchronous judgments — the mnemonics above are a reading aid, not a
claim about the intended expansion.)

In the spec ([`LJF_Rules.v`](../src/rules/LJF_Rules.v)) `bct` and `ept` are one
relation `ufcL C L K state` with `state ∈ {Bracketed, Unbracketed}`:
`ept ≈ ufcL … Bracketed`, `bct ≈ ufcL … Unbracketed`.

## Calculus suffixes

| Suffix | Calculus | What it adds over the previous rung |
|---|---|---|
| `L` (`ufcL`, `lfcL`, `rfcL`) | **LJF** | the specification; `state` flag, `Permutation` left rules |
| `4` (`bct4`, …) | **LJF4** | `state` replaced by two separate judgments |
| `O` (`bctO`, …) | **LJFO** | linear context consumed in fixed order (head-first) |
| *(none)* (`bct`, `ept`, `lfc`, `rfc`) | **LJFPS** | unrestricted context is a `pndctx` (finite dedup'd permeable set) |
| `n` (`bctn n`, …) | **LJFn** | explicit `nat` derivation-height index |
| `h` (`bcth Hs`, …) | **LJFh** | `hist` of visited focus points; no revisits |

Mnemonic for the middle: **4** judgments split out, **O**rdered context,
**P**roof **S**earch context, **n**-height, **h**istory.

## Polarity vocabulary (this development's specifics)

Formulas `o`: `Atom Pos n` / `Atom Neg n`, `TT`, `FF`, `AndP` (∧⁺), `AndN` (∧⁻),
`Or` (∨, positive), `Imp` (→, negative). Propositional only; no quantifiers, no
explicit shift operators — polarity is carried by atoms and by the two
predicates below.

| Predicate | Holds of | Used for |
|---|---|---|
| `positive` | positive atoms, `TT`, `FF`, `AndP`, `Or` | eligible for right focus (`rfc`) |
| `negative` | negative atoms, `AndN`, `Imp` | eligible for left focus (`lfc`) |
| `atomic` | `Atom _ _` | init rules |
| `bracketable` | `positive`, **or** a negative atom | allowed as an `ept`/`lfc` **goal**; gate for `boxR` |
| `permeable` | `negative`, **or** a positive atom | allowed to enter the unrestricted context; gate for `boxL` |

`bracketable` and `permeable` are near-duals: every formula is one or the other,
and the atoms are both. `permeable_ctx C := Forall permeable C`.

## Rule-name affixes

| Affix | Meaning |
|---|---|
| `boxR` | cross from `bct` to `ept` once the goal is `bracketable` (`[·]` bracket boundary on the right) |
| `boxL` | move a `permeable` linear-context formula `B` into the unrestricted context `C` |
| `Lf` / `Rf` | end an `ept` phase by choosing **l**eft / **r**ight **f**ocus |
| `Rl` / `Rr` | **r**elease **l**eft / **r**ight focus back to the asynchronous phase |
| `Il` / `Ir` | **i**nit on the **l**eft / **r**ight (focused formula = goal / in context) |
| `_star` (`ufcL_boxL_star`, …) | **LJF only** — the copy of a left rule that runs in `Unbracketed` mode; gone from LJF4 onward |
| `_1` / `_2` | the two premises/choices of a binary rule (`AndNL_1`, `OrR_2`, …) |
| `_inv` | inversion lemma for that rule (`ept_boxL_inv`) |
| `subp_*` | "subsequent preservation" for that step ([`Subsequent_Preservation.v`](../src/proofsearch/Subsequent_Preservation.v)) |

## Contexts

| Name | Type | Meaning |
|---|---|---|
| `sctx`, `lctx`, `octx` | `list o` | notations: **s**tructural (unrestricted), **l**inear, **o**rdered — all `list o`, the name signals intent |
| `C` | `sctx` or `pndctx` | unrestricted / structural context (left of `;`) |
| `L` | `lctx` / `octx` | linear context being decomposed |
| `K` | `o` | goal |
| `N`, `P` | `o` | a **n**egative / **p**ositive formula under focus |
| `pndctx` | `{ C : sctx \| NoDup C & permeable_ctx C }` | **p**ermeable **n**o-**d**up context; see [`Pndctx.v`](../src/definitions/Pndctx.v). Enforces the paper's "unrestricted zone = permeable only" invariant, so hypotheses go in the linear context, not here — see [KEY_RESULTS.md](KEY_RESULTS.md#asking-about-lj-provability) |
| `pndctx_list C` | `sctx` | the underlying list |
| `pndctx_insert B C` | `pndctx` | add `B` if permeable and not already present (else `C` unchanged) |
| `mk_pndctx l` | `pndctx` | `filter permeable_b (nodup … l)` |
| `pndctx_set_eq`, `pndctx_o_eq` | relations | equality up to `equivlistA` (set equality) of contexts / `(context, goal)` pairs |

## Procedure vocabulary

| Name | Meaning |
|---|---|
| `sequent` | `Sbct C L K` / `Sept C L K` / `Slfc C N K` / `Srfc C K` — a judgment goal as data |
| `sequent_derivable s` | the corresponding LJFPS proposition |
| `subsequent S S0` | every formula in `S` is a subformula of `S0`, in the correct polarity bucket |
| `hist` | `list (pndctx * o)` — visited focus points (LJFh); called `stack` in `search` |
| `get_all_focus_decision init` | finite superset of all reachable focus points = subsets(permeable subformulas) × bracketable subformulas |
| `phase_ranking` / `phase_measure` | 2nd / 3rd components of the termination triple |
| `pterm` | first-order proof term, one constructor per LJFPS rule (`pbct_boxR`, `pept_Lf`, …) |
| `verify p seq` | checker relation: `p` is a valid LJFPS derivation of `seq` |
| `try_decide_sequent s` | entry point → `Some (inl {p \| verify p s})` \| `Some (inr ¬deriv)` \| `None` |
| `returns_some_proof` / `_disproof` / `returns_none` | predicates classifying that result |
