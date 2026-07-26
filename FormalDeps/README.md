# FormalDeps: ported homological prerequisites

Mathlib v4.31 has a generic functorial projective-resolution API, but the
main development also needs finite global dimension for the polynomial ring —
**Hilbert's Syzygy Theorem** — together with the depth machinery it rests on.
This directory supplies them.

What the main development uses from here:

```lean
theorem Hilberts_Syzygy (k : Type u) [Field k] [Small.{v, u} k] (n : ℕ) :
    globalDimension.{v} (MvPolynomial (Fin n) k) = n
```

surfaced through `FormalDepsBridge.lean` as `FormalDeps.hilbertsSyzygy` and
`FormalDeps.projectiveDimensionLEOfPolynomial`, and consumed in
`GradedResolution.lean` as `r3_globalDimension` / `r3_projectiveDimensionLE`.
That bound is what makes the third syzygy of the Matlis dual projective,
hence — with the graded-Nakayama/determinant argument in
`GradedResolution.lean` — free, giving the injectivity of `d₃` in the paper's
display (1). `ModuloStanley.lean` additionally imports the Rees/depth
material directly.

## Provenance

The files under `Port/` are taken from the public Mathlib fork
[`Thmoas-Guan/mathlib4_fork`](https://github.com/Thmoas-Guan/mathlib4_fork),
branch `ABS-Criterion-Project-new`, commit `0ff6e01f56` — the
Auslander–Buchsbaum–Serre criterion project by Nailin Guan, Yongle Hu et al.,
Apache-2.0 — and **ported to this project's toolchain** (Lean/Mathlib
v4.31.0). The fork is based on a newer Mathlib, so proofs were adapted to
v4.31's renamed APIs. The files keep their upstream declaration names,
copyright headers and author attributions; only their `import` lines are
rewritten to the `FormalDeps.Port.Mathlib.*` module path, so that they build
alongside stock Mathlib rather than shadowing it.

These files remain under the Apache-2.0 licence of their origin, not the MIT
licence of the rest of this repository.

## Verifying the port

Proofs necessarily differ from upstream — that is what porting is. The
statements must not. `verify-port.sh` checks this mechanically: it fetches
each file from the upstream commit and compares the statement of every
theorem and lemma present in both.

```sh
sh FormalDeps/verify-port.sh    # needs curl, python3, network access
```

Current result: **131 shared statements compared, 0 differ.** One is reported
as a known equivalence — the port writes `_root_.Submodule.comap` where
upstream writes `comap`, resolving to the same constant — and is listed
explicitly in the script rather than silently normalized. Five auxiliary
upstream lemmas are not carried over, which the script also reports; nothing
is added. `Hilberts_Syzygy` and `AuslanderBuchsbaum` match upstream
character for character.

## Axiom audit

The audit runs inside the ordinary `lake build`: `FormalDepsBridge.lean` ends
with `#print axioms` for every result imported from here, so CI checks them
on every run along with everything else. All report
`[propext, Classical.choice, Quot.sound]`.

There is one `sorry` in the tree, at
`Port/Mathlib/RingTheory/CohenMacaulay/Maximal.lean:46`. It sits inside a
`/- … -/` block comment, it is present in the upstream original, and it is
therefore not part of any proof — the axiom audit is what actually
establishes that nothing depends on it.

## Contents

| File | Key results |
|---|---|
| `Algebra/Category/ModuleCat/Baer.lean` | Baer criterion Ext machinery |
| `RingTheory/Regular/Category.lean`, `Depth.lean` | depth via Ext |
| `RingTheory/Regular/Ischebeck.lean` | `depth_le_supportDim`, `depth_le_ringKrullDim` |
| `RingTheory/Regular/AuslanderBuchsbaum.lean` | `AuslanderBuchsbaum` |
| `RingTheory/GlobalDimension.lean` | `globalDimension`, localization principle |
| `RingTheory/CohenMacaulay/Basic.lean`, `Maximal.lean` | CM modules; MCM over regular local ⇒ free |
| `RingTheory/RegularLocalRing/Basic.lean` | regular local ring facts |
| `RingTheory/RegularLocalRing/GlobalDimension.lean` | `IsRegularLocalRing.globalDimension_eq_ringKrullDim` |
| `RegularRing/Basic.lean` | shim — stock v4.31 `Defs` already provides `IsRegularRing` |
| `RegularRing/Polynomial.lean` | regularity of `R[X]`, `MvPolynomial (Fin n) R` |
| `RegularRing/GlobalDimension.lean` | `IsRegularRing.globalDimension_eq_ringKrullDim` |
| `RegularRing/Syzygy.lean` | **`Hilberts_Syzygy`**: `globalDimension (MvPolynomial (Fin n) k) = n` |

Stock v4.31 already provides `RingTheory/RegularLocalRing/Defs.lean` and
`RingTheory/Regular/IsSMulRegular.lean`; the build uses the stock versions and
they are not vendored here.

## Porting notes

Beyond mechanical import rewriting, the last four files needed real
adaptation to v4.31: it renamed/privatized `Ideal.primeHeight` (use
`Ideal.height` with `Ideal.sup_isMaximal_height_eq_ringKrullDim` and
`Ideal.height_add_one_le_of_lt_of_isPrime`), renamed
`comap_map_of_isPrime_disjoint` to `under_map_of_isPrime_disjoint`, and
provides `IsLocalRing.ker_residue` and `Polynomial.height_map_C`. One
localization instance-path defeq (OreLocalization vs `CommRing`-derived) is
not exposed across `module` boundaries; `Polynomial.lean` pins it with named
type arguments plus `by with_unfolding_all exact …`.
