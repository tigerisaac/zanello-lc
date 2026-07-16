# FormalDeps: homological machinery port (toward Hilbert syzygy)

Work toward discharging the one non-Stanley gap of the main development,

```
IsTypeTwoLevel I e → HasGradedResolutionPackage I e
```

whose missing mathematical inputs are minimal graded free resolutions and
graded Matlis duality. The plan of attack: obtain finite global dimension /
Hilbert-syzygy machinery for regular rings, then specialize to the graded
setting.

## Provenance

The files under `Mathlib/` here are taken from the public Mathlib fork
[`Thmoas-Guan/mathlib4_fork`](https://github.com/Thmoas-Guan/mathlib4_fork),
branch `ABS-Criterion-Project-new`, commit `0ff6e01f56` (the
Auslander–Buchsbaum–Serre criterion project by Nailin Guan et al., Apache
2.0), and **ported to this project's toolchain (Lean/Mathlib v4.31.0)**: the
fork is based on a newer Mathlib, so proofs were adapted to v4.31's renamed
APIs.

The port was originally carried out in a `/tmp` staging area by an agent
session on 2026-07-14 that was interrupted before re-integrating its work;
`/tmp` was subsequently cleaned. This tree is a faithful reconstruction:
base files re-fetched from the fork commit, then the session's 43
successfully-applied patches replayed from its rollout log.

## Building

The files keep their upstream `Mathlib.*` module names and are compiled
against a shadow copy of Mathlib's olean tree (ported oleans overwrite the
stock ones):

```sh
lake exe cache get && lake build   # once, for the Mathlib oleans
zsh FormalDeps/shadowbuild.sh
```

## Status (as verified on v4.31.0)

| File | Status |
|---|---|
| `Algebra/Category/ModuleCat/Baer.lean` | compiles |
| `RingTheory/Regular/Category.lean` | compiles |
| `RingTheory/Regular/Depth.lean` | compiles |
| `RingTheory/Regular/Ischebeck.lean` | compiles — `depth_le_supportDim`, `depth_le_ringKrullDim` |
| `RingTheory/Regular/AuslanderBuchsbaum.lean` | compiles — `AuslanderBuchsbaum` |
| `RingTheory/GlobalDimension.lean` | compiles |
| `RingTheory/CohenMacaulay/Basic.lean` | compiles |
| `RingTheory/RegularLocalRing/Basic.lean` | compiles |
| `RingTheory/CohenMacaulay/Maximal.lean` | compiles, **but contains one upstream `sorry`** (line 46, `Nontrivial M` for maximal CM modules) |
| `RingTheory/RegularLocalRing/GlobalDimension.lean` | compiles — `IsRegularLocalRing.globalDimension_eq_ringKrullDim` |
| `RingTheory/RegularLocalRing/RegularRing/Basic.lean` | **not ported** — redeclares `IsRegularRing`, which stock v4.31 already has in `RegularLocalRing/Defs`; needs dedup |
| `RingTheory/RegularLocalRing/RegularRing/Polynomial.lean` | **not ported** (blocked on `RegularRing/Basic`) |
| `RingTheory/RegularLocalRing/RegularRing/GlobalDimension.lean` | **not ported** (blocked on `RegularRing/Basic`) |
| `RingTheory/RegularLocalRing/RegularRing/Syzygy.lean` | **not ported** (blocked on the above) — the Hilbert-syzygy endgame |
| `RingTheory/RegularLocalRing/Defs.lean`, `RingTheory/Regular/IsSMulRegular.lean` | reference only — stock v4.31 already provides these modules; the compiled files above build against the stock versions |

## Caveats

- The one upstream `sorry` means any result depending on
  `CohenMacaulay/Maximal`'s nontriviality lemma would carry `sorryAx`; it
  must be proved (or routed around) before this chain can feed the main
  development's axiom-clean audit.
- Nothing here is imported by `LogConcavity.lean` yet. Even with `Syzygy`
  ported, bridging from finite global dimension to the *graded minimal*
  resolution and duality data of `HasGradedResolutionPackage` remains open
  (see `Scratch.lean` for the graded scaffold built so far).
