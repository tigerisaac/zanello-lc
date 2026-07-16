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

## Status (as verified on v4.31.0): the full chain compiles

Every file compiles and `AxiomAudit.lean` confirms the key theorems —
including `Hilberts_Syzygy`, `AuslanderBuchsbaum`,
`depth_le_ringKrullDim` (Ischebeck),
`free_of_isMaximalCohenMacaulay_of_isRegularLocalRing`,
`IsRegularLocalRing.globalDimension_eq_ringKrullDim`, and
`MvPolynomial.isRegularRing_of_isRegularRing` — depend only on `propext`,
`Classical.choice`, `Quot.sound`. (The lone `sorry` visible in
`CohenMacaulay/Maximal.lean` sits inside a block comment; the audit
proves nothing depends on it.)

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
| `RingTheory/RegularLocalRing/Defs.lean`, `RingTheory/Regular/IsSMulRegular.lean` | reference only — stock v4.31 provides these; the build uses the stock versions |

Porting notes for the final four files (beyond the recovered session's
work): stock v4.31 renamed/privatized `Ideal.primeHeight` (use
`Ideal.height` and `Ideal.sup_isMaximal_height_eq_ringKrullDim`,
`Ideal.height_add_one_le_of_lt_of_isPrime`), renamed
`comap_map_of_isPrime_disjoint` to `under_map_of_isPrime_disjoint`, and
provides `IsLocalRing.ker_residue` and `Polynomial.height_map_C`. One
localization instance-path defeq (OreLocalization vs `CommRing`-derived)
is not exposed across `module` boundaries; `Polynomial.lean` pins it with
named type arguments plus `by with_unfolding_all exact ...`.

## Remaining gap to the main development

Nothing here is imported by `LogConcavity.lean` yet. `Hilberts_Syzygy`
supplies the abstract finiteness input (global dimension of
`k[x₁,x₂,x₃]` is 3), but bridging from categorical projective dimension
to the *graded minimal* resolution-with-shifts and duality data of
`HasGradedResolutionPackage` (graded Matlis duality, minimality, the
critical-branch construction) remains open — see `Scratch.lean` for the
graded scaffold built so far.
