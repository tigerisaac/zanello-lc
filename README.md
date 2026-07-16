# Lean verification: Log-concavity of codimension-three level Hilbert functions of type two

A Lean 4 + Mathlib formalization of the proof of:

> **Theorem 1.** Let `A = R/I` (`R = k[x₁,x₂,x₃]`, `k` any field) be a standard
> graded Artinian level algebra of embedding dimension three, socle degree `e`,
> and type two. Then its Hilbert function is log-concave:
> `hᵢ² ≥ h_{i-1} h_{i+1}` for `1 ≤ i ≤ e−1`.

All Lean code is in [`LogConcavity.lean`](LogConcavity.lean). Dependencies
are pinned by `lean-toolchain` and `lake-manifest.json`.

## Verification status

`lake build` succeeds with **zero `sorry`**, and `#print axioms` reports only
Lean's standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`) for every theorem — no hidden axioms.

## What is machine-checked

The development derives Theorem 1 from the *primitive numerical shadows* of
the paper's commutative algebra. Everything the paper does on pp. 2–4 —
every identity, inequality, sum manipulation, and case split — is formally
verified:

| Paper step | Lean theorem |
|---|---|
| `2Nⱼ = (j+1)(j+2)`, Pascal recursion, strict monotonicity | `two_mul_N`, `N_succ`, `N_strictMono` |
| First/second differences of `N` extended by zero | `Nz_diff`, `Nz_second_diff` |
| ε=1 case: windows `(N_m, N_{m−1}, N_{m−2})` are log-concave | `binomial_window_log_concave`, `Nz_window` |
| Hilbert-numerator computation `Δ²g_d = 2 + Q_d − P_{<d} − p_d` (from rank additivity of complex (1)) | `shiftSum_second_diff` + inside `deep_dispatch` |
| Central estimate (4) from (3), and (5) ⇒ (6) (`p_d = 0`, `Δ²g_d = 1`) | inside `deep_dispatch` |
| AM–GM step: `Δ² ≤ 0 ⇒ ac ≤ b²` | `amgm_log_concave` |
| r=0 case: evaluation `g = (d(d−1), d(d+1), (d+1)(d+2)−p_d)` and margin `> 0` | `deep_dispatch`, `r_eq_zero_log_concave` |
| Inequality (9): `2d ≤ e+2` from `N_{d−1} ≤ g_{d−1} ≤ N_{e−d+1}` | inside `deep_dispatch` |
| `x = g_{d−1} − g_{d−2} = d + a + D ≥ d`, `g_{d−2} ≤ d(d−1)` (via (8), Stanley) | inside `deep_dispatch` |
| r=1 failure margin `x² − y ≥ d > 0` | `r_eq_one_log_concave` |
| Full scenario case analysis | `GoodTriple.log_concave`, `deep_dispatch` |
| Reversal transfer `g → h` | `theorem1`, `theorem1_full` |

In addition, the **structural layer** machine-checks the abstract algebra
behind the imported hypotheses, in the exact form the paper uses it:

| Paper step | Lean theorem |
|---|---|
| (2): 1-dim kernel spanned by a full-support vector ⇒ every proper subset of columns independent | `proper_subfamily_linearIndependent` |
| (3): rank inequality `Q_d − ε_d ≤ P_{<d} − r_d` from the graded zero pattern of a minimal matrix | `rank_estimate`, `rank_estimate_graded` |
| UFD lemma `(Kv) ∩ R² = Rv` for a primitive vector (Euclid's-lemma step) | `primitive_line_saturated`, `primitive_line_saturated_fraction` |
| Passage from the low-shift image to `vJ`; truncated-kernel identity (7), `cv ∈ (vJ) ⟺ c ∈ J` | `line_factorization` |
| Nonzero cyclic submodule of a finite-length module with simple socle ⇒ Artinian quotient with simple socle | `cyclic_submodule_simple_socle` |

## The formal algebraic input and resolution bridge

The **formal-algebra layer** defines the paper's actual starting object in
Lean: `R = k[x₁,x₂,x₃]` with its monomial grading, a homogeneous ideal `I`,
the graded quotient `A = R/I` with graded pieces `quotPiece I n` (images of
`Rₙ`), its Hilbert function `hilb I : ℤ → ℤ`, its socle, and the predicate
`IsTypeTwoLevel I e` — Artinian, embedding dimension three, socle
concentrated in degree `e`, type two. Machine-checked from that object:

| Statement | Lean theorem |
|---|---|
| `dim_k Rₙ = binom(n+2,2) = N n` (monomial basis, stars and bars) | `finrank_homogeneousSubmodule` |
| `h_t ≥ 0` and `h_t ≤ N_t` — hypotheses `hnn`, `hquot` **derived** | `hilb_nonneg`, `hilb_le_Nz` |
| Profile of the paper: `h₀ = 1`, `h₁ = 3`, `h_e = 2`, `h_t = 0` for `t > e` (socle = top piece), hence `2 ≤ e` | `hilb_zero`, `IsTypeTwoLevel.hilb_one`, `IsTypeTwoLevel.hilb_top`, `IsTypeTwoLevel.hilb_vanish`, `IsTypeTwoLevel.socle_eq`, `IsTypeTwoLevel.two_le_socleDegree` |
| Gorenstein bounds — hypothesis `hGor` **derived** over the *concrete* predicate `GorensteinQuotientHF` (graded Artinian quotient of `R` with one-dimensional socle in degree `E`) | `GorensteinQuotientHF.bounds` |

The new resolution bridge replaces the old arbitrary functions `g,p,q,r,ε`
by proof-carrying algebraic data:

| Checklist step | Lean object / theorem |
|---|---|
| finite Betti bases and genuine shift multiplicities | `GradedResolutionDuality`, `shiftMultiplicity`, `sum_shiftMultiplicity_Icc` |
| the pieces `M_d = Hom_k(A_{e-d},k)` and `g_d=h_{e-d}` | `gradedDualPiece`, `reversedHilb`, `finrank_gradedDualPiece` |
| Hilbert-series coefficients from actual degreewise exact maps (not a numerical field) | `ExactPresentation.finrank_add`, `GradedResolutionDuality.hilbert_series` |
| localized low-shift matrices form a complex | `lowδ₂`, `lowδ₁`, `low_complex` |
| `ε_d` and `r_d` are actual nullity/rank; `(3)` follows | `resolutionEpsilon`, `resolutionRank`, `rank_epsilon_cases`, `rank_inequality` |
| properness gives the upper shift bound; homogeneous generators give no lower-degree ideal elements | `qShift_le_of_proper`, `ideal_no_low_degree` |
| `ε_d=1` gives the full binomial window | `all_qShift_le_of_epsilon_one`, `epsilon_one_full_hilbert` |
| `r_d=0` gives `P_{<d}=0` | `rank_zero_no_low_shifts` |
| primitive line, coefficient ideal, and low annihilator chain | `CriticalBranchCertificate`, `line_coefficient_eq_annihilator_low` |
| critical presentation dimension from a surjective map and its actual kernel | `SurjectivePresentation.finrank_add`, `CriticalBranchCertificate.presentation_dimension` |
| actual Gorenstein annihilator quotient | `GorensteinAnnihilatorData.toGorensteinQuotientHF` |
| degreewise ideal/quotient dimension split and equation (8) | `idealPiece_finrank_add_quotPiece`, `idealHilb_add_hilb`, `CriticalBranchCertificate.equation8` |

`theorem1_of_resolution` feeds all of these derived facts into
`theorem1_full`. Its user-visible mathematical inputs are the actual level
algebra, a certified `GradedResolutionDuality`/`ResolutionPackage` pair,
and Stanley's theorem. It no longer asks separately for `hrev`, `hres`, `hrε`, `h3`,
`hε1`, `hr0`, `hr1`, or `hGor`.
`theorem1_of_hasGradedResolutionPackage` bundles the whole non-Stanley input
as the single named proposition `HasGradedResolutionPackage I e`.

## Remaining trust boundary

Mathlib 4.31 has a generic functorial projective-resolution API, but no
minimal **graded** free resolutions, Hilbert-syzygy bridge, or graded
Matlis-duality theory. Consequently the repository still cannot
prove the *existence* of `GradedResolutionDuality`/`ResolutionPackage` from
`IsTypeTwoLevel I e`. In exact Lean terms, the missing theorem is
`IsTypeTwoLevel I e → HasGradedResolutionPackage I e`. The package is deliberately proof-carrying: it
contains finite bases and shifts, localized matrices, the last
differential's full-support generator vector, degreewise exact linear maps,
and the graded critical-branch construction. Once such a
package is supplied, all former numerical assumptions are theorems listed
above. In particular, the package now carries exact linear maps rather than
the Hilbert-series and critical presentation dimension equalities; both
equalities are kernel-checked consequences of rank–nullity.

Stanley's monotonicity theorem is the other explicit input. Thus the new
result is end-to-end **conditional on the missing resolution/duality
existence theorem and Stanley**, not yet a theorem modulo Stanley alone.
This distinction is reflected directly in the signature of
`theorem1_of_resolution`; no `sorry`, custom axiom, or opaque numerical
hypothesis hides it.

The legacy `theorem1_full` and `theorem1_of_level` are retained for
compatibility and for the numerical consistency witness.

## Numerical consistency witness

Assumed hypotheses could in principle be mutually contradictory, making the
theorem vacuous. The `NumericalConsistencyWitness` section rules this out:
for the numerical data computed from the level algebra
`A = R/Ann(X², Y²+XZ)` — Hilbert function `(1,3,2)`, socle degree 2, type
two, dual resolution `F₁ = R(−1)³⊕R(−2)²`, `F₂ = R(−3)⁴`, `s = 5`, rank
data `r₂ = 2, ε₂ = 0` — **every hypothesis of `theorem1_full` is
machine-verified** (`consistency_witness`), and the theorem delivers the
concrete inequality `h₀h₂ = 2 ≤ 9 = h₁²`. (The algebra itself is not
constructed in Lean; the witness certifies exactly that the hypothesis set
is jointly satisfiable, no more.)

## Reproducing

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get   # fetch the prebuilt Mathlib binary cache
lake build           # expect: Build completed successfully + axiom audit lines
```

Setup: Lean `v4.31.0`, Mathlib `v4.31.0` (pinned in `lean-toolchain` /
`lake-manifest.json`).

## Continuous integration

[`.github/workflows/ci.yml`](.github/workflows/ci.yml) builds the project
with `lake build` from a clean checkout on every push and pull request,
records the full `#print axioms` audit in the job summary and as an
artifact, and **fails the build** if any audited theorem depends on
anything beyond Lean's three standard foundational axioms.
