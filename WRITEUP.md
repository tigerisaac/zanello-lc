# Full Writeup: Lean Verification of "Log-concavity of codimension-three level Hilbert functions of type two"

## 1. What was built

A fully self-contained Lean 4 verification environment in this repository's
root folder — nothing installed outside it:

- **Toolchain**: Lean 4.31.0 (via elan, pinned in `lean-toolchain`)
- **Library**: Mathlib (release v4.31.0) with its prebuilt binary cache
- **The formalization**: `LogConcavity.lean` (~2200 lines), documentation in
  `README.md`

To re-verify, with elan installed:

```sh
lake exe cache get
lake build
```

The build ends with an axiom audit showing every theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` — Lean's three standard
foundational axioms. There are **no `sorry`s and no custom axioms** anywhere.

## 2. Architecture of the proof

**Layer 0 — Hilbert function of `R = k[x₁,x₂,x₃]`.**
`N j = C(j+2,2)` and its zero-extension `Nz` to integer degrees, with the
closed form `2Nⱼ = (j+1)(j+2)`, Pascal recursion, strict monotonicity, the
first difference `Nz t − Nz(t−1) = t+1`, and the second difference
`Δ²Nz = 1` on nonnegative degrees (the numerical content of the Hilbert
series of `R`). All proved.

**Layer 1 — the four scenarios imply log-concavity.**
The paper's case analysis distills each tested triple
`(g_{d−2}, g_{d−1}, g_d)` into one of four shapes (`GoodTriple`); each is
proved log-concave:

- binomial windows `(N_m, N_{m−1}, N_{m−2})` (the ε_d = 1 case);
- the AM–GM step (`Δ²g_d ≤ 0` implies the inequality);
- the r_d = 0 margin `g_{d−1}² − g_{d−2}g_d = d(2(d+1)+(d−1)p_d) > 0`;
- the r_d = 1 failure margin `x² − y ≥ d² − d(d−1) = d > 0`.

**Structural layer — the local algebra behind the imported hypotheses.**
Five theorem-specific abstract lemmas are now fully machine-checked, in the
exact form the paper uses them:

- `proper_subfamily_linearIndependent` — paper (2): if the space of linear
  dependencies of a finite family is the line spanned by a full-support
  vector, every proper subfamily is linearly independent;
- `rank_estimate`, `rank_estimate_graded` — paper (3): from `ψ ∘ φ = 0`,
  `dim ker φ ≤ ε`, and the graded zero pattern (the restricted `δ₂` lands in
  the span `W'` of the low-shift rows), rank–nullity gives
  `Q_d + r_d ≤ P_{<d} + ε_d`;
- `primitive_line_saturated`(`_fraction`) — the UFD lemma
  `(Kv) ∩ R² = Rv` for a primitive vector over a GCD domain (Euclid's-lemma
  step, stated both in cleared-denominator form and literally over
  `Frac(R)`);
- `line_factorization` — the passage from the low-shift image to `vJ`: a map
  into `Rⁿ` with image on the line through a nonzero `v` factors through a
  scalar map `ψ` with ideal `J = range ψ`, `im φ = vJ`,
  `cv ∈ (vJ) ⟺ c ∈ J`, and the truncated-kernel identity
  `ker ψ = ker φ` (paper (7));
- `cyclic_submodule_simple_socle` — a nonzero cyclic submodule of a
  finite-length module with simple socle again has simple socle, and the
  cyclic quotient `R ⧸ Ann(x)` is an Artinian module isomorphic to it
  (via a local lattice-theoretic development of the socle, `socleOf`).

**Layer 2 — from resolution numerics to the scenarios (`deep_dispatch`).**
This is the deep part. Starting only from the *numerical shadows* of the
commutative algebra, Lean derives the paper's entire reduction:

- the telescoping identity turning rank additivity of the complex
  `0 → R(−s) → F₂ → F₁ → R² → M → 0` into
  `Δ²g_d = 2 + Q_d − P_{<d} − p_d` (formalized as `shiftSum_second_diff`,
  a genuine finite-sum argument over shift multisets);
- the central estimate (4) from the rank inequality (3);
- the proof that a putative failure under `r_d = 1` forces equation (6)
  (`p_d = 0`, `Δ²g_d = 1`);
- inequality (9) `2d ≤ e+2`, from squeezing `g_{d−1}` between `N_{d−1}` and
  `N_{e−d+1}` using strict monotonicity of `N`;
- the computation `x = g_{d−1} − g_{d−2} = d + a + D ≥ d` using
  equation (8) and Stanley monotonicity of `B` (including the boundary case
  `n − 2 < 0` and the paper's `H = 0` case `B = 0`) — Stanley's theorem
  itself enters only through the separately named hypothesis `hStanley`;
- the bound `g_{d−2} ≤ 2N_{d−2} = d(d−1)`;
- the explicit evaluation of the r_d = 0 triple
  `(d(d−1), d(d+1), (d+1)(d+2) − p_d)` from the resolution formula, via
  `P_{<d} = 0` and nonnegativity forcing `Q_d = 0`.

**Assembly.** `theorem1_full` chains Layer 2 → Layer 1 → the reversal
transfer `g_d = h_{e−d}`, concluding `h_{i−1}h_{i+1} ≤ h_i²` for
`1 ≤ i ≤ e−1`.

**Formal-algebra layer (`theorem1_of_level`).**
The paper's actual starting object, formalized (roadmap item 1):
`R = k[x₁,x₂,x₃]` with its monomial grading, a homogeneous ideal `I`, the
graded quotient `A = R/I` with graded pieces `quotPiece I n` (images of
`Rₙ`), Hilbert function `hilb I : ℤ → ℤ`, socle, and the predicate
`IsTypeTwoLevel I e` — `I` homogeneous and proper, no linear forms in `I`
(embedding dimension three), `A` finite-dimensional (Artinian), graded
pieces vanishing above `e`, socle contained in the degree-`e` piece
(levelness) and of dimension two (type two). Machine-checked from it:

- the dimension count `dim_k Rₙ = binom(n+2,2) = N n`, via the identification
  of `Rₙ` with finitely supported functions on degree-`n` exponent vectors
  and the stars-and-bars count (`finrank_homogeneousSubmodule`);
- `hnn` and `hquot` as theorems: `hilb_nonneg`, `hilb_le_Nz`;
- faithfulness of the definition — the formal object provably has the
  paper's profile: `h₀ = 1` (a nonzero constant in `I` would be a unit),
  `h₁ = 3` (no linear forms), `h_e = 2` (the socle *equals* the top piece:
  the reverse containment follows from `vanish_above` and the graded
  structure `quotPiece_X_mul`), and `h_t = 0` above `e`; comparing the top
  dimension with degrees zero and one also proves `2 ≤ e`
  (`IsTypeTwoLevel.two_le_socleDegree`);
- a **concrete Gorenstein predicate** `GorensteinQuotientHF B E` — "`B` is
  the Hilbert function of a graded Artinian quotient of `R` with
  one-dimensional socle concentrated in degree `E`" — with `hGor` as a
  theorem (`GorensteinQuotientHF.bounds`).

`theorem1_of_level` restates Theorem 1 from `IsTypeTwoLevel I e`, deriving
`hnn`/`hquot`/`hGor` and instantiating the abstract `Gor` at
`GorensteinQuotientHF` — so its `hStanley` hypothesis is a faithful
statement of Stanley's theorem about actual Gorenstein quotients of
`k[x₁,x₂,x₃]`, and every remaining hypothesis is a proposition about the
concrete `hilb I`, i.e. a precisely specified open lemma for roadmap items
2–10.

**Resolution-to-numerics bridge (`theorem1_of_resolution`).**
The development now also has a proof-carrying interface for those roadmap
items. `GradedResolutionDuality` contains finite homogeneous bases, shift
functions, localized matrices, the full-support last-differential vector,
and actual degreewise exact linear presentations. Betti functions are
defined as cardinalities of shift fibres. `ExactPresentation.finrank_add`
and rank–nullity derive the Hilbert-series coefficients; the integer identity
is no longer a certificate field. Properness plus the full-support
homogeneous generators likewise derive the upper shift bound and the
absence of lower-degree elements of `I`. The restricted maps `lowδ₂` and
`lowδ₁` define `resolutionEpsilon` and `resolutionRank` as actual finranks.
Lean then proves the complex identity, the rank alternatives, inequality
(3), the `ε=1` window, and the `r=0` vanishing consequence.

For the critical branch, `CriticalBranchCertificate` carries the primitive
homogeneous vector and the actual coefficient and annihilator ideals.
Its former numerical presentation-dimension field is replaced by an actual
surjective linear presentation whose kernel is equivalent to the graded
kernel piece; `SurjectivePresentation.finrank_add` derives the dimension
formula. The low ideal-piece equality is derived from homogeneous
membership equivalence rather than stored directly.
`line_coefficient_eq_annihilator_low` formalizes the membership chain before
(8), `GorensteinAnnihilatorData` constructs a concrete Gorenstein quotient,
and degreewise rank-nullity for `J ⊂ R` proves equation (8). Hence
`theorem1_of_resolution` no longer accepts the former hypotheses `hrev`,
`hres`, `hrε`, `h3`, `hε1`, `hr0`, `hr1`, or `hGor` separately.
The wrapper `theorem1_of_hasGradedResolutionPackage` collects the entire
non-Stanley input into one proposition. Thus the precise missing theorem is
`IsTypeTwoLevel I e → HasGradedResolutionPackage I e`.

**Numerical consistency witness (`consistency_witness`).**
Since the structural facts are hypotheses, one must rule out that they are
secretly contradictory (which would make the theorem vacuously true). For
the numerical data computed from the level algebra `A = R/Ann(X², Y²+XZ)` —
Hilbert function `(1,3,2)`, socle degree 2, type two, whose Hilbert
numerator `(1−t)³(1+3t+2t²) = 1 − 4t² + 2t³ + 3t⁴ − 2t⁵` yields the dual
resolution data `F₁ = R(−1)³ ⊕ R(−2)²` (p₁ = 3, p₂ = 2), `F₂ = R(−3)⁴`
(q₃ = 4), `s = 5`, rank data `r₂ = 2`, `ε₂ = 0` — Lean verifies **all
hypotheses of `theorem1_full`** concretely, and the theorem produces the
concrete inequality `h₀h₂ = 2 ≤ 9 = h₁²`. What is certified formally is
exactly that the hypothesis set is jointly satisfiable — the algebra
itself is not constructed in Lean, so the section is named for what it
proves: a *numerical consistency witness*.

## 3. What is machine-checked vs. assumed

**Kernel-checked (everything quantitative in the paper, pp. 2–4):** every
identity, inequality, sum manipulation, case split, and the logic that
strings them together — including all four margin computations and the
entire dispatch from inequality (3) plus rank additivity down to the
conclusion.

**Assumed, as named hypotheses of `theorem1_full`** (each annotated in the
Lean source with its origin in the paper):

| Hypothesis | Content | Paper source |
|---|---|---|
| `hrev` | `g_d = h_{e−d}` | graded Matlis duality, p. 1 |
| `hquot` | `h_t ≤ N_t` | `A` is a quotient of `R` |
| `hres` | rank additivity of complex (1) | exactness of the dual resolution |
| `hrε`, `h3` | `r_d ∈ {0,1,2}`, `ε_d ∈ {0,1}`, estimate (3) | linear algebra over `Frac(R)`, (2)–(3); abstract form machine-checked (`rank_estimate_graded`) |
| `hε1` | `ε_d = 1` ⇒ `h_t = N_t` below `s−d` | dual degree correspondence, p. 3 |
| `hr0` | `r_d = 0` ⇒ `P_{<d} = 0` | minimal relations are nonzero, p. 3 |
| `hr1` | equation (8) with `B = 0` or `Gor B (e−a)` | UFD/cyclic-submodule argument, (7)–(8), pp. 3–4; abstract forms machine-checked (`primitive_line_saturated`, `line_factorization`, `cyclic_submodule_simple_socle`) |
| `hGor` | Gorenstein Hilbert functions are supported on `[0,∞)` and bounded by `N` | `B` is a graded quotient of `R` — **now a theorem** (`GorensteinQuotientHF.bounds`) in `theorem1_of_level` |
| `hStanley` | Stanley monotonicity for `Gor` | **the sole major imported structural theorem** — Lemma 1 (Zanello's characteristic-free Stanley theorem) |

In the formal-algebra form `theorem1_of_level`, the rows `hquot` (with the
nonnegativity `hnn`) and `hGor` are discharged — derived from the formal
type-two level algebra — and `Gor` is instantiated at the concrete
`GorensteinQuotientHF`.  The trust base there is `hrev`, `hres`, `hrε`,
`h3`, `hε1`, `hr0`, `hr1` (stated about the concrete `hilb I`), plus
`hStanley`.

The stronger `theorem1_of_resolution` consolidates all of those structural
rows into one certified resolution/duality package. This is a substantially
narrower and more algebraic boundary, but its existence is not derived from
`IsTypeTwoLevel`: Mathlib has a generic functorial projective-resolution API,
but the package-existence bridge is still the missing construction: the
separate `GradedResolution.lean` module now formalizes finite shifted bases,
homogeneous minimality/Nakayama certificates, localized Euler bookkeeping,
and the graded Matlis component identities.  It does not yet construct
those certificate objects from `IsTypeTwoLevel`.

## 4. Honest verdict

**Is this a complete formalization modulo Stanley?** Not quite, but the gap
is now a single named hypothesis. The old list of unrelated numerical
hypotheses was eliminated in `theorem1_of_resolution`; the graded-resolution
certificates were then formalized in `GradedResolution.lean`; and
`ModuloStanley.lean` now constructs the graded minimal free complex, the
Matlis-annihilator Gorenstein property, and the full resolution/duality
package **from `IsTypeTwoLevel I e` alone** — except for one input. The
endpoint is

```lean
theorem1_modulo_Stanley_of_lastBetti
  (e I hA)
  (hBetti : Fintype.card (GradedMinimalFreeComplex.ofLevel hA).β₃ = 1)
  (hStanley : …)
```

The remaining input `hBetti` says that the third free module in the minimal
graded resolution of the Matlis dual has rank one, i.e. `Tor₃(M,k) ≅
Soc(M)(-3)`. The socle half is proved here (`matlisDualSocle_finrank = 1`);
the `Tor` half needs a Koszul complex on `(x₁,x₂,x₃)`, absent from Mathlib
4.31. Everything else — the shift `e+3`, full support of the last
differential, and the identification of `I` with the ideal generated by its
entries — is now derived, the last two by projective null-homotopies on the
complex and on its dual.
Stanley's theorem remains the other explicit hypothesis.

**Is it strong verification? Yes, and here is its precise value.** For a
paper like this, errors overwhelmingly live in the quantitative
bookkeeping: an off-by-one in a degree bound, a sign in a second
difference, a case silently dropped, a margin that isn't actually positive.
*Every one of those failure modes is now excluded by the Lean kernel.* The
structural layer further machine-checks the abstract linear algebra and
UFD/socle arguments behind (2), (3), (7) and the cyclic-submodule step.
The formal-algebra layer now anchors the statement at an actual formal
object — `A = R/I` for a homogeneous ideal of `k[x₁,x₂,x₃]` with the
type-two level conditions — derives `hnn`, `hquot`, `hGor` from it,
verifies the object's Hilbert-function profile `(1, 3, …, h_e = 2)` and
deduces `2 ≤ e`, and makes the Stanley hypothesis a faithful statement about actual Gorenstein
quotients of `R`.  What remains on trust in `theorem1_of_level` are the
graded/duality identifications connecting the abstract lemmas to the
specific module `M` (duality, exactness, minimality of the resolution —
`hrev`, `hres`, `hrε`, `h3`, `hε1`, `hr0`, `hr1`, each now a precisely
stated proposition about the concrete `hilb I`) plus one citation to
Zanello's published characteristic-free Stanley theorem — isolated as the
single named hypothesis `hStanley` — exactly the parts a referee verifies
by standard theory rather than computation. The numerical consistency
witness additionally proves the hypothesis interface is coherent and
realizable.

In the taxonomy of partial formalizations, this is a **complete,
non-vacuous, machine-checked verification of the paper's reduction and case
analysis** — the strongest form of verification achievable for this result
with today's libraries.

## 5. Key named results in `LogConcavity.lean`

| Lean name | Statement |
|---|---|
| `two_mul_N`, `N_succ`, `N_strictMono` | closed form, Pascal recursion, strict monotonicity of `N` |
| `Nz_diff`, `Nz_second_diff` | first/second differences of the zero-extended `N` |
| `binomial_window_log_concave`, `Nz_window` | log-concavity of descending windows of `N` |
| `amgm_log_concave` | `a + c ≤ 2b`, `a,c ≥ 0` ⇒ `ac ≤ b²` |
| `r_eq_zero_log_concave` | the r = 0 margin is positive |
| `r_eq_one_log_concave` | the r = 1 failure margin is positive |
| `GoodTriple.log_concave` | all four scenarios are log-concave |
| `shiftSum_second_diff` | the Hilbert-numerator telescoping identity |
| `proper_subfamily_linearIndependent` | paper (2): full-support kernel line ⇒ proper subfamilies independent |
| `rank_estimate`, `rank_estimate_graded` | paper (3): the rank inequality from the graded zero pattern |
| `primitive_line_saturated`(`_fraction`) | the UFD lemma `(Kv) ∩ R² = Rv` |
| `line_factorization` | the passage to `vJ` and the truncated-kernel identity (7) |
| `cyclic_submodule_simple_socle` | nonzero cyclic submodule of finite-length module with simple socle ⇒ Artinian quotient with simple socle |
| `deep_dispatch` | resolution numerics ⇒ every tested triple is a `GoodTriple` |
| `theorem1`, `theorem1_full` | the main theorem (scenario form / full form), with `hStanley` as the sole imported structural theorem |
| `finrank_homogeneousSubmodule` | `dim_k Rₙ = binom(n+2,2)` (stars and bars) |
| `quotPiece`, `hilb`, `socle`, `IsTypeTwoLevel` | the formal algebraic input: graded pieces, Hilbert function, socle of `A = R/I`; the type-two level predicate |
| `hilb_nonneg`, `hilb_le_Nz` | hypotheses `hnn`, `hquot` as theorems |
| `hilb_zero`, `IsTypeTwoLevel.hilb_one`, `IsTypeTwoLevel.hilb_top`, `IsTypeTwoLevel.hilb_vanish`, `IsTypeTwoLevel.two_le_socleDegree` | the profile `h = (1, 3, …, h_e = 2)`, vanishing above `e`, and `2 ≤ e` |
| `GorensteinQuotientHF`, `GorensteinQuotientHF.bounds` | the concrete Gorenstein predicate; hypothesis `hGor` as a theorem |
| `ExactPresentation.finrank_add`, `GradedResolutionDuality.hilbert_series` | Hilbert-series coefficients from actual degreewise exact maps |
| `qShift_le_of_proper`, `ideal_no_low_degree` | shift upper bound and low-degree vanishing derived from the homogeneous generators |
| `SurjectivePresentation.finrank_add`, `CriticalBranchCertificate.presentation_dimension` | critical presentation dimension from an actual surjection and kernel |
| `HasGradedResolutionPackage`, `theorem1_of_hasGradedResolutionPackage` | the exact single non-Stanley existence boundary and its end-to-end wrapper |
| `theorem1_of_level` | Theorem 1 from the formal algebra, with `hnn`/`hquot`/`hGor` derived |
| `consistency_witness` | all hypotheses verified numerically for the data of `A = R/Ann(X², Y²+XZ)` |

Axiom audit (from `lake build`, also enforced by CI): every audited
theorem, including all structural-layer lemmas, reports

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Continuous integration

`.github/workflows/ci.yml` re-verifies everything from a clean checkout on
every push: it installs elan, fetches the Mathlib binary cache, runs
`lake build`, publishes the `#print axioms` audit in the job summary and
as an artifact, and fails if any audited theorem depends on anything
beyond `propext`, `Classical.choice`, `Quot.sound`.
