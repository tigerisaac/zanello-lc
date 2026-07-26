# Lean verification: Log-concavity of codimension-three level Hilbert functions of type two

A Lean 4 + Mathlib formalization of the paper
[`paper/type2-log-concavity.pdf`](paper/type2-log-concavity.pdf):

> **Theorem 1.** Let `A = R/I` (`R = k[x₁,x₂,x₃]`, `k` any field) be a standard
> graded Artinian level algebra of embedding dimension three, socle degree `e`,
> and type two. Then its Hilbert function is log-concave:
> `hᵢ² ≥ h_{i-1} h_{i+1}` for `1 ≤ i ≤ e−1`.

This is the case `(r, t) = (3, 2)` of the log-concavity question for level
Hilbert functions. Iarrobino settled `r = 2` (any `t`) and `(3,1)`
positively and `(4,1)` negatively; Zanello settled all remaining pairs
negatively **except** `(3,2)`, which
[arXiv:2210.09447](https://arxiv.org/abs/2210.09447) records as open in every
characteristic. The paper formalized here proves that case, assuming only
Stanley's theorem on codimension-three Gorenstein Hilbert functions.

### Relation to concurrent work on pure O-sequences

Zanello's note asks two questions. Question 1 is about **level Hilbert
functions** — the Hilbert functions of *all* standard graded Artinian level
algebras of codimension `r` and type `t`. Question 2 is about **pure
O-sequences** — equivalently, the Hilbert functions of *monomial* Artinian
level algebras. `(3,2)` was the principal open case of both.

Question 2 for `(3,2)` was settled in May 2026 by Google DeepMind's
AlphaProof/Nexus agent, reported as "Every pure `O`-sequence of codimension 3
and type 2 is log-concave" in
[arXiv:2605.22763](https://arxiv.org/abs/2605.22763); the proof there is
combinatorial, counting monomials below the two maximal monomials of a pure
order ideal in `ℕ³`.

The theorem formalized here is **question 1**: every codimension-three
type-two level algebra over any field, monomial or not. It is strictly more
general, and it implies the pure O-sequence statement whenever the order
ideal genuinely uses all three variables — the degenerate cases fall under
Iarrobino's settled `r ≤ 2`. The proof is correspondingly different: minimal
free resolutions, graded Matlis duality and Stanley's theorem rather than
monomial counting.

**Start here:** [`Statement.lean`](Statement.lean) restates every definition
the theorem depends on, names the assumption, gives the endpoint, runs it on
an explicit algebra, and prints the axiom audit — in about 200 lines, with no
proofs to read. Everything else in the repository exists to prove that one
statement.

## What is proved, and what is assumed

```lean
theorem theorem1_log_concave
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (hStanley : StanleyLemma1 k) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2
```

`hA` is the algebra of the theorem and `hilb I` is its honest Hilbert
function (`dim_k` of the image of `Rₜ` in `A`). There is no hypothesis on the
characteristic or the cardinality of `k`, and no numerical data about a
resolution is assumed.

`StanleyLemma1 k` is the paper's Lemma 1 and the **only** input the
development does not prove:

```lean
def StanleyLemma1 (k : Type u) [Field k] : Prop :=
  ∀ B E, GorensteinQuotientHF k B E →
    ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i
```

— the Hilbert function of a standard graded Artinian Gorenstein algebra of
embedding dimension at most three and socle degree `E` is nondecreasing
through degree `⌊E/2⌋` (for integers, `i ≤ ⌊E/2⌋` is `2*i ≤ E`). Sources:

* R. P. Stanley, *Hilbert functions of graded algebras*, Adv. Math. 28 (1978),
  57–83 — the codimension-three Gorenstein case, via the Buchsbaum–Eisenbud
  structure theorem;
* F. Zanello, *Stanley's theorem on codimension 3 Gorenstein h-vectors*,
  Proc. Amer. Math. Soc. 134 (2006), 5–8,
  [arXiv:math/0411231](https://arxiv.org/abs/math/0411231) — the
  characteristic-free proof cited by the paper.

Two points about the exact form assumed. First, only *monotonicity* is
assumed, not the full SI-sequence conclusion — the weakest form the proof
uses. Second, it is assumed over the given field with no infiniteness
hypothesis, matching the paper's "the result holds over an arbitrary field";
arguments through a general linear form are normally written over an infinite
field, and the reduction is standard and lossless, since for `k ⊆ k'` the
algebra `A ⊗_k k'` has the same Hilbert function and the same socle
dimension, so Gorenstein-ness, socle degree and Hilbert function all survive
base change to an infinite extension. `Statement.lean` records both remarks
next to the definition.

`GorensteinQuotientHF` is a concrete predicate — an actual homogeneous ideal
`J ⊆ k[x₁,x₂,x₃]` with `B t = hilb J t` at every degree — not an
uninterpreted predicate variable, so `StanleyLemma1` cannot be satisfied
vacuously or by an unrelated function.

## Verification status

`lake build` succeeds with **zero `sorry`**, and `#print axioms` reports only
Lean's standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`) for every audited theorem — no hidden axioms. CI rebuilds from
a clean checkout and **fails** if the endpoint's audit line is missing or
mentions anything else.

`IsTypeTwoLevel` is not vacuous: [`Witness.lean`](Witness.lean) constructs
`J = (xy, xz, y², z², x³)` (the inverse system `⟨X², YZ⟩`) and verifies every
field of the structure from the monomial generators, including
`finrank (socle J) = 2` via the explicit basis `{x², yz}`. Running the
development's own derivations on it pins the Hilbert function to `(1, 3, 2)`
and yields `h₀·h₂ = 2 ≤ 9 = h₁²` (`theorem1_witness`, `witness_log_concave`).
Because the lemmas that compute `hilb J 1 = 3` and `hilb J 2 = 2` are the
ones the main theorem uses, this doubles as an end-to-end check of the
`hilb`/`socle`/`quotPiece` definitions against a case computable by hand.

## Correspondence with the paper

Every step of the proof on pp. 1–4 is machine-checked. The paper's own
numbering is used throughout.

| Paper | Lean |
|---|---|
| `N_j = binom(j+2,2)`, `N_j − N_{j−1} = j+1`, ratios `N_j/N_{j−1}` nonincreasing | `N`, `two_mul_N`, `Nz_diff`, `Nz_second_diff`, `binomial_window_log_concave` |
| `s = e+3`; last free module of the resolution of `A` is `R(−s)²` | `lastShift_eq_of_unique`, `card_beta₃_eq_one` (**proved**, not assumed) |
| Display (1): `0 → R(−s) → F₂ → F₁ → R² → M → 0`, `M` two-generated in degree 0, socle one-dimensional in degree `e` | `GradedMinimalFreeComplex`, `inverseSystemMap_surjective`, `matlisDualSocle_finrank` |
| `M_d = Hom_k(A_{e−d}, k)`, `g_d = h_{e−d}` | `gradedDualPiece`, `reversedHilb`, `finrank_gradedDualPiece` |
| (2): kernel of `δ₂` one-dimensional, spanning vector of full support ⇒ every proper subset of columns `K`-independent | `proper_subfamily_linearIndependent`, `lastDifferentialVector_full`, `proper_subfamily_delta₂` |
| `Q_d`, `P_{<d}`, `r_d`, `ε_d` | `qMultiplicity`, `pMultiplicity`, `resolutionRank`, `resolutionEpsilon` |
| (3): `Q_d − ε_d ≤ P_{<d} − r_d` | `rank_estimate_graded`, `rank_inequality` |
| Hilbert numerator ⇒ `Δ²g_d = 2 + Q_d − P_{<d} − p_d` | `shiftSum_second_diff`, `GradedResolutionDuality.hilbert_series` |
| (4) central estimate; AM–GM ⇒ (5) `Δ²g_d ≥ 1` at a putative failure | `amgm_log_concave`, inside `deep_dispatch` |
| `ε_d = 1`: `I` has no element below degree `s−d`; triple is `(N_m, N_{m−1}, N_{m−2})`, `m = e−d+2` | `ideal_no_low_degree`, `all_qShift_le_of_epsilon_one`, `epsilon_one_full_hilbert`, `Nz_window` |
| `r_d = 2` ⇒ `Δ²g_d ≤ 0`, contradiction | inside `deep_dispatch` |
| `r_d = 0` ⇒ `Q_d = 0`, explicit values, margin `d(2(d+1)+(d−1)p_d) > 0` | `rank_zero_no_low_shifts`, `r_eq_zero_log_concave` |
| `r_d = 1` ⇒ (6) `p_d = 0`, `Δ²g_d = 1` | inside `deep_dispatch` |
| Primitive `v = (v₁,v₂)` of degree `a < d` spanning the line; low-shift columns generate `vJ` (Euclid's lemma, `R` a UFD) | `primitive_line_saturated`, `primitive_line_saturated_fraction`, `line_factorization`, `r3_primitive_pair_factorization` |
| (7): `ker(R² → M)_t = (vJ)_t` for `t ≤ d` | `rank_one_critical_equation7`, `CriticalBranchCertificate.equation7` |
| `H = 0` ⇒ `J = R`, `B ≡ 0`; `H ≠ 0` ⇒ `B = R/Ann(H)` Gorenstein of socle degree `E = e−a`, agreeing with `J` through degree `n = d−a` | `CriticalBranchCertificate.annihilator_case`, `cyclic_submodule_simple_socle`, `GorensteinAnnihilatorData.toGorensteinQuotientHF`, `low_piece_eq` |
| (8): `g_t = 2N_t − N_{t−a} + B_{t−a}` for `t = d−2, d−1, d` | `CriticalBranchCertificate.equation8` |
| (9): `2d ≤ e+2` from `N_{d−1} ≤ g_{d−1} ≤ N_{e−d+1}` | inside `deep_dispatch` |
| `2(n−1) ≤ E`, Lemma 1 ⇒ `D = B_{n−1} − B_{n−2} ≥ 0` | inside `deep_dispatch` (the sole use of `hStanley`) |
| `x = g_{d−1} − g_{d−2} = d + a + D ≥ d`, `g_{d−2} ≤ d(d−1)`, margin `x² − y ≥ d > 0` | `r_eq_one_log_concave` |
| Full case analysis; reversal `g ↦ h` | `GoodTriple.log_concave`, `deep_dispatch`, `theorem1` |

Type two is load-bearing exactly where the paper uses it: `M` is presented
from `Fin 2 → R3 k` (`finrank_reversedMatlisPiece_zero = 2`, which consumes
`type_two`), and the critical branch runs on a two-component primitive vector
`IsRelPrime (v 0) (v 1)`. The machinery does not carry over to type three,
where log-concavity is false.

## Structure of the development

| File | Contents |
|---|---|
| [`Statement.lean`](Statement.lean) | definitions, the assumption, the endpoint, the witness instance, the axiom audit — the reader's entry point |
| [`LogConcavity.lean`](LogConcavity.lean) | the numerical layer (`N`, `Nz`, `GoodTriple`, `deep_dispatch`, `theorem1_full`), the formal algebra (`hilb`, `socle`, `IsTypeTwoLevel`, `GorensteinQuotientHF`), and the resolution-to-numerics bridge |
| [`InverseSystem.lean`](InverseSystem.lean) | low-level homogeneous-component and inverse-system constructions, graded Matlis dual |
| [`GradedResolution.lean`](GradedResolution.lean) | finite-basis/shifted complexes, graded Nakayama, localized Euler characteristic, graded Matlis interfaces |
| [`ModuloStanley.lean`](ModuloStanley.lean) | builds the minimal graded free complex, the Matlis-annihilator Gorenstein property and the whole resolution/duality package from `IsTypeTwoLevel` alone |
| [`Koszul.lean`](Koszul.lean), [`KoszulHomology.lean`](KoszulHomology.lean) | the Koszul complex on `(x₁,x₂,x₃)` and its connecting isomorphisms |
| [`BettiThree.lean`](BettiThree.lean) | the last Betti number is one; `theorem1_modulo_Stanley` |
| [`Witness.lean`](Witness.lean) | the concrete instance `(xy, xz, y², z², x³)` |
| [`FormalDeps/`](FormalDeps/) | ported homological prerequisites (see below) |

### How the resolution data is obtained

The paper's display (1) is not assumed. `ModuloStanley.lean` constructs it
from `IsTypeTwoLevel I e`: finite homogeneous bases with genuine shift
multisets, minimality of every differential (entries in the irrelevant
ideal), degreewise exact presentations, and the localized rank data. `ε_d`
and `r_d` are an actual nullity and rank, not numerical parameters; `p` and
`q` are cardinalities of shift fibres. The Hilbert-series identity is derived
from the presentations by rank–nullity.

The one homological fact that needed machinery Mathlib lacks is that the
third free module has rank one — the `R(−s)` at the left of (1). Its socle
side is `matlisDualSocle_finrank = 1`; the `Tor` side needs a Koszul complex
on `(x₁,x₂,x₃)`, which `Koszul.lean` builds by hand and `KoszulHomology.lean`
walks up the syzygies via three explicit connecting isomorphisms, giving
`Soc M ≅ F₃ ⧸ m F₃`. Comparing dimensions in `BettiThree.lean` gives
`card_beta₃_eq_one`. The hypotheses of that chain are not vacuous:
`koszulResolutionWitness` instantiates it at the Koszul complex itself.

Consequences that earlier drafts assumed alongside it are also derived:
`rShift a₀ = e+3` (`lastShift_eq_of_unique`), every coordinate of `d₃`
nonzero (`lastDifferential_coordinate_ne_zero`), `I = span (entries of d₃)`
(`originalIdeal_le_coordinateIdeal`, `coordinateIdeal_le_originalIdeal`), and
`β₂` nonempty (`beta₂_nonempty_of_beta₃`).

### FormalDeps

Mathlib 4.31 has a generic functorial projective-resolution API but no
minimal **graded** free resolutions, no Koszul complex and no graded Matlis
duality. [`FormalDeps/`](FormalDeps/) supplies the homological prerequisites
— Ischebeck's depth bound, Auslander–Buchsbaum, Cohen–Macaulay freeness and
**Hilbert's Syzygy Theorem**
(`globalDimension (MvPolynomial (Fin n) k) = n`) — ported to this toolchain
from the public Mathlib fork
[`Thmoas-Guan/mathlib4_fork`](https://github.com/Thmoas-Guan/mathlib4_fork)
@ `0ff6e01f56` (the Auslander–Buchsbaum–Serre criterion project by Nailin
Guan et al., Apache-2.0). Those files keep their upstream names, headers and
authorship; see [`FormalDeps/README.md`](FormalDeps/README.md) for provenance
and how to diff them against the source commit.

## Reproducing

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get   # fetch the prebuilt Mathlib binary cache
lake build           # expect: Build completed successfully + axiom audit lines
```

Lean `v4.31.0`, Mathlib `v4.31.0`, pinned in `lean-toolchain` and
`lake-manifest.json`.

[`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs exactly this from
a clean checkout on every push and pull request, records the full
`#print axioms` audit in the job summary and as an artifact, and fails the
build if any audited theorem depends on anything beyond Lean's three standard
foundational axioms, or if any of the required endpoint declarations is
missing from the audit.

## Licence

This repository is MIT-licensed (see [`LICENSE`](LICENSE)), **except** for
the vendored files under [`FormalDeps/`](FormalDeps/), which are derived from
Mathlib and its fork and remain under the Apache-2.0 licence, retaining their
original copyright headers and author attributions.
