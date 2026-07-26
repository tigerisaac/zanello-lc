# Verification report

Companion to [`README.md`](README.md). This document records what the Lean
development proves, how it is organized, where the trust boundary sits, and
what was checked independently of the build.

The object of verification is
[`paper/type2-log-concavity.pdf`](paper/type2-log-concavity.pdf), *Log-concavity
of codimension-three level Hilbert functions of type two*, whose Theorem 1 is
the case `(r, t) = (3, 2)` recorded as open in
[arXiv:2210.09447](https://arxiv.org/abs/2210.09447).

## 1. Environment

- Lean 4.31.0 (pinned in `lean-toolchain`), Mathlib v4.31.0 (pinned in
  `lake-manifest.json`), nothing installed outside the repository.
- `lake exe cache get && lake build` reproduces the whole verification.
- ~16 000 lines of project Lean plus ~7 700 lines of ported homological
  prerequisites under `FormalDeps/`.

## 2. The endpoint

```lean
theorem theorem1_log_concave
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (hStanley : StanleyLemma1 k) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2
```

in [`Statement.lean`](Statement.lean), which also reproduces every definition
it depends on. `StanleyLemma1` is the paper's Lemma 1 and the only
mathematical input not proved here; `README.md` gives the citations and the
two remarks on the exact form assumed (monotonicity only; all fields,
including finite ones, via base change).

Nothing else is assumed. In particular the theorem takes no hypothesis on
the characteristic or cardinality of `k`, and no numerical data about any
resolution.

## 3. Architecture

**Layer 0 — the Hilbert function of `R`.** `N j = binom(j+2,2)` and its
zero-extension `Nz`, with the division-free closed form `2N_j = (j+1)(j+2)`,
Pascal recursion, strict monotonicity, the first difference
`Nz t − Nz(t−1) = t+1`, and `Δ²Nz = 1` on nonnegative degrees.

**Layer 1 — the four scenarios.** The paper's case analysis distils each
tested triple `(g_{d−2}, g_{d−1}, g_d)` into one of four shapes
(`GoodTriple`), each proved log-concave: binomial windows (the `ε_d = 1`
case), the AM–GM step, the `r_d = 0` margin `d(2(d+1)+(d−1)p_d) > 0`, and the
`r_d = 1` failure margin `x² − y ≥ d² − d(d−1) = d > 0`.

**Layer 2 — `deep_dispatch`.** From the resolution numerics to the scenarios:
the telescoping identity turning rank additivity of the paper's display (1)
into `Δ²g_d = 2 + Q_d − P_{<d} − p_d`, the central estimate (4) from (3), the
proof that a putative failure under `r_d = 1` forces (6), inequality (9)
`2d ≤ e+2`, the computation `x = d + a + D ≥ d` using (8) and Lemma 1
(including the boundary case `n − 2 < 0` and the paper's `H = 0` case), and
the bound `g_{d−2} ≤ 2N_{d−2} = d(d−1)`.

**The formal algebra.** `R = k[x₁,x₂,x₃]` with its monomial grading, a
homogeneous ideal `I`, graded pieces `quotPiece I n`, Hilbert function
`hilb I`, socle, and the predicate `IsTypeTwoLevel I e`. Machine-checked
from that object: `dim_k Rₙ = binom(n+2,2)` via stars and bars; `h_t ≥ 0` and
`h_t ≤ N_t`; and the paper's profile `h₀ = 1`, `h₁ = 3`, `h_e = 2`, `h_t = 0`
for `t > e`, hence `2 ≤ e`. The socle is proved *equal* to the top graded
piece, so "socle degree `e`" is genuinely what the structure encodes.

**The resolution.** `ModuloStanley.lean` constructs the paper's display (1)
from `IsTypeTwoLevel I e`: finite homogeneous bases with genuine shift
multisets, minimality of every differential, degreewise exact presentations,
and localized rank data. `ε_d` and `r_d` are an actual nullity and rank;
`p` and `q` are cardinalities of shift fibres; the Hilbert-series identity is
derived from the presentations by rank–nullity, not stored as a field. The
critical branch carries the actual primitive homogeneous vector and the
coefficient and annihilator ideals, and equation (8) is derived by degreewise
rank–nullity for `J ⊂ R`.

**The last Betti number.** The one homological fact needing machinery Mathlib
lacks is that the third free module has rank one. `Koszul.lean` builds the
Koszul complex on `(x₁,x₂,x₃)` and proves it exact over `R` and over finite
free modules; `KoszulHomology.lean` proves three explicit connecting
isomorphisms carrying `Soc M` up the syzygies to `F₃ ⧸ m F₃`;
`BettiThree.lean` instantiates the chain at the minimal graded free complex
of the Matlis dual and compares dimensions, giving `card_beta₃_eq_one`.

## 4. What is machine-checked vs. assumed

Machine-checked: everything quantitative in the paper — every identity,
inequality, sum manipulation, case split, and the logic connecting them,
including all four margin computations; the abstract linear algebra and
UFD/socle arguments behind (2), (3), (7) and the cyclic-submodule step; and
the construction of the resolution data itself from `IsTypeTwoLevel I e`.

Assumed: `StanleyLemma1` alone.

Earlier drafts of this development carried a list of separately named
numerical hypotheses (`hrev`, `hres`, `hrε`, `h3`, `hε1`, `hr0`, `hr1`,
`hGor`, `hBetti`). All have since been discharged. The legacy entry points
`theorem1_full`, `theorem1_of_level` and `theorem1_of_resolution` are
retained for compatibility and for the numerical consistency witness; they
are not on the path from `IsTypeTwoLevel` to the endpoint.

## 5. Non-vacuity

Two independent checks that the hypotheses are satisfiable and the
conclusion has content.

`Witness.lean` constructs the actual algebra `J = (xy, xz, y², z², x³)`, the
inverse system `⟨X², YZ⟩`, and verifies every field of `IsTypeTwoLevel` from
the monomial generators, including `finrank (socle J) = 2` from the explicit
basis `{x², yz}`. Its Hilbert function is pinned to `(1, 3, 2)` by the same
lemmas the main theorem uses, so this doubles as an end-to-end check of the
`hilb`/`socle`/`quotPiece` definitions against a hand-computable case.
`Statement.theorem1_witness` runs the endpoint itself on that algebra.

`KoszulHomology.koszulResolutionWitness` instantiates the socle/last-Betti
chain at the Koszul complex, which is a minimal free resolution of
`k = R ⧸ m`, so the hypotheses of that theorem are simultaneously
satisfiable; `nontrivial_H₀_self` shows the conclusion is about nonzero
modules.

The legacy `NumericalConsistencyWitness` section certifies, for the numerical
data `F₁ = R(−1)³⊕R(−2)²`, `F₂ = R(−3)⁴`, `s = 5`, `r₂ = 2`, `ε₂ = 0`, that
every hypothesis of the older `theorem1_full` is jointly satisfiable.

## 6. Independent checks

These were performed against the built library, separately from the build
itself, and are reproducible.

**Build from a clean toolchain.** elan → Lean/Mathlib v4.31.0 →
`lake exe cache get` → `lake build`: completes successfully, no errors, no
`declaration uses 'sorry'` warnings, and every `#print axioms` line reports
`[propext, Classical.choice, Quot.sound]`.

**Generality is real, not an artifact of universe defaults.** The endpoint
type-checks when instantiated at `k : Type 5` and at `ZMod 2`, confirming
that it is universe-polymorphic and characteristic-free as stated.

**Correspondence with the paper.** Each step of the proof on pp. 1–4 was
matched against a named Lean result; the table is in `README.md`. The
correspondence includes the side conditions, e.g. the `2(n−1) ≤ E` needed to
apply Lemma 1 at `D = B_{n−1} − B_{n−2}`.

**Type two is load-bearing.** Log-concavity is *false* for codimension-three
level algebras of type ≥ 3, so a proof that did not use type two would be
suspect. It enters where the paper says it does: the Matlis dual is presented
from `Fin 2 → R3 k` (via `finrank_reversedMatlisPiece_zero = 2`, which
consumes the `type_two` field), and the critical branch runs on a
two-component primitive vector with `IsRelPrime (v 0) (v 1)`.

**Provenance of `FormalDeps/`.** All 14 ported files were diffed against the
upstream fork commit they claim to come from. Of 131 theorem/lemma statements
present in both, exactly one differs, by a namespace disambiguation
(`comap` → `_root_.Submodule.comap`); no statement is weakened and no
hypothesis added. `Hilberts_Syzygy` and `AuslanderBuchsbaum` match verbatim.
The single `sorry` in the tree is inside a block comment and is present in
the upstream original. See `FormalDeps/README.md` for the diff recipe.

## 7. Assessment

For a result of this kind, errors overwhelmingly live in quantitative
bookkeeping: an off-by-one in a degree bound, a sign in a second difference, a
silently dropped case, a margin that is not actually positive. Every one of
those failure modes is excluded by the Lean kernel here. Beyond that, the
structural layer machine-checks the linear algebra and UFD/socle arguments,
and the resolution layer constructs the paper's display (1) rather than
assuming its numerical shadow.

What remains on trust is one published theorem, cited and isolated as a
single named hypothesis, of the kind a referee verifies from the literature
rather than by computation.
