/-
# Log-concavity of codimension-three level Hilbert functions of type two

Formalization of:

  **Theorem 1.** Let `A = R/I` (`R = k[x₁,x₂,x₃]`, `k` any field) be a standard
  graded Artinian level algebra of embedding dimension three, socle degree `e`,
  and type two.  Then its Hilbert function `h = (1, 3, h₂, …, h_e = 2)` is
  log-concave: `hᵢ² ≥ h_{i-1} h_{i+1}` for `1 ≤ i ≤ e - 1`.

## Architecture

The development has three machine-checked layers plus a clearly delimited
set of structural hypotheses.

* **Layer 0** — the Hilbert function `N j = binom(j+2,2)` of `R` and its
  arithmetic (closed form, Pascal recursion, strict monotonicity, first and
  second differences, log-concavity of descending windows).

* **Layer 1** — `GoodTriple → log-concave`: the four arithmetic scenarios of
  the paper's case analysis each force the log-concavity inequality
  (`GoodTriple.log_concave`).

* **Structural layer** — machine-checked abstract forms of the local
  algebra behind the imported hypotheses: paper (2)
  (`proper_subfamily_linearIndependent`), the rank estimate (3)
  (`rank_estimate`, `rank_estimate_graded`), the UFD lemma
  `(Kv) ∩ R² = Rv` (`primitive_line_saturated`), the passage to `vJ` with
  the truncated-kernel identity (7) (`line_factorization`), and the
  cyclic-submodule/simple-socle lemma (`cyclic_submodule_simple_socle`).

* **Layer 2** — `deep_dispatch`: starting from the *primitive numerical
  shadows* of the commutative algebra — rank additivity of the minimal
  resolution (paper (1)), the rank estimate (3), and equation (8) with
  Stanley's monotonicity — this layer machine-checks the whole reduction of
  pp. 2–4: the Hilbert-numerator computation `Δ²g_d = 2 + Q_d − P_{<d} − p_d`,
  the central estimate (4), the failure criterion (5) forcing (6)
  (`p_d = 0`, `Δ²g_d = 1`), inequality (9) `2d ≤ e + 2`, the computation
  `x = g_{d-1} − g_{d-2} = d + a + D ≥ d`, and the bound
  `g_{d-2} ≤ 2N_{d-2} = d(d-1)`.

* **`theorem1_full`** chains Layer 2 into Layer 1 and transfers back from the
  reindexed dual `g` to `h` by reversal.

* **Formal-algebra layer** — the actual starting object of the paper
  (roadmap item 1): `R = k[x₁,x₂,x₃]` with its monomial grading, a
  homogeneous ideal `I`, the graded quotient `A = R/I` with graded pieces
  `quotPiece` and Hilbert function `hilb`, its socle, and the predicate
  `IsTypeTwoLevel` (Artinian, embedding dimension three, socle concentrated
  in degree `e`, type two).  Machine-checked: the dimension count
  `dim_k R_n = N n` (stars and bars, `finrank_homogeneousSubmodule`), the
  profile `h₀ = 1`, `h₁ = 3`, `h_e = 2`, `h_t = 0` for `t > e`
  (`hilb_zero`, `IsTypeTwoLevel.hilb_one`, `IsTypeTwoLevel.hilb_top`,
  `IsTypeTwoLevel.hilb_vanish`), the necessary bound `2 ≤ e`, and the
  discharge of the hypotheses `hnn`,
  `hquot` (`hilb_nonneg`, `hilb_le_Nz`) and `hGor`
  (`GorensteinQuotientHF.bounds`, over the *concrete* Gorenstein predicate
  `GorensteinQuotientHF`).  `theorem1_of_level` restates the main theorem
  from this formal object with those hypotheses derived rather than assumed.

* **Resolution bridge (roadmap items 2--10)** — `gradedDualPiece` constructs
  `Hom_k(A_{e-d},k)` and proves dimension reversal; `GradedResolutionDuality`
  records the finite bases, shifts, localized matrices, last-differential
  generator coordinates, and degreewise exact presentations unavailable in
  Mathlib.  Rank–nullity derives the Hilbert-series identity and the critical
  presentation dimension rather than accepting either numerical equality as
  a field.  The generator data also prove the upper shift bound and the
  absence of lower-degree ideal elements.  Lean then defines the Betti
  multiplicities and ranks/nullities, proves (3), the `ε=1` and `r=0`
  consequences, and constructs the primitive-line critical branch.
  Degreewise rank-nullity for the coefficient and annihilator ideals proves
  equation (8).  `theorem1_of_resolution`
  consumes this proof-carrying package and Stanley's theorem, with none of
  the old numerical hypotheses in its signature.

## What remains assumed (and exactly why)

The legacy numerical theorem `theorem1_full` retains the following named
hypotheses, each annotated with its source in the paper:

* `hrev`  — `g_d = h_{e-d}` (graded Matlis duality, p. 1);
* `hquot` — `h_t ≤ N_t` (`A` is a quotient of `R`);
* `hres`  — rank additivity of the exact complex (1):
  `g_t = 2N_t − Σ_b p_b N_{t-b} + Σ_b q_b N_{t-b} − N_{t-s}`;
* `hrε`, `h3` — the rank data `r_d ∈ {0,1,2}`, `ε_d ∈ {0,1}` and the linear
  algebra estimate (3) `Q_d − ε_d ≤ P_{<d} − r_d` (from (2), p. 2);
* `hε1`  — if `ε_d = 1` then `h_t = N_t` for `t < s − d` (degree
  correspondence in the dual resolution, p. 3, first case);
* `hr0`  — if `r_d = 0` then `P_{<d} = 0` (minimal relations are nonzero,
  p. 3, third case);
* `hr1`  — in the putative-failure case `r_d = 1, p_d = 0, Δ²g_d = 1`, the
  existence of `a < d` and of `B` — either zero (the paper's `H = 0` case)
  or a Gorenstein Hilbert function `Gor B (e−a)` — with equation (8): the
  UFD/cyclic-Gorenstein-submodule argument, (7)–(8), pp. 3–4 (its abstract
  algebraic content is machine-checked in the structural layer below);
* `hGor` — a Gorenstein Hilbert function vanishes in negative degrees, is
  nonnegative, and is bounded by the Hilbert function of `R`;
* `hStanley` — **Stanley's theorem (Lemma 1)**, the sole major imported
  structural theorem: a codimension-≤3 Gorenstein Hilbert function of
  socle degree `E` is nondecreasing through degree `⌊E/2⌋`.

In the formal-algebra form `theorem1_of_level`, the hypotheses `hnn`,
`hquot`, and `hGor` are *derived* from a formally defined type-two level
algebra and the abstract predicate `Gor` is instantiated at the concrete
`GorensteinQuotientHF`; what remains assumed there is `hrev`, `hres`,
`hrε`, `h3`, `hε1`, `hr0`, `hr1` — now stated about the concrete Hilbert
function `hilb I` of the formal algebra, i.e. precisely specified open
lemmas (roadmap items 2–10) — plus `hStanley` (item 12).

The stronger `theorem1_of_resolution` replaces that entire list by a
`GradedResolutionDuality`/`ResolutionPackage` pair.  Mathlib today has no
minimal graded free resolutions or graded Matlis-duality construction, so
the existence of that proof-carrying pair is not yet derived from
`IsTypeTwoLevel`; Stanley is the other explicit input.  Thus this theorem
is conditional on the missing resolution/duality existence theorem and
Stanley, rather than on unrelated numerical functions.

Everything else — every inequality, identity, sum manipulation and case
split in the paper — is proved below with **no `sorry` and no extra axioms**
(see the `#print axioms` audit at the bottom).
-/
import Mathlib

namespace LogConcavity

/-! ## Layer 0a: the Hilbert function of `R` on natural indices -/

/-- `N j = binom (j+2) 2`, the dimension of the degree-`j` part of a
polynomial ring in three variables, as an integer. -/
def N (j : ℕ) : ℤ := ((j + 2).choose 2 : ℤ)

/-- Pascal recursion for `N`. -/
lemma N_succ (j : ℕ) : N (j + 1) = N j + (j + 2) := by
  have h : (j + 3).choose 2 = (j + 2).choose 1 + (j + 2).choose 2 :=
    Nat.choose_succ_succ (j + 2) 1
  simp only [N, show j + 1 + 2 = j + 3 from rfl, h, Nat.choose_one_right]
  push_cast
  ring

/-- The closed form, multiplied by `2` to stay division-free:
`2 N j = (j+1)(j+2)`. -/
lemma two_mul_N (j : ℕ) : 2 * N j = ((j : ℤ) + 1) * ((j : ℤ) + 2) := by
  induction j with
  | zero => norm_num [N]
  | succ k ih =>
    rw [N_succ]
    push_cast
    linear_combination ih

lemma N_nonneg (j : ℕ) : 0 ≤ N j := by unfold N; exact Int.natCast_nonneg _

/-- `N` is strictly increasing (used for the paper's inequality (9)). -/
lemma N_strictMono {i j : ℕ} (h : i < j) : N i < N j := by
  have h2i := two_mul_N i
  have h2j := two_mul_N j
  have hij : (i : ℤ) < (j : ℤ) := by exact_mod_cast h
  have hi : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  nlinarith

lemma N_mono {i j : ℕ} (h : i ≤ j) : N i ≤ N j := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact le_of_lt (N_strictMono h')
  · rw [h']

/-- **Windows of `N` are log-concave**: the ratios `N_j / N_{j-1}` are
nonincreasing, division-free form.  This is the ε_d = 1 case of the paper. -/
lemma binomial_window_log_concave (k : ℕ) : N (k + 2) * N k ≤ N (k + 1) ^ 2 := by
  have h0 := two_mul_N k
  have h1 := two_mul_N (k + 1)
  have h2 := two_mul_N (k + 2)
  push_cast at h1 h2
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  nlinarith [h0, h1, h2, sq_nonneg ((k : ℤ) + 2), sq_nonneg ((k : ℤ) + 3)]

/-! ## Layer 0b: the Hilbert function of `R` on integer indices

`Nz t = N t` for `t ≥ 0` and `0` for `t < 0` — the natural indexing for
graded dimension counts, where negative degrees vanish. -/

/-- `N` extended by zero to negative integers. -/
def Nz (t : ℤ) : ℤ := if 0 ≤ t then N t.toNat else 0

lemma Nz_neg (t : ℤ) (h : t < 0) : Nz t = 0 := by
  rw [Nz, if_neg (by omega)]

lemma Nz_natCast (n : ℕ) : Nz (n : ℤ) = N n := by
  rw [Nz, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]

lemma Nz_nonneg (t : ℤ) : 0 ≤ Nz t := by
  rw [Nz]; split
  · exact N_nonneg _
  · exact le_refl 0

lemma Nz_zero : Nz 0 = 1 := by decide

/-- Division-free closed form on the nonnegative range. -/
lemma two_mul_Nz (t : ℤ) (ht : 0 ≤ t) : 2 * Nz t = (t + 1) * (t + 2) := by
  rw [Nz, if_pos ht]
  have h := two_mul_N t.toNat
  rwa [Int.toNat_of_nonneg ht] at h

/-- First difference: `Nz t − Nz (t−1) = t + 1` for `t ≥ 0`
(the paper's `N_j − N_{j-1} = j + 1`, p. 4). -/
lemma Nz_diff (t : ℤ) (ht : 0 ≤ t) : Nz t - Nz (t - 1) = t + 1 := by
  by_cases h1 : 0 ≤ t - 1
  · have a0 := two_mul_Nz t ht
    have a1 := two_mul_Nz (t - 1) h1
    have h2 : 2 * (Nz t - Nz (t - 1)) = 2 * (t + 1) := by linear_combination a0 - a1
    linarith
  · have ht0 : t = 0 := by omega
    subst ht0
    rw [Nz_zero, Nz_neg _ (by norm_num)]
    norm_num

/-- Second difference: `Δ²Nz t = 1` for `t ≥ 0` and `0` for `t < 0` —
the numerical content of `(1−t)³ · 1/(1−t)³ = 1`. -/
lemma Nz_second_diff (t : ℤ) :
    Nz t - 2 * Nz (t - 1) + Nz (t - 2) = if 0 ≤ t then 1 else 0 := by
  by_cases h0 : 0 ≤ t
  · rw [if_pos h0]
    by_cases h2 : 0 ≤ t - 2
    · have a0 := two_mul_Nz t h0
      have a1 := two_mul_Nz (t - 1) (by omega)
      have a2 := two_mul_Nz (t - 2) h2
      have key : 2 * (Nz t - 2 * Nz (t - 1) + Nz (t - 2)) = 2 := by
        linear_combination a0 - 2 * a1 + a2
      linarith
    · by_cases h1 : 0 ≤ t - 1
      · have ht1 : t = 1 := by omega
        subst ht1
        norm_num [Nz_neg (1 - 2 : ℤ) (by norm_num), Nz_zero]
        decide
      · have ht0 : t = 0 := by omega
        subst ht0
        rw [Nz_zero, Nz_neg _ (by norm_num), Nz_neg _ (by norm_num)]
        ring
  · rw [if_neg h0, Nz_neg _ (by omega), Nz_neg _ (by omega), Nz_neg _ (by omega)]
    ring

lemma Nz_mono {a b : ℤ} (h : a ≤ b) : Nz a ≤ Nz b := by
  by_cases ha : 0 ≤ a
  · rw [Nz, if_pos ha, Nz, if_pos (by omega)]
    exact N_mono (by omega)
  · rw [Nz, if_neg ha]
    exact Nz_nonneg b

lemma Nz_lt {a b : ℤ} (ha : 0 ≤ a) (h : a < b) : Nz a < Nz b := by
  rw [Nz, if_pos ha, Nz, if_pos (by omega)]
  exact N_strictMono (by omega)

/-- Windows of `Nz` are log-concave, integer-index form. -/
lemma Nz_window (m : ℤ) (hm : 2 ≤ m) : Nz m * Nz (m - 2) ≤ Nz (m - 1) ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m - 2 = (k : ℤ) := ⟨(m - 2).toNat, by omega⟩
  have a0 : Nz m = N (k + 2) := by
    rw [show m = ((k + 2 : ℕ) : ℤ) by push_cast; omega, Nz_natCast]
  have a1 : Nz (m - 1) = N (k + 1) := by
    rw [show m - 1 = ((k + 1 : ℕ) : ℤ) by push_cast; omega, Nz_natCast]
  have a2 : Nz (m - 2) = N k := by rw [hk, Nz_natCast]
  rw [a0, a1, a2]
  exact binomial_window_log_concave k

/-! ## Layer 1: the four arithmetic scenarios, and why each is log-concave -/

/-- The four possible shapes of the tested triple
`(a, b, c) = (g_{d-2}, g_{d-1}, g_d)` after the paper's structural analysis. -/
def GoodTriple (d a b c : ℤ) : Prop :=
  -- ε_d = 1 (p. 3): a window (N_m, N_{m-1}, N_{m-2}) with m = e - d + 2 ≥ 2
  (∃ m : ℤ, 2 ≤ m ∧ a = Nz m ∧ b = Nz (m - 1) ∧ c = Nz (m - 2))
  ∨
  -- Δ²g_d ≤ 0: covers r_d = 2 (via (4)) and the non-failure branch of r_d = 1
  (a + c ≤ 2 * b)
  ∨
  -- r_d = 0 (p. 3): Q_d = 0 forces the explicit values
  (∃ p : ℤ, 0 ≤ p ∧ a = d * (d - 1) ∧ b = d * (d + 1) ∧ c = (d + 1) * (d + 2) - p)
  ∨
  -- r_d = 1, putative failure (pp. 3–4): (6) plus x ≥ d and a ≤ d(d-1)
  (c = 2 * b - a + 1 ∧ d ≤ b - a ∧ a ≤ d * (d - 1))

/-- The AM–GM step of the paper (p. 2, between (4) and (5)). -/
lemma amgm_log_concave {a b c : ℤ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : a + c ≤ 2 * b) : a * c ≤ b ^ 2 := by
  nlinarith [sq_nonneg (a - c), sq_nonneg (a + c)]

/-- **Scenario r_d = 0** (p. 3): the direct calculation
`g_{d-1}² − g_{d-2} g_d = d(2(d+1) + (d−1) p_d) > 0`. -/
lemma r_eq_zero_log_concave {d p : ℤ} (hd : 2 ≤ d) (hp : 0 ≤ p) :
    d * (d - 1) * ((d + 1) * (d + 2) - p) < (d * (d + 1)) ^ 2 := by
  have key : (d * (d + 1)) ^ 2 - d * (d - 1) * ((d + 1) * (d + 2) - p)
      = d * (2 * (d + 1) + (d - 1) * p) := by ring
  have h1 : 0 ≤ (d - 1) * p := mul_nonneg (by linarith) hp
  nlinarith [key, h1]

/-- **Scenario r_d = 1, putative failure** (p. 4): with `x = b − a ≥ d` and
`y = a ≤ d(d−1)`, the margin is
`b² − ac = (y+x)² − y(y+2x+1) = x² − y ≥ d² − d(d−1) = d > 0`. -/
lemma r_eq_one_log_concave {d a b c : ℤ} (hd : 2 ≤ d) (hc : c = 2 * b - a + 1)
    (hx : d ≤ b - a) (ha2 : a ≤ d * (d - 1)) : a * c < b ^ 2 := by
  subst hc
  have hsq : d ^ 2 ≤ (b - a) ^ 2 := by nlinarith
  nlinarith [hsq]

/-- **Every scenario yields log-concavity of the tested triple** — the
complete case analysis of pp. 3–4 of the paper. -/
theorem GoodTriple.log_concave {d a b c : ℤ} (hd : 2 ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (h : GoodTriple d a b c) : a * c ≤ b ^ 2 := by
  rcases h with ⟨m, hm, rfl, rfl, rfl⟩ | h | ⟨p, hp, rfl, rfl, rfl⟩ | ⟨hceq, hx, ha2⟩
  · exact Nz_window m hm
  · exact amgm_log_concave ha hc h
  · exact le_of_lt (r_eq_zero_log_concave hd hp)
  · exact le_of_lt (r_eq_one_log_concave hd hceq hx ha2)

/-! ## Structural layer: the local algebra behind the imported hypotheses

The hypotheses `h3` and `hr1` of `theorem1_full` are the numerical shadows
of genuine linear-algebra and commutative-algebra facts — paper (2), (3),
(7), and the cyclic-Gorenstein-submodule step of p. 3.  This section
machine-checks those facts themselves, in the abstract, theorem-specific
form in which the paper uses them.  They are proved with full generality
over an arbitrary field / GCD domain / Artinian module, so instantiating
them at `K = Frac(R)`, `R = k[x₁,x₂,x₃]`, `M` the dualized module is pure
bookkeeping. -/

section StructuralLemmas

open Module

/-- **Paper (2), abstract form.**  If the space of linear dependencies of a
finite family of vectors is the line spanned by a single dependency `c` of
*full support* (`c i ≠ 0` for every `i`), then every proper subfamily is
linearly independent.

In the paper: tensoring the minimal exact complex (1) with `K = Frac(R)`
shows the kernel of `δ₂` is one-dimensional, spanned by the coordinate
vector of the minimal generators of `I` — all nonzero; hence every proper
subset of the columns of `δ₂` is `K`-linearly independent. -/
theorem proper_subfamily_linearIndependent
    {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : ι → V) (c : ι → K)
    (hker : ∀ g : ι → K, ∑ i, g i • f i = 0 → ∃ a : K, g = a • c)
    (hfull : ∀ i, c i ≠ 0)
    (s : Finset ι) (hs : s ≠ Finset.univ) :
    LinearIndependent K (fun i : s => f i) := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, i ∉ s := by
    by_contra hcon
    push Not at hcon
    exact hs (Finset.eq_univ_iff_forall.mpr hcon)
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  -- extend the dependency by zero to the whole index set
  set G : ι → K := fun i => if h : i ∈ s then g ⟨i, h⟩ else 0 with hG
  have hzero : ∀ x ∈ Finset.univ, x ∉ s → G x • f x = 0 := by
    intro x _ hx
    rw [hG]
    simp [dif_neg hx]
  have hGsum : ∑ i, G i • f i = 0 := by
    calc (∑ i, G i • f i)
        = ∑ i ∈ s, G i • f i :=
          (Finset.sum_subset (Finset.subset_univ s) hzero).symm
      _ = ∑ i : s, G ↑i • f ↑i := (Finset.sum_coe_sort s fun i => G i • f i).symm
      _ = ∑ i : s, g i • f ↑i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hG]
          simp
      _ = 0 := hg
  -- the extension is a multiple of the full-support vector, hence zero
  obtain ⟨a, ha⟩ := hker G hGsum
  have ha0 : a = 0 := by
    have h0 : G i₀ = 0 := by rw [hG]; simp [dif_neg hi₀]
    have h1 : a * c i₀ = 0 := by
      have := congrFun ha i₀
      rw [h0] at this
      simpa using this.symm
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (hfull i₀)
  have hGj : G ↑j = 0 := by
    have := congrFun ha ↑j
    rw [ha0] at this
    simpa using this
  rw [hG] at hGj
  simpa [dif_pos j.2] using hGj

/-- **Rank–nullity bookkeeping for (3).**  If `ψ ∘ φ = 0` and the kernel of
`φ` has dimension at most `ε`, then rank-nullity gives
`rank φ ≥ dim V − ε`, while `range φ ⊆ ker ψ` gives
`rank φ ≤ dim W − rank ψ`; together (in subtraction-free form)
`dim V + rank ψ ≤ dim W + ε`. -/
theorem rank_estimate
    {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup U] [Module K U]
    (φ : V →ₗ[K] W) (ψ : W →ₗ[K] U) (hcomp : ψ ∘ₗ φ = 0)
    {ε : ℕ} (hker : finrank K (LinearMap.ker φ) ≤ ε) :
    finrank K V + finrank K (LinearMap.range ψ) ≤ finrank K W + ε := by
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := LinearMap.finrank_range_add_finrank_ker ψ
  have h3 : finrank K (LinearMap.range φ) ≤ finrank K (LinearMap.ker ψ) :=
    Submodule.finrank_mono (LinearMap.range_le_ker_iff.mpr hcomp)
  omega

/-- **Paper (3): `Q_d − ε_d ≤ P_{<d} − r_d`, in additive form.**  The graded
zero pattern of minimality: the columns of `δ₂` of shift ≤ `d` (source
`V`, `dim V = Q_d`) can only involve rows of `F₁` of shift `< d`, i.e. the
restricted `δ₂` lands in the subspace `W'` spanned by those rows
(`dim W' = P_{<d}`).  Composing with `δ₁` gives zero, the kernel of the
restricted `δ₂` is at most `ε_d`-dimensional by (2), and `r_d` is by
definition the rank of `δ₁` restricted to `W'` — the image `W'.map ψ`.
Conclusion: `Q_d + r_d ≤ P_{<d} + ε_d`. -/
theorem rank_estimate_graded
    {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup U] [Module K U]
    (φ : V →ₗ[K] W) (W' : Submodule K W) (hzero : ∀ v, φ v ∈ W')
    (ψ : W →ₗ[K] U) (hcomp : ψ ∘ₗ φ = 0)
    {ε : ℕ} (hker : finrank K (LinearMap.ker φ) ≤ ε) :
    finrank K V + finrank K (W'.map ψ) ≤ finrank K W' + ε := by
  have hcomp' : (ψ ∘ₗ W'.subtype) ∘ₗ LinearMap.codRestrict W' φ hzero = 0 := by
    rw [LinearMap.comp_assoc, LinearMap.subtype_comp_codRestrict]
    exact hcomp
  have hker' :
      finrank K (LinearMap.ker (LinearMap.codRestrict W' φ hzero)) ≤ ε := by
    rwa [LinearMap.ker_codRestrict]
  have key := rank_estimate (LinearMap.codRestrict W' φ hzero)
    (ψ ∘ₗ W'.subtype) hcomp' hker'
  have hrange : LinearMap.range (ψ ∘ₗ W'.subtype) = W'.map ψ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rwa [hrange] at key

/-- **The UFD lemma (p. 3): `(Kv) ∩ R² = Rv` for a primitive vector.**
Over a GCD domain (in the paper, the UFD `R = k[x₁,x₂,x₃]`): if
`v = (v₁, v₂)` is primitive (its entries have no common non-unit factor)
and `b·w = a·v` with `b ≠ 0` — that is, `w = (a/b)·v` inside `Frac(R)²` —
then `w` is already an `R`-multiple of `v`.  This is the "divide a column
by the gcd of its entries / Euclid's lemma" step that produces the ideal
`J` with image `vJ`. -/
theorem primitive_line_saturated
    {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    {v w : Fin 2 → R} (hprim : IsRelPrime (v 0) (v 1))
    {a b : R} (hb : b ≠ 0) (h : ∀ i, b * w i = a * v i) :
    ∃ r : R, ∀ i, w i = r * v i := by
  obtain ⟨a', b', ea, eb, hunit⟩ := extract_gcd a b
  have hg : gcd a b ≠ 0 := fun h0 => hb (by rw [eb, h0, zero_mul])
  -- reduce the fraction: b'·w = a'·v with a', b' coprime
  have hred : ∀ i, b' * w i = a' * v i := by
    intro i
    apply mul_left_cancel₀ hg
    calc gcd a b * (b' * w i) = b * w i := by rw [← mul_assoc, ← eb]
      _ = a * v i := h i
      _ = gcd a b * (a' * v i) := by conv_lhs => rw [ea, mul_assoc]
  have hrel : IsRelPrime b' a' := (gcd_isUnit_iff_isRelPrime.mp hunit).symm
  -- Euclid: b' divides both entries of the primitive v, so b' is a unit
  have hdvd : ∀ i, b' ∣ v i := fun i =>
    hrel.dvd_of_dvd_mul_left ⟨w i, (hred i).symm⟩
  obtain ⟨u, hu⟩ := hprim (hdvd 0) (hdvd 1)
  refine ⟨↑u⁻¹ * a', fun i => ?_⟩
  have hi := hred i
  rw [← hu] at hi
  calc w i = ↑u⁻¹ * (↑u * w i) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ↑u⁻¹ * (a' * v i) := by rw [hi]
    _ = ↑u⁻¹ * a' * v i := (mul_assoc _ _ _).symm

/-- The same statement phrased literally over the fraction field: an
element of `R²` lying on the `K`-line through a primitive vector is an
`R`-multiple of it (`(Kv) ∩ R² = Rv`). -/
theorem primitive_line_saturated_fraction
    {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    {v w : Fin 2 → R} (hprim : IsRelPrime (v 0) (v 1))
    (k : FractionRing R)
    (h : ∀ i, algebraMap R (FractionRing R) (w i)
          = k * algebraMap R (FractionRing R) (v i)) :
    ∃ r : R, ∀ i, w i = r * v i := by
  obtain ⟨a, b, hbmem, hk⟩ := IsFractionRing.div_surjective (A := R) k
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have hbK : algebraMap R (FractionRing R) b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective R (FractionRing R) (by rw [h0, map_zero]))
  refine primitive_line_saturated hprim (a := a) (b := b) hb fun i => ?_
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_mul, map_mul, h i, ← hk]
  field_simp

/-- **The passage from the low-shift image to `vJ`, and the truncated-kernel
identity (paper (7)).**  A linear map `φ` into `Rⁿ` whose image lies on the
line through a nonzero vector `v` (over a domain) factors as
`φ = (· • v) ∘ ψ` for a scalar-valued linear map `ψ`.  The ideal
`J := range ψ` then realizes the image as `vJ`
(`range φ = J.map (· • v)`), membership works degreewise
(`c • v ∈ im φ ↔ c ∈ J` — the paper's `cv ∈ (vJ) ⟺ c ∈ J`, whose proof
"uses the injectivity of multiplication by the nonzero vector `v`"),
and `ker ψ = ker φ`. -/
theorem line_factorization
    {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    {n : ℕ} {v : Fin n → R} (hv : v ≠ 0)
    (φ : M →ₗ[R] (Fin n → R)) (hline : ∀ m, ∃ r : R, φ m = r • v) :
    ∃ ψ : M →ₗ[R] R,
      (∀ m, φ m = ψ m • v) ∧
      LinearMap.range φ
        = (LinearMap.range ψ).map (LinearMap.toSpanSingleton R (Fin n → R) v) ∧
      (∀ r : R, r • v ∈ LinearMap.range φ ↔ r ∈ LinearMap.range ψ) ∧
      LinearMap.ker ψ = LinearMap.ker φ := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  -- multiplication by v is injective, so the coefficient is unique
  have huniq : ∀ {r s : R}, r • v = s • v → r = s := by
    intro r s hrs
    have h := congrFun hrs i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact mul_right_cancel₀ hi₀ h
  choose c hc using hline
  have hadd : ∀ m₁ m₂, c (m₁ + m₂) = c m₁ + c m₂ := fun m₁ m₂ =>
    huniq (by rw [← hc, map_add, hc, hc, add_smul])
  have hsmul : ∀ (r : R) (m : M), c (r • m) = r * c m := fun r m =>
    huniq (by rw [← hc, map_smul, hc, ← mul_smul])
  let ψ : M →ₗ[R] R := ⟨⟨c, hadd⟩, fun r m => by simpa using hsmul r m⟩
  have hφψ : ∀ m, φ m = ψ m • v := hc
  refine ⟨ψ, hφψ, ?_, ?_, ?_⟩
  · -- range φ = vJ
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      refine ⟨ψ m, ⟨m, rfl⟩, ?_⟩
      rw [LinearMap.toSpanSingleton_apply]
      exact (hφψ m).symm
    · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      refine ⟨m, ?_⟩
      rw [LinearMap.toSpanSingleton_apply]
      exact hφψ m
  · -- c • v ∈ im φ ↔ c ∈ J
    intro r
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, huniq (by rw [← hφψ m, hm])⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, hφψ m⟩
  · -- the truncated-kernel identity ker ψ = ker φ
    ext m
    simp only [LinearMap.mem_ker]
    constructor
    · intro h0
      rw [hφψ m, h0, zero_smul]
    · intro h0
      exact huniq (by rw [← hφψ m, h0, zero_smul])

/-- The socle of a submodule `N` of `M`, relative to the ambient lattice:
the join of the simple submodules of `M` contained in `N` (simple = atom
in the submodule lattice). -/
def socleOf {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Submodule R M :=
  sSup {S | S ≤ N ∧ IsAtom S}

section Socle

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

lemma socleOf_le (N : Submodule R M) : socleOf N ≤ N :=
  sSup_le fun _ hS => hS.1

lemma socleOf_mono {N N' : Submodule R M} (h : N ≤ N') :
    socleOf N ≤ socleOf N' :=
  sSup_le_sSup fun _ hS => ⟨hS.1.trans h, hS.2⟩

/-- Every nonzero submodule of an Artinian (e.g. finite-length) module
contains a simple submodule, so its socle is nonzero. -/
lemma socleOf_ne_bot [IsArtinian R M] {N : Submodule R M} (hN : N ≠ ⊥) :
    socleOf N ≠ ⊥ := by
  haveI : IsAtomic (Submodule R M) :=
    isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf
  obtain h | ⟨S, hS, hSN⟩ := IsAtomic.eq_bot_or_exists_atom_le N
  · exact absurd h hN
  · intro hbot
    exact hS.1 (le_bot_iff.mp (hbot ▸ le_sSup ⟨hSN, hS⟩))

/-- In a finite-length module with simple socle, every nonzero submodule
has the *same* — hence simple — socle. -/
theorem socleOf_eq_top_socle [IsArtinian R M]
    (hsoc : IsAtom (socleOf (⊤ : Submodule R M)))
    {N : Submodule R M} (hN : N ≠ ⊥) : socleOf N = socleOf ⊤ :=
  (hsoc.le_iff.mp (socleOf_mono le_top)).resolve_left (socleOf_ne_bot hN)

/-- **The elementary module lemma of p. 3.**  A nonzero cyclic submodule
`R·x` of a finite-length module with simple socle again has simple socle,
and the corresponding cyclic quotient `R ⧸ Ann(x)` — the paper's
`B = R/Ann(H)`, presented as `R` modulo the kernel of `r ↦ r • x` — is an
Artinian module isomorphic to it. -/
theorem cyclic_submodule_simple_socle [IsArtinian R M]
    (hsoc : IsAtom (socleOf (⊤ : Submodule R M))) {x : M} (hx : x ≠ 0) :
    IsSimpleModule R (socleOf (Submodule.span R {x}))
      ∧ IsArtinian R (R ⧸ LinearMap.ker (LinearMap.toSpanSingleton R M x))
      ∧ Nonempty ((R ⧸ LinearMap.ker (LinearMap.toSpanSingleton R M x))
          ≃ₗ[R] Submodule.span R {x}) := by
  have hN : Submodule.span R {x} ≠ ⊥ := by
    simpa [Submodule.span_singleton_eq_bot] using hx
  have equiv : (R ⧸ LinearMap.ker (LinearMap.toSpanSingleton R M x))
      ≃ₗ[R] Submodule.span R {x} :=
    (LinearMap.quotKerEquivRange _).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton x))
  refine ⟨?_, ?_, ⟨equiv⟩⟩
  · rw [isSimpleModule_iff_isAtom, socleOf_eq_top_socle hsoc hN]
    exact hsoc
  · exact isArtinian_of_linearEquiv equiv.symm

end Socle

end StructuralLemmas

/-! ## Layer 2: from the resolution numerics to the scenarios

The finite sums `Σ_b f(b) · Nz(t − b)` over shifts `b ∈ [0, u]` are the
graded dimension counts contributed by a free module `⊕_b R(−b)^{f(b)}`. -/

/-- `shiftSum u f t = Σ_{b=0}^{u} f b · Nz (t − b)`: the degree-`t` dimension
of the graded free module with `f b` summands `R(−b)`. -/
noncomputable def shiftSum (u : ℤ) (f : ℤ → ℤ) (t : ℤ) : ℤ :=
  ∑ b ∈ Finset.Icc (0 : ℤ) u, f b * Nz (t - b)

lemma shiftSum_nonneg (u : ℤ) {f : ℤ → ℤ} (hf : ∀ b, 0 ≤ f b) (t : ℤ) :
    0 ≤ shiftSum u f t := by
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (hf b) (Nz_nonneg _)

/-- If all coefficients with shift ≤ `t` vanish, the sum vanishes. -/
lemma shiftSum_vanish (u : ℤ) (f : ℤ → ℤ) (t : ℤ)
    (hlow : ∀ b, 0 ≤ b → b ≤ t → f b = 0) : shiftSum u f t = 0 := by
  refine Finset.sum_eq_zero fun b hb => ?_
  by_cases h : b ≤ t
  · rw [hlow b (Finset.mem_Icc.mp hb).1 h, zero_mul]
  · rw [Nz_neg _ (by omega), mul_zero]

/-- If all coefficients with shift < `t` vanish, only the shift-`t` term
survives. -/
lemma shiftSum_single (u : ℤ) (f : ℤ → ℤ) (t : ℤ) (h0 : 0 ≤ t) (htu : t ≤ u)
    (hlow : ∀ b, 0 ≤ b → b < t → f b = 0) : shiftSum u f t = f t := by
  have hside : ∀ b ∈ Finset.Icc (0 : ℤ) u, b ≠ t → f b * Nz (t - b) = 0 := by
    intro b hb hbne
    by_cases hlt : b < t
    · rw [hlow b (Finset.mem_Icc.mp hb).1 hlt, zero_mul]
    · rw [Nz_neg _ (by omega), mul_zero]
  rw [shiftSum,
    Finset.sum_eq_single_of_mem t (Finset.mem_Icc.mpr ⟨h0, htu⟩) hside,
    sub_self, Nz_zero, mul_one]

/-- **The Hilbert-numerator computation** (paper p. 2, "summing its
coefficients through degree d"): the second difference of a shift sum
telescopes to the partial coefficient sum `Σ_{b ≤ d} f b`. -/
lemma shiftSum_second_diff (u : ℤ) (f : ℤ → ℤ) (d : ℤ) (_hd0 : 0 ≤ d)
    (hdu : d ≤ u) :
    shiftSum u f d - 2 * shiftSum u f (d - 1) + shiftSum u f (d - 2)
      = ∑ b ∈ Finset.Icc (0 : ℤ) d, f b := by
  have step : ∀ b ∈ Finset.Icc (0 : ℤ) u,
      f b * Nz (d - b) - 2 * (f b * Nz (d - 1 - b)) + f b * Nz (d - 2 - b)
        = if b ≤ d then f b else 0 := by
    intro b _
    have e1 : d - 1 - b = d - b - 1 := by ring
    have e2 : d - 2 - b = d - b - 2 := by ring
    rw [e1, e2]
    have h := Nz_second_diff (d - b)
    by_cases hbd : b ≤ d
    · rw [if_pos hbd]
      rw [if_pos (by omega : (0 : ℤ) ≤ d - b)] at h
      linear_combination f b * h
    · rw [if_neg hbd]
      rw [if_neg (by omega : ¬(0 : ℤ) ≤ d - b)] at h
      linear_combination f b * h
  unfold shiftSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl step, ← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- **The deep dispatch** (pp. 2–4 of the paper).  From the primitive
numerical hypotheses — rank additivity `hres` of the exact complex (1), the
rank estimate `h3` (= (3)), and the structural facts `hε1`, `hr0`, `hr1` —
derive that every tested triple of the reindexed dual falls into one of the
four scenarios.  All the arithmetic of the paper (deriving (4), (5) ⇒ (6),
(9), `x ≥ d`, `g_{d-2} ≤ d(d-1)`) is machine-checked here.

The abstract predicate `Gor B E` reads "`B` is the Hilbert function of a
standard graded Artinian Gorenstein quotient of `R` of socle degree `E`"
(the paper's `B = R/Ann(H)`).  `hr1` produces such a `B` (or `B = 0`, the
paper's `H = 0` case) together with equation (8); `hGor` records the
elementary facts that any such Hilbert function is supported on `[0, ∞)`
and bounded by that of `R`; and **`hStanley` — Stanley's theorem (Lemma 1),
the sole major imported structural theorem — enters as its own separately
named hypothesis** rather than being packaged into `hr1`. -/
theorem deep_dispatch
    (e : ℤ) (g h p q r ε : ℤ → ℤ)
    (Gor : (ℤ → ℤ) → ℤ → Prop)
    (hquot : ∀ t, h t ≤ Nz t)
    (hrev : ∀ t, g t = h (e - t))
    (hp0 : ∀ b, 0 ≤ p b) (hq0 : ∀ b, 0 ≤ q b)
    (hres : ∀ t, t ≤ e →
      g t = 2 * Nz t - shiftSum (e + 3) p t + shiftSum (e + 3) q t
              - Nz (t - (e + 3)))
    (hrε : ∀ d, 2 ≤ d → d ≤ e →
      (r d = 0 ∨ r d = 1 ∨ r d = 2) ∧ (ε d = 0 ∨ ε d = 1))
    (h3 : ∀ d, 2 ≤ d → d ≤ e →
      (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) - ε d
        ≤ (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b) - r d)
    (hε1 : ∀ d, 2 ≤ d → d ≤ e → ε d = 1 →
      ∀ t, t < e + 3 - d → h t = Nz t)
    (hr0 : ∀ d, 2 ≤ d → d ≤ e → r d = 0 →
      ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b = 0)
    (hr1 : ∀ d, 2 ≤ d → d ≤ e → r d = 1 → p d = 0 →
      g d - 2 * g (d - 1) + g (d - 2) = 1 →
      ∃ (a : ℤ) (B : ℤ → ℤ), 0 ≤ a ∧ a < d ∧
        ((∀ t, B t = 0) ∨ Gor B (e - a)) ∧
        (∀ t, d - 2 ≤ t → t ≤ d → g t = 2 * Nz t - Nz (t - a) + B (t - a)))
    (hGor : ∀ B E, Gor B E →
      (∀ t : ℤ, t < 0 → B t = 0) ∧ (∀ t, 0 ≤ B t) ∧ (∀ t, B t ≤ Nz t))
    (hStanley : ∀ B E, Gor B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ d, 2 ≤ d → d ≤ e → GoodTriple d (g (d - 2)) (g (d - 1)) (g d) := by
  intro d hd hde
  obtain ⟨hrc, hεc⟩ := hrε d hd hde
  -- the second-difference identity Δ²g_d = 2 − P_{≤d} + Q_d  (paper p. 2)
  have hs2p := shiftSum_second_diff (e + 3) p d (by omega) (by omega)
  have hs2q := shiftSum_second_diff (e + 3) q d (by omega) (by omega)
  have hNdd := Nz_second_diff d
  rw [if_pos (by omega : (0 : ℤ) ≤ d)] at hNdd
  have hz0 : Nz (d - (e + 3)) = 0 := Nz_neg _ (by omega)
  have hz1 : Nz (d - 1 - (e + 3)) = 0 := Nz_neg _ (by omega)
  have hz2 : Nz (d - 2 - (e + 3)) = 0 := Nz_neg _ (by omega)
  have hΔ : g d - 2 * g (d - 1) + g (d - 2)
      = 2 - (∑ b ∈ Finset.Icc (0 : ℤ) d, p b)
          + (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) := by
    have h₁ := hres d (by omega)
    have h₂ := hres (d - 1) (by omega)
    have h₃ := hres (d - 2) (by omega)
    linarith
  -- split off the top coefficient: P_{≤d} = p_d + P_{<d}
  have hsplitp : (∑ b ∈ Finset.Icc (0 : ℤ) d, p b)
      = p d + ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b := by
    have hins : Finset.Icc (0 : ℤ) d = insert d (Finset.Icc (0 : ℤ) (d - 1)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  rcases hεc with hε0 | hεone
  · -- ε_d = 0: dispatch on r_d
    have h3' := h3 d hd hde
    rw [hε0] at h3'
    rcases hrc with hr' | hr' | hr'
    · -- r_d = 0 (paper p. 3, third case)
      rw [hr'] at h3'
      have hP0 := hr0 d hd hde hr'
      have hpz : ∀ b, 0 ≤ b → b ≤ d - 1 → p b = 0 := fun b hb0 hbd =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hp0 b)).mp hP0 b
          (Finset.mem_Icc.mpr ⟨hb0, hbd⟩)
      have hQ0 : (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) = 0 := by
        have hQnn : 0 ≤ ∑ b ∈ Finset.Icc (0 : ℤ) d, q b :=
          Finset.sum_nonneg fun b _ => hq0 b
        linarith
      have hqz : ∀ b, 0 ≤ b → b ≤ d → q b = 0 := fun b hb0 hbd =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hq0 b)).mp hQ0 b
          (Finset.mem_Icc.mpr ⟨hb0, hbd⟩)
      -- evaluate g at d−2, d−1, d: only 2·Nz and the p_d term survive
      have ea : g (d - 2) = d * (d - 1) := by
        have h₁ := hres (d - 2) (by omega)
        have h₂ : shiftSum (e + 3) p (d - 2) = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hpz b hb0 (by omega)
        have h₃ : shiftSum (e + 3) q (d - 2) = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hqz b hb0 (by omega)
        have h₄ := two_mul_Nz (d - 2) (by omega)
        linarith
      have eb : g (d - 1) = d * (d + 1) := by
        have h₁ := hres (d - 1) (by omega)
        have h₂ : shiftSum (e + 3) p (d - 1) = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hpz b hb0 (by omega)
        have h₃ : shiftSum (e + 3) q (d - 1) = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hqz b hb0 (by omega)
        have h₄ := two_mul_Nz (d - 1) (by omega)
        linarith
      have ec : g d = (d + 1) * (d + 2) - p d := by
        have h₁ := hres d (by omega)
        have h₂ : shiftSum (e + 3) p d = p d :=
          shiftSum_single _ _ _ (by omega) (by omega)
            fun b hb0 hbd => hpz b hb0 (by omega)
        have h₃ : shiftSum (e + 3) q d = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hqz b hb0 (by omega)
        have h₄ := two_mul_Nz d (by omega)
        linarith
      exact Or.inr (Or.inr (Or.inl ⟨p d, hp0 d, ea, eb, ec⟩))
    · -- r_d = 1: derive Δ² ≤ 1 − p_d; a failure forces (6)
      rw [hr'] at h3'
      by_cases hΔ0 : g d - 2 * g (d - 1) + g (d - 2) ≤ 0
      · exact Or.inr (Or.inl (by linarith))
      · have hpos := not_le.mp hΔ0
        have hone : (1 : ℤ) ≤ g d - 2 * g (d - 1) + g (d - 2) := by
          have := Int.add_one_le_iff.mpr hpos
          linarith
        have hpd0 : p d = 0 := le_antisymm (by linarith) (hp0 d)
        have hΔeq : g d - 2 * g (d - 1) + g (d - 2) = 1 :=
          le_antisymm (by linarith) hone
        obtain ⟨a, B, ha0, had, hBcase, h8⟩ := hr1 d hd hde hr' hpd0 hΔeq
        -- in the `H = 0` case `B = 0` and every needed fact is trivial;
        -- otherwise they come from `hGor` and from Stanley's theorem
        obtain ⟨hBneg, hB0, hBN, hStan⟩ :
            (∀ t : ℤ, t < 0 → B t = 0) ∧ (∀ t, 0 ≤ B t) ∧
            (∀ t, B t ≤ Nz t) ∧
            (∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ e - a → B j ≤ B i) := by
          rcases hBcase with hB | hGorB
          · exact ⟨fun t _ => hB t, fun t => le_of_eq (hB t).symm,
              fun t => by rw [hB t]; exact Nz_nonneg t,
              fun i j _ _ _ => le_of_eq ((hB j).trans (hB i).symm)⟩
          · obtain ⟨h₁, h₂, h₃⟩ := hGor B (e - a) hGorB
            exact ⟨h₁, h₂, h₃, hStanley B (e - a) hGorB⟩
        have h8a := h8 (d - 2) (by omega) (by omega)
        have h8b := h8 (d - 1) (by omega) (by omega)
        -- inequality (9): 2d ≤ e + 2, via N_{d-1} ≤ g_{d-1} ≤ N_{e-d+1}
        have hb_lb : Nz (d - 1) ≤ g (d - 1) := by
          have hmono : Nz (d - 1 - a) ≤ Nz (d - 1) := Nz_mono (by omega)
          have := hB0 (d - 1 - a)
          linarith
        have hb_ub : g (d - 1) ≤ Nz (e - d + 1) := by
          rw [hrev, show e - (d - 1) = e - d + 1 from by ring]
          exact hquot _
        have h9 : 2 * d ≤ e + 2 := by
          by_contra hcon
          have hcon' : e + 2 < 2 * d := by omega
          have hlt : Nz (e - d + 1) < Nz (d - 1) := Nz_lt (by omega) (by omega)
          linarith
        -- D = B_{n-1} − B_{n-2} ≥ 0 by Stanley's monotonicity (Lemma 1)
        have hD : B (d - 2 - a) ≤ B (d - 1 - a) := by
          by_cases hn2 : 0 ≤ d - 2 - a
          · exact hStan (d - 1 - a) (d - 2 - a) hn2 (by omega) (by linarith)
          · rw [hBneg _ (by omega)]
            exact hB0 _
        -- x = g_{d-1} − g_{d-2} = 2d − (d − a) + D = d + a + D ≥ d  (p. 4)
        have hdiff1 : Nz (d - 1) - Nz (d - 2) = d := by
          have hdd := Nz_diff (d - 1) (by omega)
          rw [show d - 1 - 1 = d - 2 from by ring] at hdd
          linarith
        have hdiff2 : Nz (d - 1 - a) - Nz (d - 2 - a) = d - a := by
          have hdd := Nz_diff (d - 1 - a) (by omega)
          rw [show d - 1 - a - 1 = d - 2 - a from by ring] at hdd
          linarith
        have hx : d ≤ g (d - 1) - g (d - 2) := by linarith
        -- g_{d-2} ≤ 2 N_{d-2} = d(d-1)  (p. 4)
        have hab : g (d - 2) ≤ d * (d - 1) := by
          have hBb : B (d - 2 - a) ≤ Nz (d - 2 - a) := hBN _
          have h₄ := two_mul_Nz (d - 2) (by omega)
          linarith
        exact Or.inr (Or.inr (Or.inr ⟨by linarith, hx, hab⟩))
    · -- r_d = 2: (4) gives Δ²g_d ≤ −p_d ≤ 0
      rw [hr'] at h3'
      have hpd := hp0 d
      exact Or.inr (Or.inl (by linarith))
  · -- ε_d = 1 (paper p. 3, first case): the triple is a window of Nz
    refine Or.inl ⟨e - d + 2, by omega, ?_, ?_, ?_⟩
    · have hval := hε1 d hd hde hεone (e - d + 2) (by omega)
      rw [hrev, show e - (d - 2) = e - d + 2 from by ring, hval]
    · have hval := hε1 d hd hde hεone (e - d + 1) (by omega)
      rw [hrev, show e - (d - 1) = e - d + 1 from by ring, hval]
      congr 1
      ring
    · have hval := hε1 d hd hde hεone (e - d) (by omega)
      rw [hrev, hval]
      congr 1
      ring

/-! ## Assembling the theorem -/

/-- Log-concavity of the reindexed dual at every tested center. -/
theorem dual_log_concave (e : ℤ) (g : ℤ → ℤ) (gnn : ∀ t, 0 ≤ g t)
    (hgood : ∀ d : ℤ, 2 ≤ d → d ≤ e →
      GoodTriple d (g (d - 2)) (g (d - 1)) (g d)) :
    ∀ d : ℤ, 2 ≤ d → d ≤ e → g (d - 2) * g d ≤ g (d - 1) ^ 2 :=
  fun d h2 he => (hgood d h2 he).log_concave h2 (gnn _) (gnn _)

/-- **Theorem 1, scenario form**: if every tested triple of the reindexed
dual is a `GoodTriple`, then `h` is log-concave.  (Reversal preserves
log-concavity, paper p. 4.) -/
theorem theorem1 (e : ℤ) (h g : ℤ → ℤ)
    (hnn : ∀ t, 0 ≤ h t)
    (hrev : ∀ t, g t = h (e - t))
    (hgood : ∀ d : ℤ, 2 ≤ d → d ≤ e →
      GoodTriple d (g (d - 2)) (g (d - 1)) (g d)) :
    ∀ i : ℤ, 1 ≤ i → i ≤ e - 1 → h (i - 1) * h (i + 1) ≤ h i ^ 2 := by
  intro i h1 hie
  have gnn : ∀ t, 0 ≤ g t := fun t => by rw [hrev]; exact hnn _
  have key := dual_log_concave e g gnn hgood (e - i + 1) (by linarith) (by linarith)
  have e2 : g (e - i + 1 - 2) = h (i + 1) := by rw [hrev]; congr 1; ring
  have e1 : g (e - i + 1 - 1) = h i := by rw [hrev]; congr 1; ring
  have e0 : g (e - i + 1) = h (i - 1) := by rw [hrev]; congr 1; ring
  rw [e2, e1, e0] at key
  linarith [key, mul_comm (h (i + 1)) (h (i - 1))]

/-- **Theorem 1, full form.**  Log-concavity of the Hilbert function of a
standard graded Artinian level algebra of embedding dimension three, socle
degree `e`, and type two — derived from the primitive numerical shadows of
the paper's commutative algebra (see the header of this file for the exact
list of assumed structural facts `hrev, hquot, hres, hrε, h3, hε1, hr0, hr1,
hGor` and their sources in the paper).

Stanley's theorem (Lemma 1 of the paper, Zanello's characteristic-free
version) is the sole major imported structural theorem; it enters as the
separately named hypothesis `hStanley`, quantified over the abstract
Gorenstein-Hilbert-function predicate `Gor`, rather than being packaged
into the case-analysis hypothesis `hr1`. -/
theorem theorem1_full
    (e : ℤ) (h g p q r ε : ℤ → ℤ)
    (Gor : (ℤ → ℤ) → ℤ → Prop)
    (hnn : ∀ t, 0 ≤ h t)
    (hquot : ∀ t, h t ≤ Nz t)
    (hrev : ∀ t, g t = h (e - t))
    (hp0 : ∀ b, 0 ≤ p b) (hq0 : ∀ b, 0 ≤ q b)
    (hres : ∀ t, t ≤ e →
      g t = 2 * Nz t - shiftSum (e + 3) p t + shiftSum (e + 3) q t
              - Nz (t - (e + 3)))
    (hrε : ∀ d, 2 ≤ d → d ≤ e →
      (r d = 0 ∨ r d = 1 ∨ r d = 2) ∧ (ε d = 0 ∨ ε d = 1))
    (h3 : ∀ d, 2 ≤ d → d ≤ e →
      (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) - ε d
        ≤ (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b) - r d)
    (hε1 : ∀ d, 2 ≤ d → d ≤ e → ε d = 1 →
      ∀ t, t < e + 3 - d → h t = Nz t)
    (hr0 : ∀ d, 2 ≤ d → d ≤ e → r d = 0 →
      ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b = 0)
    (hr1 : ∀ d, 2 ≤ d → d ≤ e → r d = 1 → p d = 0 →
      g d - 2 * g (d - 1) + g (d - 2) = 1 →
      ∃ (a : ℤ) (B : ℤ → ℤ), 0 ≤ a ∧ a < d ∧
        ((∀ t, B t = 0) ∨ Gor B (e - a)) ∧
        (∀ t, d - 2 ≤ t → t ≤ d → g t = 2 * Nz t - Nz (t - a) + B (t - a)))
    (hGor : ∀ B E, Gor B E →
      (∀ t : ℤ, t < 0 → B t = 0) ∧ (∀ t, 0 ≤ B t) ∧ (∀ t, B t ≤ Nz t))
    (hStanley : ∀ B E, Gor B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ e - 1 → h (i - 1) * h (i + 1) ≤ h i ^ 2 :=
  theorem1 e h g hnn hrev
    (deep_dispatch e g h p q r ε Gor hquot hrev hp0 hq0 hres hrε h3 hε1 hr0
      hr1 hGor hStanley)

/-! ## The formal algebraic input (roadmap item 1)

This section begins the programme of deriving the structural hypotheses of
`theorem1_full` from an actual formal algebra rather than assuming their
numerical shadows.  It formalizes the paper's *starting object*:

  `R = k[x₁,x₂,x₃]`,  `A = R/I`,  `I` homogeneous,

standard graded (the degree-`n` piece of `A` being the image of `R_n`),
Artinian (finite-dimensional over `k`), of embedding dimension three, with
socle concentrated in degree `e` and of dimension two — a codimension-three
level algebra of type two (`IsTypeTwoLevel`) — together with its honest
Hilbert function `hilb I : ℤ → ℤ`.

Machine-checked here, from that formal object:

* the dimension count `dim_k R_n = binom(n+2,2) = N n` (stars and bars),
  giving `h_t ≤ N_t` for any graded quotient — the hypotheses `hnn` and
  `hquot` of `theorem1_full` become theorems (`hilb_nonneg`, `hilb_le_Nz`);
* a *concrete* Gorenstein predicate `GorensteinQuotientHF` — "`B` is the
  Hilbert function of a standard graded Artinian quotient of `R` with
  one-dimensional socle concentrated in degree `E`" — whose elementary
  bounds discharge the hypothesis `hGor` (`GorensteinQuotientHF.bounds`),
  and which turns `hStanley` into a faithful statement of Stanley's theorem
  about actual Gorenstein quotients of `k[x₁,x₂,x₃]` rather than a
  statement about an abstract predicate variable;
* `theorem1_of_level`: the main theorem restated from the formal algebra,
  with `hnn`, `hquot`, `hGor` *derived* rather than assumed.  The remaining
  hypotheses (`hrev`, `hres`, `hrε`, `h3`, `hε1`, `hr0`, `hr1`, `hStanley`)
  are now propositions about the concrete Hilbert function of `A = R/I`,
  i.e. precisely specified lemmas awaiting the resolution-theoretic
  development (roadmap items 2–10), plus Stanley's theorem (item 12). -/

section FormalAlgebra

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type*) [Field k]

/-- The ambient polynomial ring `R = k[x₁,x₂,x₃]`. -/
abbrev R3 := MvPolynomial (Fin 3) k

/-- **Stars and bars**: exponent vectors of total degree `n` in three
variables correspond to multisets of size `n` over `Fin 3`. -/
noncomputable def degreeSetEquivSym (n : ℕ) :
    ↥{d : Fin 3 →₀ ℕ | d.degree = n} ≃ Sym (Fin 3) n :=
  (Equiv.subtypeEquivRight fun d => by
    simp [Finsupp.degree_apply, Finsupp.sum]).trans (Sym.equivNatSum (Fin 3) n).symm

noncomputable instance (n : ℕ) : Fintype ↥{d : Fin 3 →₀ ℕ | d.degree = n} :=
  Fintype.ofEquiv (Sym (Fin 3) n) (degreeSetEquivSym n).symm

/-- **The dimension count of roadmap item 1**: the degree-`n` piece of
`R = k[x₁,x₂,x₃]` has dimension `binom(n+2,2) = N n`, by the monomial
basis and stars and bars. -/
theorem finrank_homogeneousSubmodule (n : ℕ) :
    finrank k (homogeneousSubmodule (Fin 3) k n) = (n + 2).choose 2 := by
  have e1 : finrank k (homogeneousSubmodule (Fin 3) k n)
      = finrank k (Finsupp.supported k k {d : Fin 3 →₀ ℕ | d.degree = n}) := by
    rw [homogeneousSubmodule_eq_finsupp_supported]
    rfl
  have e2 : finrank k (Finsupp.supported k k {d : Fin 3 →₀ ℕ | d.degree = n})
      = finrank k ((↥{d : Fin 3 →₀ ℕ | d.degree = n}) →₀ k) :=
    (Finsupp.supportedEquivFinsupp _).finrank_eq
  have e3 : finrank k ((↥{d : Fin 3 →₀ ℕ | d.degree = n}) →₀ k)
      = Fintype.card ↥{d : Fin 3 →₀ ℕ | d.degree = n} :=
    finrank_finsupp_self k
  have e4 : Fintype.card ↥{d : Fin 3 →₀ ℕ | d.degree = n}
      = Fintype.card (Sym (Fin 3) n) :=
    Fintype.card_congr (degreeSetEquivSym n)
  have e5 : Fintype.card (Sym (Fin 3) n)
      = (Fintype.card (Fin 3) + n - 1).choose n :=
    Sym.card_sym_eq_choose n
  have e6 : (Fintype.card (Fin 3) + n - 1).choose n = (n + 2).choose 2 := by
    have h := Nat.choose_symm (show 2 ≤ n + 2 by omega)
    rw [Nat.add_sub_cancel] at h
    rw [Fintype.card_fin, show 3 + n - 1 = n + 2 by omega, h]
  omega

instance homogeneousSubmodule_finiteDimensional (n : ℕ) :
    FiniteDimensional k (homogeneousSubmodule (Fin 3) k n) :=
  FiniteDimensional.of_finrank_pos <| by
    rw [finrank_homogeneousSubmodule k n]
    exact Nat.choose_pos (by omega)

variable {k}

/-- The degree-`n` graded piece of `A = R/I`: the image of `R_n` under the
quotient map.  For a homogeneous ideal this is the standard grading of `A`. -/
noncomputable def quotPiece (I : Ideal (R3 k)) (n : ℕ) : Submodule k (R3 k ⧸ I) :=
  (homogeneousSubmodule (Fin 3) k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

/-- The (integer-indexed) Hilbert function of `A = R/I`:
`hilb I t = dim_k A_t`, vanishing in negative degrees. -/
noncomputable def hilb (I : Ideal (R3 k)) (t : ℤ) : ℤ :=
  if 0 ≤ t then (finrank k (quotPiece I t.toNat) : ℤ) else 0

lemma hilb_neg (I : Ideal (R3 k)) {t : ℤ} (ht : t < 0) : hilb I t = 0 := by
  rw [hilb, if_neg (by omega)]

/-- The hypothesis `hnn` of `theorem1_full`, now a theorem: dimensions are
nonnegative. -/
lemma hilb_nonneg (I : Ideal (R3 k)) (t : ℤ) : 0 ≤ hilb I t := by
  rw [hilb]
  split
  · exact Int.natCast_nonneg _
  · exact le_refl 0

/-- The hypothesis `hquot` of `theorem1_full`, now a theorem: `A` is a
degreewise quotient of `R`, so `h_t = dim A_t ≤ dim R_t = N_t`. -/
lemma hilb_le_Nz (I : Ideal (R3 k)) (t : ℤ) : hilb I t ≤ Nz t := by
  rw [hilb, Nz]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, if_pos ht]
    have hle : finrank k (quotPiece I t.toNat)
        ≤ finrank k (homogeneousSubmodule (Fin 3) k t.toNat) :=
      Submodule.finrank_map_le _ _
    have heq := finrank_homogeneousSubmodule k t.toNat
    rw [N]
    exact_mod_cast hle.trans_eq heq
  · rw [if_neg ht, if_neg ht]

/-- The socle of `A = R/I`: the elements killed by (the images of) all
three variables — equivalently, by the irrelevant maximal ideal — as a
`k`-submodule of `A`. -/
def socle (I : Ideal (R3 k)) : Submodule k (R3 k ⧸ I) where
  carrier := {a | ∀ j : Fin 3, Ideal.Quotient.mk I (X j) * a = 0}
  add_mem' := by
    intro a b ha hb j
    rw [mul_add, ha j, hb j, add_zero]
  zero_mem' := fun j => mul_zero _
  smul_mem' := by
    intro c a ha j
    rw [mul_smul_comm, ha j, smul_zero]

/-- **The formal algebraic input of the paper (roadmap item 1)**:
`A = R/I` is a standard graded Artinian level `k`-algebra of embedding
dimension three, socle degree `e`, and type two.  Concretely:

* `I` is homogeneous and proper, so `A = R/I` is a standard graded algebra;
* `I` contains no linear forms — embedding dimension three;
* `A` is finite-dimensional over `k` — Artinian;
* the graded pieces of `A` vanish above degree `e`;
* the socle is contained in the degree-`e` piece (levelness; the reverse
  containment is automatic) and has dimension two — so the socle is
  concentrated in degree exactly `e` (it is nonzero) and `A` has type two. -/
structure IsTypeTwoLevel (I : Ideal (R3 k)) (e : ℕ) : Prop where
  homogeneous : I.IsHomogeneous (homogeneousSubmodule (Fin 3) k)
  proper : I ≠ ⊤
  no_linear_forms : ∀ f ∈ I, MvPolynomial.IsHomogeneous f 1 → f = 0
  finiteDimensional : FiniteDimensional k (R3 k ⧸ I)
  vanish_above : ∀ n : ℕ, e < n → quotPiece I n = ⊥
  socle_concentrated : socle I ≤ quotPiece I e
  type_two : finrank k (socle I) = 2

/-! ### Faithfulness of the formal object

The structure `IsTypeTwoLevel` provably yields the Hilbert-function profile
claimed in the statement of Theorem 1 — `h = (1, 3, h₂, …, h_e = 2)`,
vanishing above the socle degree.  Beyond validating the definition, these
lemmas are the first ones to *consume* the structure fields. -/

/-- If `I` contains no nonzero homogeneous element of degree `n`, the
degree-`n` piece of `A = R/I` has the full dimension `N n`: the quotient
map is injective on `R_n`. -/
lemma finrank_quotPiece_eq (I : Ideal (R3 k)) (n : ℕ)
    (hdisj : ∀ f ∈ I, MvPolynomial.IsHomogeneous f n → f = 0) :
    finrank k (quotPiece I n) = (n + 2).choose 2 := by
  set g : ↥(homogeneousSubmodule (Fin 3) k n) →ₗ[k] R3 k ⧸ I :=
    (Ideal.Quotient.mkₐ k I).toLinearMap.comp
      (homogeneousSubmodule (Fin 3) k n).subtype with hgdef
  have hker : LinearMap.ker g = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hgy := LinearMap.mem_ker.mp hy
    have hy0 : Ideal.Quotient.mk I (y : R3 k) = 0 := by
      simpa [hgdef, Ideal.Quotient.mkₐ_eq_mk] using hgy
    exact Subtype.ext
      (hdisj _ (Ideal.Quotient.eq_zero_iff_mem.mp hy0)
        ((mem_homogeneousSubmodule n _).mp y.2))
  have hrange : LinearMap.range g = quotPiece I n := by
    rw [hgdef, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hcount := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker, finrank_bot] at hcount
  rw [← finrank_homogeneousSubmodule k n]
  omega

/-- `h₀ = 1` for every proper quotient of `R`: a nonzero constant in `I`
would be a unit. -/
lemma hilb_zero (I : Ideal (R3 k)) (hI : I ≠ ⊤) : hilb I 0 = 1 := by
  have hdisj : ∀ f ∈ I, MvPolynomial.IsHomogeneous f 0 → f = 0 := by
    intro f hfI hfhom
    by_contra hf0
    obtain ⟨c, rfl⟩ : ∃ c, f = MvPolynomial.C c :=
      ⟨f.coeff 0, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr hfhom)⟩
    have hc0 : c ≠ 0 := fun hc => hf0 (by rw [hc, map_zero])
    have hmem : MvPolynomial.C c⁻¹ * MvPolynomial.C c ∈ I := I.mul_mem_left _ hfI
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one] at hmem
    exact hI ((Ideal.eq_top_iff_one I).mpr hmem)
  have h := finrank_quotPiece_eq I 0 hdisj
  rw [hilb, if_pos le_rfl, show ((0 : ℤ)).toNat = 0 from rfl, h]
  decide

/-- `h₁ = 3`: embedding dimension three means `I` contains no linear form. -/
lemma IsTypeTwoLevel.hilb_one {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : hilb I 1 = 3 := by
  have h := finrank_quotPiece_eq I 1 hA.no_linear_forms
  rw [hilb, if_pos (by norm_num), show ((1 : ℤ)).toNat = 1 from rfl, h]
  decide

/-- `h₀ = 1`, structure form. -/
lemma IsTypeTwoLevel.hilb_zero {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : hilb I 0 = 1 :=
  LogConcavity.hilb_zero I hA.proper

/-- Multiplication by a variable raises degree by one — the standard-graded
structure of the quotient. -/
lemma quotPiece_X_mul {I : Ideal (R3 k)} (j : Fin 3) {n : ℕ} {a : R3 k ⧸ I}
    (ha : a ∈ quotPiece I n) :
    Ideal.Quotient.mk I (X j) * a ∈ quotPiece I (n + 1) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp ha
  refine Submodule.mem_map.mpr ⟨X j * f, ?_, ?_⟩
  · have hX := (isHomogeneous_X k j).mul ((mem_homogeneousSubmodule n f).mp hf)
    rw [Nat.add_comm] at hX
    exact (mem_homogeneousSubmodule _ _).mpr hX
  · simp [Ideal.Quotient.mkₐ_eq_mk, map_mul]

/-- Levelness upgrade: the socle *equals* the top graded piece (the reverse
containment to `socle_concentrated` is automatic from `vanish_above`). -/
lemma IsTypeTwoLevel.socle_eq {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : socle I = quotPiece I e := by
  refine le_antisymm hA.socle_concentrated fun a ha => ?_
  show ∀ j : Fin 3, Ideal.Quotient.mk I (X j) * a = 0
  intro j
  have hmem := quotPiece_X_mul j ha
  rw [hA.vanish_above (e + 1) (Nat.lt_succ_self e)] at hmem
  simpa using hmem

/-- `h_e = 2`: the top graded piece coincides with the two-dimensional
socle — the "type two" and "socle degree `e`" of the theorem. -/
lemma IsTypeTwoLevel.hilb_top {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : hilb I (e : ℤ) = 2 := by
  rw [hilb, if_pos (Int.natCast_nonneg e), Int.toNat_natCast, ← hA.socle_eq,
    hA.type_two]
  norm_num

/-- A type-two level quotient with embedding dimension three has socle
degree at least two: degree zero has dimension one and degree one has
dimension three, whereas the top piece has dimension two. -/
lemma IsTypeTwoLevel.two_le_socleDegree {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : 2 ≤ e := by
  by_contra he
  have he0 : e = 0 ∨ e = 1 := by omega
  rcases he0 with rfl | rfl
  · have hzero := hA.hilb_zero
    have htop := hA.hilb_top
    norm_num at htop
    rw [hzero] at htop
    norm_num at htop
  · have hone := hA.hilb_one
    have htop := hA.hilb_top
    norm_num at htop
    rw [hone] at htop
    norm_num at htop

/-- `h_t = 0` above the socle degree. -/
lemma IsTypeTwoLevel.hilb_vanish {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) {t : ℤ} (ht : (e : ℤ) < t) : hilb I t = 0 := by
  rw [hilb, if_pos (by omega), hA.vanish_above t.toNat (by omega)]
  simp

variable (k)

/-- **The concrete Gorenstein predicate (roadmap item 11)**: `B` is the
Hilbert function of a standard graded Artinian quotient of `k[x₁,x₂,x₃]`
(so of embedding dimension at most three) whose socle is one-dimensional
and concentrated in degree `E` — a graded Artinian Gorenstein algebra of
socle degree `E`.  This replaces the abstract predicate variable `Gor` of
`theorem1_full`: `hStanley` phrased over this predicate *is* Stanley's
theorem (Lemma 1 of the paper) rather than a statement about an
uninterpreted predicate. -/
def GorensteinQuotientHF (B : ℤ → ℤ) (E : ℤ) : Prop :=
  ∃ (J : Ideal (R3 k)) (E' : ℕ), (E' : ℤ) = E ∧
    J.IsHomogeneous (homogeneousSubmodule (Fin 3) k) ∧
    J ≠ ⊤ ∧
    FiniteDimensional k (R3 k ⧸ J) ∧
    (∀ n : ℕ, E' < n → quotPiece J n = ⊥) ∧
    socle J ≤ quotPiece J E' ∧
    finrank k (socle J) = 1 ∧
    ∀ t : ℤ, B t = hilb J t

variable {k}

/-- The hypothesis `hGor` of `theorem1_full`, now a theorem: the Hilbert
function of a graded quotient of `R` vanishes in negative degrees, is
nonnegative, and is bounded by the Hilbert function of `R`. -/
lemma GorensteinQuotientHF.bounds {B : ℤ → ℤ} {E : ℤ}
    (hgor : GorensteinQuotientHF k B E) :
    (∀ t : ℤ, t < 0 → B t = 0) ∧ (∀ t, 0 ≤ B t) ∧ (∀ t, B t ≤ Nz t) := by
  obtain ⟨J, E', -, -, -, -, -, -, -, hB⟩ := hgor
  refine ⟨fun t ht => ?_, fun t => ?_, fun t => ?_⟩
  · rw [hB t]; exact hilb_neg J ht
  · rw [hB t]; exact hilb_nonneg J t
  · rw [hB t]; exact hilb_le_Nz J t

/-! ## The resolution-to-numerics bridge (roadmap items 2--10)

Mathlib does not yet provide minimal graded free resolutions or graded
Matlis duality.  Accordingly, the one unavoidable input of this section is
`GradedResolutionDuality`: a certificate for the *actual* dualized minimal
resolution, with finite bases, shifts, localized matrices, the full-support
circuit supplied by the last differential, and degreewise exact
presentations.  The Hilbert-series identity is derived from those
presentations by rank–nullity.

Everything after that boundary is derived.  In particular, Betti functions
are cardinalities of shift fibres (not arbitrary integer-valued functions),
the localized ranks `resolutionRank` and `resolutionEpsilon` are finranks of
actual restricted maps, and the hypotheses `hrε`, `h3`, `hε1`, and `hr0`
are theorems.  The critical rank-one branch is represented by the graded
objects occurring in the manuscript; its annihilator quotient and equation
(8) are constructed below rather than supplied as a numerical assertion. -/

section ResolutionBridge

open scoped DirectSum

/-- The degree-`n` vector-space part of an ideal. -/
noncomputable def idealPiece (J : Ideal (R3 k)) (n : ℕ) : Submodule k (R3 k) :=
  homogeneousSubmodule (Fin 3) k n ⊓ J.restrictScalars k

noncomputable instance idealPiece_finiteDimensional
    (J : Ideal (R3 k)) (n : ℕ) : FiniteDimensional k (idealPiece J n) := by
  let f : idealPiece J n →ₗ[k] homogeneousSubmodule (Fin 3) k n :=
    LinearMap.codRestrict (homogeneousSubmodule (Fin 3) k n)
      (idealPiece J n).subtype (fun x => x.2.1)
  exact FiniteDimensional.of_injective f fun x y h =>
    Subtype.ext (congrArg (fun z : homogeneousSubmodule (Fin 3) k n =>
      (z : R3 k)) h)

/-- The Hilbert function of the degree pieces of an ideal, extended by zero
to negative degrees. -/
noncomputable def idealHilb (J : Ideal (R3 k)) (t : ℤ) : ℤ :=
  if 0 ≤ t then (finrank k (idealPiece J t.toNat) : ℤ) else 0

/-- Multiplication of a scalar polynomial by a fixed two-component vector,
viewed as a `k`-linear map. -/
noncomputable def vectorMul (v : Fin 2 → R3 k) :
    R3 k →ₗ[k] (Fin 2 → R3 k) :=
  (LinearMap.toSpanSingleton (R3 k) (Fin 2 → R3 k) v).restrictScalars k

/-- The actual degree-`t` piece of `vJ`, with `v` homogeneous of degree
`a`; negative coefficient degrees give the zero subspace. -/
noncomputable def vJPiece (J : Ideal (R3 k)) (v : Fin 2 → R3 k)
    (a : ℕ) (t : ℤ) : Submodule k (Fin 2 → R3 k) :=
  if 0 ≤ t - (a : ℤ) then
    (idealPiece J (t - (a : ℤ)).toNat).map (vectorMul v)
  else ⊥

/-- Multiplication by a nonzero vector is injective, so the degree piece of
`vJ` has the same dimension as the corresponding degree piece of `J`. -/
lemma finrank_vJPiece (J : Ideal (R3 k)) {v : Fin 2 → R3 k} (hv : v ≠ 0)
    (a : ℕ) (t : ℤ) :
    (finrank k (vJPiece J v a t) : ℤ) = idealHilb J (t - (a : ℤ)) := by
  obtain ⟨z, hz⟩ : ∃ z, v z ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hinj : Function.Injective (vectorMul v) := by
    intro x y hxy
    have hzxy := congrFun hxy z
    simp only [vectorMul, LinearMap.coe_restrictScalars,
      LinearMap.toSpanSingleton_apply, Pi.smul_apply, smul_eq_mul] at hzxy
    exact mul_right_cancel₀ hz hzxy
  by_cases ht : 0 ≤ t - (a : ℤ)
  · rw [vJPiece, if_pos ht, idealHilb, if_pos ht]
    let f := (vectorMul v).domRestrict (idealPiece J (t - (a : ℤ)).toNat)
    have hf : Function.Injective f := hinj.comp Subtype.val_injective
    have hcount := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.ker_eq_bot.mpr hf, finrank_bot, add_zero,
      LinearMap.range_domRestrict] at hcount
    exact_mod_cast hcount
  · rw [vJPiece, if_neg ht, finrank_bot, idealHilb, if_neg ht]
    norm_num

/-- Degreewise rank-nullity for `0 → J → R → R/J → 0`. -/
lemma idealPiece_finrank_add_quotPiece (J : Ideal (R3 k)) (n : ℕ) :
    finrank k (idealPiece J n) + finrank k (quotPiece J n) = (n + 2).choose 2 := by
  let g : ↥(homogeneousSubmodule (Fin 3) k n) →ₗ[k] R3 k ⧸ J :=
    (Ideal.Quotient.mkₐ k J).toLinearMap.comp
      (homogeneousSubmodule (Fin 3) k n).subtype
  let kerEquiv : LinearMap.ker g ≃ₗ[k] idealPiece J n :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, by
          have hxg := LinearMap.mem_ker.mp x.2
          have hx : Ideal.Quotient.mk J x.1.1 = 0 := by
            change Ideal.Quotient.mk J x.1.1 = 0 at hxg
            exact hxg
          exact Ideal.Quotient.eq_zero_iff_mem.mp hx⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
          have hx : Ideal.Quotient.mk J x.1 = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr x.2.2
          apply LinearMap.mem_ker.mpr
          change Ideal.Quotient.mk J x.1 = 0
          exact hx⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrange : LinearMap.range g = quotPiece J n := by
    change LinearMap.range
      ((Ideal.Quotient.mkₐ k J).toLinearMap.comp
        (homogeneousSubmodule (Fin 3) k n).subtype) = quotPiece J n
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hcount := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, kerEquiv.finrank_eq, finrank_homogeneousSubmodule k n] at hcount
  omega

/-- Every ideal and its quotient split the ambient degree dimension. -/
lemma idealHilb_add_hilb (J : Ideal (R3 k)) (t : ℤ) :
    idealHilb J t + hilb J t = Nz t := by
  by_cases ht : 0 ≤ t
  · have h := idealPiece_finrank_add_quotPiece J t.toNat
    rw [idealHilb, if_pos ht, hilb, if_pos ht, Nz, if_pos ht, N]
    exact_mod_cast h
  · rw [idealHilb, if_neg ht, hilb, if_neg ht, Nz, if_neg ht]
    ring

/-- Degreewise membership equivalence of two ideals gives equality of their
actual homogeneous pieces.  This is the final graded step in identifying
`J_j` with `Ann(H)_j`. -/
lemma idealPiece_eq_of_homogeneous_mem_iff
    (J Ann : Ideal (R3 k)) (n : ℕ)
    (h : ∀ f : R3 k, MvPolynomial.IsHomogeneous f n → (f ∈ J ↔ f ∈ Ann)) :
    idealPiece J n = idealPiece Ann n := by
  ext f
  change (MvPolynomial.IsHomogeneous f n ∧ f ∈ J) ↔
    (MvPolynomial.IsHomogeneous f n ∧ f ∈ Ann)
  constructor
  · rintro ⟨hf, hJ⟩
    exact ⟨hf, (h f hf).mp hJ⟩
  · rintro ⟨hf, hAnn⟩
    exact ⟨hf, (h f hf).mpr hAnn⟩

/-- The graded form of the chain used before equation (8).  Once the
low-shift map factors through a nonzero line `Rv`, exactness identifies the
coefficient submodule `J` with the annihilator of `H = ψ(v)` for every
coefficient in the degree range where exactness is known. -/
theorem line_coefficient_eq_annihilator_low
    {R L M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    (φ : L →ₗ[R] (Fin 2 → R)) (ψ : (Fin 2 → R) →ₗ[R] M)
    (v : Fin 2 → R) (hv : v ≠ 0)
    (hline : ∀ x, ∃ c : R, φ x = c • v)
    (Low : R → Prop)
    (hexact : ∀ c, Low c →
      (c • v ∈ LinearMap.ker ψ ↔ c • v ∈ LinearMap.range φ)) :
    ∃ θ : L →ₗ[R] R,
      (∀ x, φ x = θ x • v) ∧
      LinearMap.range φ = (LinearMap.range θ).map
        (LinearMap.toSpanSingleton R (Fin 2 → R) v) ∧
      (∀ c, Low c →
        (c ∈ LinearMap.range θ ↔
          c ∈ LinearMap.ker
            (LinearMap.toSpanSingleton R M (ψ v)))) := by
  obtain ⟨θ, hfactor, hrange, hmem, -⟩ := line_factorization hv φ hline
  refine ⟨θ, hfactor, hrange, fun c hc => ?_⟩
  rw [← hmem c, ← hexact c hc]
  simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, map_smul]

/-- The reindexed Hilbert function of the graded dual. -/
noncomputable def reversedHilb (I : Ideal (R3 k)) (e : ℕ) (t : ℤ) : ℤ :=
  hilb I ((e : ℤ) - t)

/-- The actual vector-space piece `M_d = Hom_k(A_{e-d}, k)` of the graded
dual (for natural `d`). -/
abbrev gradedDualPiece (I : Ideal (R3 k)) (e d : ℕ) :=
  Module.Dual k (quotPiece I (e - d))

/-- Dualization preserves the degreewise dimension, giving
`g_d = h_{e-d}` rather than assuming `hrev`. -/
lemma finrank_gradedDualPiece (I : Ideal (R3 k)) (e d : ℕ) (hd : d ≤ e) :
    (finrank k (gradedDualPiece I e d) : ℤ) = reversedHilb I e (d : ℤ) := by
  rw [Subspace.dual_finrank_eq]
  have heq : (e : ℤ) - (d : ℤ) = ((e - d : ℕ) : ℤ) := by
    exact (Nat.cast_sub hd).symm
  rw [reversedHilb, heq, hilb, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

/-- Multiplicity of a shift in a finite homogeneous basis. -/
noncomputable def shiftMultiplicity {ι : Type*} [Fintype ι]
    (shift : ι → ℤ) (b : ℤ) : ℤ :=
  ((Finset.univ.filter fun i => shift i = b).card : ℤ)

lemma shiftMultiplicity_nonneg {ι : Type*} [Fintype ι]
    (shift : ι → ℤ) (b : ℤ) : 0 ≤ shiftMultiplicity shift b := by
  exact Int.natCast_nonneg _

/-- Summing shift multiplicities over an interval counts the corresponding
basis vectors.  This is the bookkeeping which turns finite shift functions
into the paper's cumulative Betti numbers. -/
lemma sum_shiftMultiplicity_Icc {ι : Type*} [Fintype ι]
    (shift : ι → ℤ) (l u : ℤ) :
    (∑ b ∈ Finset.Icc l u, shiftMultiplicity shift b) =
      ((Finset.univ.filter fun i => l ≤ shift i ∧ shift i ≤ u).card : ℤ) := by
  classical
  unfold shiftMultiplicity
  norm_cast
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- A homogeneous polynomial of degree `m` belongs to every power at most
`m` of the irrelevant ideal.  This is the support-theoretic form of the
fact that all of its monomials have total degree `m`. -/
lemma isHomogeneous_mem_pow_idealOfVars {f : R3 k} {m r : ℕ}
    (hf : MvPolynomial.IsHomogeneous f m) (hrm : r ≤ m) :
    f ∈ MvPolynomial.idealOfVars (Fin 3) k ^ r := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff]
  intro x hx
  have hx0 : f.coeff x ≠ 0 := MvPolynomial.mem_support_iff.mp hx
  have hxdegree := hf hx0
  have hxdegree' : x.degree = m := by
    simpa [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
      using hxdegree
  simpa [hxdegree'] using hrm

/-- A homogeneous polynomial of degree `n` lying in the `(n+1)`st power
of the irrelevant ideal is zero. -/
lemma isHomogeneous_eq_zero_of_mem_succ_pow_idealOfVars {f : R3 k} {n : ℕ}
    (hf : MvPolynomial.IsHomogeneous f n)
    (hmem : f ∈ MvPolynomial.idealOfVars (Fin 3) k ^ (n + 1)) : f = 0 := by
  apply MvPolynomial.ext
  intro x
  by_cases hx : x.degree = n
  · by_contra hcoeff
    have hsupport : x ∈ f.support := MvPolynomial.mem_support_iff.mpr hcoeff
    have hdegree :=
      (MvPolynomial.mem_pow_idealOfVars_iff (n + 1) f).mp hmem x hsupport
    omega
  · have hcoeff : f.coeff x = 0 := by
      by_contra hcoeff
      have hxdegree := hf hcoeff
      have hxdegree' : x.degree = n := by
        simpa [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
          using hxdegree
      exact hx hxdegree'
    simp [hcoeff]

/-- An actual degreewise exact presentation
`0 → k^m² → k^m¹ → k^m⁰ → M → 0`.

The free vector spaces are written with explicit finite bases.  Recording
the maps and exactness, rather than an alternating-dimension equality,
lets rank–nullity derive the Hilbert-series coefficient formula. -/
structure ExactPresentation (k M : Type*) [Field k] [AddCommGroup M] [Module k M]
    (m₂ m₁ m₀ : ℕ) where
  d₂ : (Fin m₂ → k) →ₗ[k] (Fin m₁ → k)
  d₁ : (Fin m₁ → k) →ₗ[k] (Fin m₀ → k)
  d₀ : (Fin m₀ → k) →ₗ[k] M
  d₂_injective : Function.Injective d₂
  exact₂₁ : LinearMap.range d₂ = LinearMap.ker d₁
  exact₁₀ : LinearMap.range d₁ = LinearMap.ker d₀
  d₀_surjective : Function.Surjective d₀

namespace ExactPresentation

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
variable {m₂ m₁ m₀ : ℕ}

/-- Euler characteristic of an exact three-step presentation, proved from
rank–nullity. -/
lemma finrank_add (E : ExactPresentation k M m₂ m₁ m₀) :
    finrank k M + m₁ = m₀ + m₂ := by
  have h₂ := LinearMap.finrank_range_add_finrank_ker E.d₂
  have h₁ := LinearMap.finrank_range_add_finrank_ker E.d₁
  have h₀ := LinearMap.finrank_range_add_finrank_ker E.d₀
  have hker₂ : LinearMap.ker E.d₂ = ⊥ := LinearMap.ker_eq_bot.mpr E.d₂_injective
  have hrange₀ : LinearMap.range E.d₀ = ⊤ :=
    LinearMap.range_eq_top.mpr E.d₀_surjective
  rw [hker₂, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h₂
  rw [← E.exact₂₁] at h₁
  rw [h₂, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h₁
  rw [← E.exact₁₀, hrange₀, finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h₀
  omega

end ExactPresentation

/-- An actual finite-dimensional quotient presentation `k^m → M` whose
kernel is linearly equivalent to `K`. -/
structure SurjectivePresentation (k M K : Type*) [Field k]
    [AddCommGroup M] [Module k M] [AddCommGroup K] [Module k K] (m : ℕ) where
  π : (Fin m → k) →ₗ[k] M
  surjective : Function.Surjective π
  kernelEquiv : LinearMap.ker π ≃ₗ[k] K

namespace SurjectivePresentation

variable {k M K : Type*} [Field k]
variable [AddCommGroup M] [Module k M] [AddCommGroup K] [Module k K]
variable {m : ℕ}

/-- Rank–nullity for the certified quotient presentation. -/
lemma finrank_add (P : SurjectivePresentation k M K m) :
    finrank k M + finrank k K = m := by
  have h := LinearMap.finrank_range_add_finrank_ker P.π
  have hrange : LinearMap.range P.π = ⊤ := LinearMap.range_eq_top.mpr P.surjective
  rw [hrange, finrank_top, P.kernelEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  exact h

end SurjectivePresentation

/-- The data unavailable in Mathlib: the finite homogeneous bases and the
localized matrices of the dual minimal resolution
`0 → R(-e-3) → F₂ → F₁ → R² → M → 0`, together with graded-duality and
Hilbert-series correctness.  The last term of the original resolution is
therefore `R(-e-3)²`; its two basis vectors are the two dual generators.

The matrix fields are over `Frac(R)`, exactly where the manuscript performs
its circuit and rank argument.  Hilbert-series correctness is represented
by actual degreewise exact linear presentations, from which the coefficient
identity is proved below.  The low-degree consequence of the last
differential is likewise proved directly from the homogeneous generators. -/
structure GradedResolutionDuality
    (I : Ideal (R3 k)) (e : ℕ) (β₁ β₂ : Type*) [Fintype β₁] [Fintype β₂] where
  pShift : β₁ → ℤ
  qShift : β₂ → ℤ
  pShift_nonneg : ∀ i, 0 ≤ pShift i
  qShift_nonneg : ∀ j, 0 ≤ qShift j
  degreewise_exact : ∀ n : ℕ, n ≤ e → Nonempty
    (ExactPresentation k (gradedDualPiece I e n)
      (shiftSum ((e : ℤ) + 3) (shiftMultiplicity qShift) (n : ℤ)).toNat
      (shiftSum ((e : ℤ) + 3) (shiftMultiplicity pShift) (n : ℤ)).toNat
      (2 * Nz (n : ℤ)).toNat)
  δ₁ : β₁ → Fin 2 → R3 k
  δ₁_ne_zero : ∀ i, δ₁ i ≠ 0
  δ₁_homogeneous : ∀ i z,
    MvPolynomial.IsHomogeneous (δ₁ i z) (pShift i).toNat
  δ₂K : β₂ → β₁ → FractionRing (R3 k)
  δ₂_graded_zero : ∀ j i, qShift j ≤ pShift i → δ₂K j i = 0
  δ₁δ₂ : ∀ j,
    ∑ i, δ₂K j i •
      (fun z => algebraMap (R3 k) (FractionRing (R3 k)) (δ₁ i z)) = 0
  circuit : β₂ → FractionRing (R3 k)
  circuit_full : ∀ j, circuit j ≠ 0
  circuit_ne_zero : circuit ≠ 0
  circuit_dependency :
    ∑ j, circuit j • δ₂K j = 0
  kernel_line : ∀ c : β₂ → FractionRing (R3 k),
    (∑ j, c j • δ₂K j) = 0 →
      ∃ a : FractionRing (R3 k), c = a • circuit
  idealGenerator : β₂ → R3 k
  idealGenerator_homogeneous : ∀ j,
    MvPolynomial.IsHomogeneous (idealGenerator j)
      (((e : ℤ) + 3 - qShift j).toNat)
  ideal_eq_span_generators : I = Ideal.span (Set.range idealGenerator)
  circuit_eq_generator : ∀ j,
    circuit j = algebraMap (R3 k) (FractionRing (R3 k)) (idealGenerator j)

namespace GradedResolutionDuality

variable {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]
variable {I : Ideal (R3 k)} {e : ℕ}

/-- The actual Betti multiplicities attached to the finite shift bases. -/
noncomputable def p (D : GradedResolutionDuality I e β₁ β₂) : ℤ → ℤ :=
  shiftMultiplicity D.pShift

/-- The actual second Betti multiplicities attached to the finite shift basis. -/
noncomputable def q (D : GradedResolutionDuality I e β₁ β₂) : ℤ → ℤ :=
  shiftMultiplicity D.qShift

/-- The localized second differential, written with its actual finite bases.
The rows are indexed by `β₂`, so its kernel is the coefficient space of
dependencies among the columns appearing in the manuscript. -/
noncomputable def δ₂ (D : GradedResolutionDuality I e β₁ β₂) :
    (β₂ → FractionRing (R3 k)) →ₗ[FractionRing (R3 k)]
      (β₁ → FractionRing (R3 k)) :=
  Fintype.linearCombination (FractionRing (R3 k))
    (fun j i => D.δ₂K j i)

@[simp] lemma δ₂_apply (D : GradedResolutionDuality I e β₁ β₂)
    (c : β₂ → FractionRing (R3 k)) :
    D.δ₂ c = ∑ j, c j • D.δ₂K j := rfl

lemma δ₂_kernel_eq_span_circuit (D : GradedResolutionDuality I e β₁ β₂) :
    LinearMap.ker D.δ₂ =
      Submodule.span (FractionRing (R3 k)) {D.circuit} := by
  apply le_antisymm
  · intro c hc
    obtain ⟨a, ha⟩ := D.kernel_line c (by simpa [δ₂_apply] using hc)
    rw [Submodule.mem_span_singleton]
    exact ⟨a, ha.symm⟩
  · apply Submodule.span_le.mpr
    rintro c rfl
    change D.δ₂ D.circuit = 0
    rw [δ₂_apply]
    simpa using D.circuit_dependency

lemma δ₂_kernel_finrank (D : GradedResolutionDuality I e β₁ β₂) :
    finrank (FractionRing (R3 k)) (LinearMap.ker D.δ₂) = 1 := by
  rw [D.δ₂_kernel_eq_span_circuit]
  simpa using finrank_span_singleton D.circuit_ne_zero

lemma p_nonneg (D : GradedResolutionDuality I e β₁ β₂) (b : ℤ) : 0 ≤ D.p b :=
  shiftMultiplicity_nonneg _ _

lemma q_nonneg (D : GradedResolutionDuality I e β₁ β₂) (b : ℤ) : 0 ≤ D.q b :=
  shiftMultiplicity_nonneg _ _

/-- The Hilbert-series coefficient identity, now derived from the actual
degreewise exact presentations.  Negative degrees vanish by the level
algebra's top-degree bound; nonnegative degrees are Euler characteristics
of the exact presentations. -/
lemma hilbert_series (D : GradedResolutionDuality I e β₁ β₂)
    (hA : IsTypeTwoLevel I e) : ∀ t, t ≤ (e : ℤ) →
    reversedHilb I e t = 2 * Nz t
      - shiftSum ((e : ℤ) + 3) D.p t
      + shiftSum ((e : ℤ) + 3) D.q t
      - Nz (t - ((e : ℤ) + 3)) := by
  intro t hte
  by_cases ht : 0 ≤ t
  · let n := t.toNat
    have hnt : (n : ℤ) = t := Int.toNat_of_nonneg ht
    have hne : n ≤ e := by
      have : (n : ℤ) ≤ (e : ℤ) := hnt.trans_le hte
      exact_mod_cast this
    obtain E := (D.degreewise_exact n hne).some
    have he := E.finrank_add
    have hp0 : 0 ≤ shiftSum ((e : ℤ) + 3) D.p (n : ℤ) :=
      shiftSum_nonneg _ D.p_nonneg _
    have hq0 : 0 ≤ shiftSum ((e : ℤ) + 3) D.q (n : ℤ) :=
      shiftSum_nonneg _ D.q_nonneg _
    have hN0 : 0 ≤ 2 * Nz (n : ℤ) := mul_nonneg (by norm_num) (Nz_nonneg _)
    have heZ :
        (finrank k (gradedDualPiece I e n) : ℤ) +
            (shiftSum ((e : ℤ) + 3) D.p (n : ℤ)).toNat =
          (2 * Nz (n : ℤ)).toNat +
            (shiftSum ((e : ℤ) + 3) D.q (n : ℤ)).toNat := by
      exact_mod_cast he
    rw [Int.toNat_of_nonneg hp0, Int.toNat_of_nonneg hq0,
      Int.toNat_of_nonneg hN0] at heZ
    have hfin := finrank_gradedDualPiece I e n hne
    have hlast : Nz ((n : ℤ) - ((e : ℤ) + 3)) = 0 :=
      Nz_neg _ (by omega)
    rw [← hnt, hlast]
    linarith
  · have hrev0 : reversedHilb I e t = 0 := by
      rw [reversedHilb]
      exact hA.hilb_vanish (by omega)
    have hp0 : shiftSum ((e : ℤ) + 3) D.p t = 0 := by
      apply shiftSum_vanish
      intro b hb hbt
      omega
    have hq0 : shiftSum ((e : ℤ) + 3) D.q t = 0 := by
      apply shiftSum_vanish
      intro b hb hbt
      omega
    rw [hrev0, hp0, hq0, Nz_neg t (by omega),
      Nz_neg (t - ((e : ℤ) + 3)) (by omega)]
    ring

/-- Properness of `I` forces every last-differential generator degree
`e+3-qShift j` to be nonnegative.  Otherwise its certified degree is zero;
full support makes it a nonzero constant, hence a unit in `I`. -/
lemma qShift_le_of_proper (D : GradedResolutionDuality I e β₁ β₂)
    (hI : I ≠ ⊤) (j : β₂) : D.qShift j ≤ (e : ℤ) + 3 := by
  by_contra hshift
  have hdegree : ((e : ℤ) + 3 - D.qShift j).toNat = 0 := by
    rw [Int.toNat_eq_zero]
    omega
  have hhom : MvPolynomial.IsHomogeneous (D.idealGenerator j) 0 := by
    simpa [hdegree] using D.idealGenerator_homogeneous j
  have hgen0 : D.idealGenerator j ≠ 0 := by
    intro hzero
    have hfull := D.circuit_full j
    rw [D.circuit_eq_generator j, hzero, map_zero] at hfull
    exact hfull rfl
  obtain ⟨c, hc⟩ : ∃ c : k, D.idealGenerator j = MvPolynomial.C c :=
    ⟨(D.idealGenerator j).coeff 0,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr hhom)⟩
  have hc0 : c ≠ 0 := by
    intro hczero
    apply hgen0
    rw [hc, hczero, map_zero]
  have hgenI : D.idealGenerator j ∈ I := by
    have hle : Ideal.span (Set.range D.idealGenerator) ≤ I :=
      le_of_eq D.ideal_eq_span_generators.symm
    exact hle (Ideal.subset_span ⟨j, rfl⟩)
  have hone : (1 : R3 k) ∈ I := by
    have hmul := I.mul_mem_left (MvPolynomial.C c⁻¹) hgenI
    rw [hc, ← map_mul, inv_mul_cancel₀ hc0, map_one] at hmul
    exact hmul
  exact hI ((Ideal.eq_top_iff_one I).mpr hone)

/-- The coordinates of the last differential generate `I` in their
certified homogeneous degrees.  Consequently `I` contains no nonzero
homogeneous polynomial below all of those degrees.  This used to be a field
of `GradedResolutionDuality`; it is derivable from its generator data. -/
lemma ideal_no_low_degree (D : GradedResolutionDuality I e β₁ β₂) (n : ℕ)
    (hI : I ≠ ⊤) (hn : ∀ j, (n : ℤ) < (e : ℤ) + 3 - D.qShift j) :
    ∀ f ∈ I, MvPolynomial.IsHomogeneous f n → f = 0 := by
  intro f hfI hhom
  have hspan : Ideal.span (Set.range D.idealGenerator) ≤
      MvPolynomial.idealOfVars (Fin 3) k ^ (n + 1) := by
    rw [Ideal.span_le]
    rintro g ⟨j, rfl⟩
    apply isHomogeneous_mem_pow_idealOfVars (D.idealGenerator_homogeneous j)
    have hnonneg : 0 ≤ (e : ℤ) + 3 - D.qShift j := by
      have hq := D.qShift_le_of_proper hI j
      omega
    have hcast : (((e : ℤ) + 3 - D.qShift j).toNat : ℤ) =
        (e : ℤ) + 3 - D.qShift j := Int.toNat_of_nonneg hnonneg
    have hlt := hn j
    have hle : (n : ℤ) + 1 ≤
        (((e : ℤ) + 3 - D.qShift j).toNat : ℤ) := by
      rw [hcast]
      omega
    exact_mod_cast hle
  apply isHomogeneous_eq_zero_of_mem_succ_pow_idealOfVars hhom
  apply hspan
  rw [← D.ideal_eq_span_generators]
  exact hfI

/-- Indices of `F₁` with shift strictly below `d`. -/
abbrev LowP (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :=
  {i : β₁ // D.pShift i < d}

/-- Indices of `F₂` with shift at most `d`. -/
abbrev LowQ (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :=
  {j : β₂ // D.qShift j ≤ d}

/-- The localized low-shift part of `δ₂`. -/
noncomputable def lowδ₂ (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    (D.LowQ d → FractionRing (R3 k)) →ₗ[FractionRing (R3 k)]
      (D.LowP d → FractionRing (R3 k)) :=
  Fintype.linearCombination (FractionRing (R3 k))
    (fun j i => D.δ₂K j.1 i.1)

/-- The localized restriction of `δ₁` to rows of shift below `d`. -/
noncomputable def lowδ₁ (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    (D.LowP d → FractionRing (R3 k)) →ₗ[FractionRing (R3 k)]
      (Fin 2 → FractionRing (R3 k)) :=
  Fintype.linearCombination (FractionRing (R3 k))
    (fun i z => algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i.1 z))

/-- `ε_d` is no longer arbitrary: it is the nullity of the low part of
the localized second differential. -/
noncomputable def resolutionEpsilon
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) : ℤ :=
  (finrank (FractionRing (R3 k)) (LinearMap.ker (D.lowδ₂ d)) : ℤ)

/-- `r_d` is no longer arbitrary: it is the rank of the localized first
differential restricted to shifts below `d`. -/
noncomputable def resolutionRank
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) : ℤ :=
  (finrank (FractionRing (R3 k)) (LinearMap.range (D.lowδ₁ d)) : ℤ)

/-- The restricted localized maps still form a complex.  This is where the
graded zero pattern is used: a column of shift at most `d` has zero entries
in rows of shift at least `d`. -/
lemma low_complex (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    D.lowδ₁ d ∘ₗ D.lowδ₂ d = 0 := by
  classical
  apply LinearMap.ext
  intro x
  ext z
  simp only [LinearMap.comp_apply, lowδ₁, lowδ₂,
    Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, Pi.zero_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  suffices hinner :
      (∑ i : D.LowP d,
          D.δ₂K j.1 i.1 *
            algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i.1 z)) = 0 by
    rw [hinner, mul_zero]
  let term : β₁ → FractionRing (R3 k) := fun i =>
    D.δ₂K j.1 i * algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i z)
  have hhigh : (∑ i : {i : β₁ // ¬ D.pShift i < d}, term i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    unfold term
    rw [D.δ₂_graded_zero j.1 i.1 (by omega), zero_mul]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : β₁ => D.pShift i < d) term
  have hfull : (∑ i : β₁, term i) = 0 := by
    have hc := congrFun (D.δ₁δ₂ j.1) z
    simpa [term, Pi.smul_apply, smul_eq_mul] using hc
  have hlow : (∑ i : D.LowP d, term i.1) = 0 := by
    rw [hhigh, add_zero] at hsplit
    exact hsplit.trans hfull
  exact hlow

lemma q_cumulative (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    (∑ b ∈ Finset.Icc (0 : ℤ) d, D.q b) =
      (Fintype.card (D.LowQ d) : ℤ) := by
  classical
  rw [q, sum_shiftMultiplicity_Icc]
  norm_cast
  rw [Fintype.card_subtype]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨D.qShift_nonneg j, h⟩

lemma p_cumulative (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), D.p b) =
      (Fintype.card (D.LowP d) : ℤ) := by
  classical
  rw [p, sum_shiftMultiplicity_Icc]
  norm_cast
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · omega
  · intro h
    exact ⟨D.pShift_nonneg i, by omega⟩

/-- A dependency among the projected low-shift columns extends by zero to
a dependency among all columns.  The full-support circuit therefore still
controls the restricted kernel. -/
lemma lowδ₂_kernel_line (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ)
    (x : D.LowQ d → FractionRing (R3 k))
    (hx : x ∈ LinearMap.ker (D.lowδ₂ d)) :
    ∃ a : FractionRing (R3 k),
      x = a • (fun j : D.LowQ d => D.circuit j.1) := by
  classical
  let X : β₂ → FractionRing (R3 k) := fun j =>
    if h : D.qShift j ≤ d then x ⟨j, h⟩ else 0
  have hglobal : (∑ j, X j • D.δ₂K j) = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hi : D.pShift i < d
    · have hxi := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
      simp only [lowδ₂, Fintype.linearCombination_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hxi
      let s : Finset β₂ := Finset.univ.filter fun j => D.qShift j ≤ d
      calc
        (∑ j : β₂, X j * D.δ₂K j i)
            = ∑ j ∈ s, X j * D.δ₂K j i := by
                symm
                apply Finset.sum_subset (Finset.subset_univ s)
                intro j _ hj
                have hj' : ¬ D.qShift j ≤ d := by simpa [s] using hj
                rw [show X j = 0 by simp [X, hj'], zero_mul]
        _ = ∑ j : s, X j.1 * D.δ₂K j.1 i :=
              (Finset.sum_coe_sort s fun j => X j * D.δ₂K j i).symm
        _ = ∑ j : D.LowQ d, x j * D.δ₂K j.1 i := by
              let equiv : s ≃ D.LowQ d :=
                Equiv.subtypeEquivRight (by simp [s])
              exact Fintype.sum_equiv equiv _ _ (fun j => by
                have hjmem := j.2
                change j.1 ∈ Finset.univ.filter (fun z => D.qShift z ≤ d) at hjmem
                have hj : D.qShift j.1 ≤ d := (Finset.mem_filter.mp hjmem).2
                have heq : equiv j = (⟨j.1, hj⟩ : D.LowQ d) := Subtype.ext rfl
                rw [heq]
                simp [X, hj])
        _ = 0 := hxi
    · apply Finset.sum_eq_zero
      intro j _
      unfold X
      split
      next hj =>
        rw [D.δ₂_graded_zero j i (by omega), mul_zero]
      next => rw [zero_mul]
  obtain ⟨a, ha⟩ := D.kernel_line X hglobal
  refine ⟨a, funext fun j => ?_⟩
  have hj := congrFun ha j.1
  simpa [X, j.2, Pi.smul_apply, smul_eq_mul] using hj

/-- The full-support circuit proves `ε_d ≤ 1`. -/
lemma resolutionEpsilon_le_one
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    finrank (FractionRing (R3 k)) (LinearMap.ker (D.lowδ₂ d)) ≤ 1 := by
  let c : D.LowQ d → FractionRing (R3 k) := fun j => D.circuit j.1
  have hle : LinearMap.ker (D.lowδ₂ d) ≤
      Submodule.span (FractionRing (R3 k)) {c} := by
    intro x hx
    obtain ⟨a, ha⟩ := D.lowδ₂_kernel_line d x hx
    rw [Submodule.mem_span_singleton]
    exact ⟨a, ha.symm⟩
  exact (Submodule.finrank_mono hle).trans (by
    simpa using finrank_span_le_card (R := FractionRing (R3 k)) ({c} : Set _))

/-- The rank data now have exactly the finite alternatives asserted in the
paper: the target has dimension two, and the circuit kernel has dimension
at most one. -/
lemma rank_epsilon_cases (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    (D.resolutionRank d = 0 ∨ D.resolutionRank d = 1 ∨
      D.resolutionRank d = 2) ∧
    (D.resolutionEpsilon d = 0 ∨ D.resolutionEpsilon d = 1) := by
  have hrle : finrank (FractionRing (R3 k)) (LinearMap.range (D.lowδ₁ d)) ≤ 2 := by
    calc
      _ ≤ finrank (FractionRing (R3 k)) (Fin 2 → FractionRing (R3 k)) :=
        Submodule.finrank_le _
      _ = 2 := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hεle := D.resolutionEpsilon_le_one d
  unfold resolutionRank resolutionEpsilon
  omega

/-- Paper (3), with every term interpreted as the dimension/rank of its
actual localized restricted map. -/
lemma rank_inequality (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    (∑ b ∈ Finset.Icc (0 : ℤ) d, D.q b) - D.resolutionEpsilon d ≤
      (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), D.p b) - D.resolutionRank d := by
  have h := rank_estimate (D.lowδ₂ d) (D.lowδ₁ d) (D.low_complex d)
    (ε := finrank (FractionRing (R3 k)) (LinearMap.ker (D.lowδ₂ d))) le_rfl
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  rw [D.q_cumulative d, D.p_cumulative d]
  unfold resolutionEpsilon resolutionRank
  omega

/-- If one `F₂` column is omitted from the low-shift block, the restricted
kernel is zero: extending a dependency by zero and evaluating the
full-support circuit at the omitted coordinate kills its scalar. -/
lemma lowδ₂_ker_eq_bot_of_omitted
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ)
    (j₀ : β₂) (hj₀ : ¬ D.qShift j₀ ≤ d) :
    LinearMap.ker (D.lowδ₂ d) = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  intro x hx
  let X : β₂ → FractionRing (R3 k) := fun j =>
    if h : D.qShift j ≤ d then x ⟨j, h⟩ else 0
  have hglobal : (∑ j, X j • D.δ₂K j) = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hi : D.pShift i < d
    · have hxi := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
      simp only [lowδ₂, Fintype.linearCombination_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hxi
      let s : Finset β₂ := Finset.univ.filter fun j => D.qShift j ≤ d
      calc
        (∑ j : β₂, X j * D.δ₂K j i)
            = ∑ j ∈ s, X j * D.δ₂K j i := by
                symm
                apply Finset.sum_subset (Finset.subset_univ s)
                intro j _ hj
                have hj' : ¬ D.qShift j ≤ d := by simpa [s] using hj
                rw [show X j = 0 by simp [X, hj'], zero_mul]
        _ = ∑ j : s, X j.1 * D.δ₂K j.1 i :=
              (Finset.sum_coe_sort s fun j => X j * D.δ₂K j i).symm
        _ = ∑ j : D.LowQ d, x j * D.δ₂K j.1 i := by
              let equiv : s ≃ D.LowQ d :=
                Equiv.subtypeEquivRight (by simp [s])
              exact Fintype.sum_equiv equiv _ _ (fun j => by
                have hjmem := j.2
                change j.1 ∈ Finset.univ.filter (fun z => D.qShift z ≤ d) at hjmem
                have hj : D.qShift j.1 ≤ d := (Finset.mem_filter.mp hjmem).2
                have heq : equiv j = (⟨j.1, hj⟩ : D.LowQ d) := Subtype.ext rfl
                rw [heq]
                simp [X, hj])
        _ = 0 := hxi
    · apply Finset.sum_eq_zero
      intro j _
      unfold X
      split
      next hj => rw [D.δ₂_graded_zero j i (by omega), mul_zero]
      next => rw [zero_mul]
  obtain ⟨a, ha⟩ := D.kernel_line X hglobal
  have ha0 : a = 0 := by
    have hj := congrFun ha j₀
    have hX0 : X j₀ = 0 := by simp [X, hj₀]
    rw [hX0] at hj
    simp only [Pi.smul_apply, smul_eq_mul] at hj
    exact (mul_eq_zero.mp hj.symm).resolve_right (D.circuit_full j₀)
  funext j
  have hj := congrFun ha j.1
  simpa [X, j.2, ha0, Pi.smul_apply, smul_eq_mul] using hj

/-- `ε_d = 1` forces every `F₂` shift to be at most `d`. -/
lemma all_qShift_le_of_epsilon_one
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ)
    (hε : D.resolutionEpsilon d = 1) : ∀ j, D.qShift j ≤ d := by
  intro j
  by_contra hj
  have hker := D.lowδ₂_ker_eq_bot_of_omitted d j hj
  have hfin : finrank (FractionRing (R3 k)) (LinearMap.ker (D.lowδ₂ d)) = 0 := by
    rw [hker, finrank_bot]
  unfold resolutionEpsilon at hε
  omega

/-- The paper's `ε_d = 1` binomial window, now derived from the shifts of
the last differential and the fact that its coordinates generate `I`. -/
lemma epsilon_one_full_hilbert
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ)
    (hI : I ≠ ⊤)
    (hε : D.resolutionEpsilon d = 1) :
    ∀ t, t < (e : ℤ) + 3 - d → hilb I t = Nz t := by
  have hall := D.all_qShift_le_of_epsilon_one d hε
  intro t ht
  by_cases ht0 : 0 ≤ t
  · have hdisj : ∀ f ∈ I,
        MvPolynomial.IsHomogeneous f t.toNat → f = 0 := by
      apply D.ideal_no_low_degree t.toNat hI
      intro j
      have htn : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
      have hj := hall j
      rw [htn]
      omega
    have hdim := finrank_quotPiece_eq I t.toNat hdisj
    rw [hilb, if_pos ht0, Nz, if_pos ht0, hdim, N]
  · rw [hilb_neg I (by omega), Nz_neg t (by omega)]

/-- A rank-zero restricted first differential has no low-shift basis
vectors, because minimality makes every column nonzero. -/
lemma rank_zero_no_low_shifts
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ)
    (hr : D.resolutionRank d = 0) :
    ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), D.p b = 0 := by
  classical
  have hr0 : finrank (FractionRing (R3 k))
      (LinearMap.range (D.lowδ₁ d)) = 0 := by
    unfold resolutionRank at hr
    omega
  have hrange : LinearMap.range (D.lowδ₁ d) = ⊥ :=
    Submodule.finrank_eq_zero.mp hr0
  have hempty : IsEmpty (D.LowP d) := by
    refine ⟨fun i => ?_⟩
    have hcol : (fun z =>
        algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i.1 z)) = 0 := by
      have hmem : D.lowδ₁ d (Pi.single i 1) ∈ LinearMap.range (D.lowδ₁ d) :=
        ⟨Pi.single i 1, rfl⟩
      rw [hrange] at hmem
      have hz : D.lowδ₁ d (Pi.single i 1) = 0 := by simpa using hmem
      simpa [lowδ₁, Fintype.linearCombination_apply_single] using hz
    apply D.δ₁_ne_zero i.1
    funext z
    apply IsFractionRing.injective (R3 k) (FractionRing (R3 k))
    simpa using congrFun hcol z
  rw [D.p_cumulative d]
  norm_cast
  exact Fintype.card_eq_zero

/-- The quotient by the unit ideal has the zero Hilbert function (the
`H = 0` alternative in the manuscript). -/
lemma hilb_top_ideal (t : ℤ) : hilb (⊤ : Ideal (R3 k)) t = 0 := by
  rw [hilb]
  split
  next ht =>
    have hpiece : quotPiece (⊤ : Ideal (R3 k)) t.toNat = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x _
      exact Subsingleton.elim x 0
    rw [hpiece, finrank_bot]
    norm_num
  next => rfl

/-- The graded algebra data proving that an annihilator quotient is an
actual codimension-at-most-three Artinian Gorenstein quotient. -/
structure GorensteinAnnihilatorData (Ann : Ideal (R3 k)) (E : ℕ) : Prop where
  homogeneous : Ann.IsHomogeneous (homogeneousSubmodule (Fin 3) k)
  proper : Ann ≠ ⊤
  finiteDimensional : FiniteDimensional k (R3 k ⧸ Ann)
  vanish_above : ∀ n : ℕ, E < n → quotPiece Ann n = ⊥
  socle_concentrated : socle Ann ≤ quotPiece Ann E
  socle_one : finrank k (socle Ann) = 1

lemma GorensteinAnnihilatorData.toGorensteinQuotientHF
    {Ann : Ideal (R3 k)} {E : ℕ} (h : GorensteinAnnihilatorData Ann E) :
    GorensteinQuotientHF k (hilb Ann) (E : ℤ) := by
  exact ⟨Ann, E, rfl, h.homogeneous, h.proper, h.finiteDimensional,
    h.vanish_above, h.socle_concentrated, h.socle_one, fun _ => rfl⟩

/-- The graded output of the primitive-vector argument in the critical
rank-one branch.  Unlike the old `hr1`, this contains the actual primitive
homogeneous vector, coefficient ideal `J`, annihilator ideal, equality of
their low-degree pieces (equation (7) plus cancellation by `v`), and the
degreewise kernel dimension.  Equation (8) is *not* a field; it is derived
below by rank-nullity for `Ann ⊂ R`.

The alternative `Ann = ⊤` is exactly `H = 0`.  Otherwise the second branch
records the graded bookkeeping obtained from the cyclic-simple-socle
theorem, making `R/Ann` an actual Gorenstein quotient of socle degree
`e-a`. -/
structure CriticalBranchCertificate
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) where
  two_le_d : 2 ≤ d
  d_le_e : d ≤ (e : ℤ)
  a : ℕ
  a_lt_d : (a : ℤ) < d
  v : Fin 2 → R3 k
  v_primitive : IsRelPrime (v 0) (v 1)
  v_homogeneous : ∀ z, MvPolynomial.IsHomogeneous (v z) a
  J : Ideal (R3 k)
  J_homogeneous : J.IsHomogeneous (homogeneousSubmodule (Fin 3) k)
  Ann : Ideal (R3 k)
  low_mem_iff : ∀ n : ℕ, (n : ℤ) ≤ d - (a : ℤ) →
    ∀ f : R3 k, MvPolynomial.IsHomogeneous f n → (f ∈ J ↔ f ∈ Ann)
  kernelPiece : ℤ → Submodule k (Fin 2 → R3 k)
  equation7 : ∀ t : ℤ, t ≤ d → kernelPiece t = vJPiece J v a t
  presentation_exact : ∀ t : ℤ, d - 2 ≤ t → t ≤ d → Nonempty
    (SurjectivePresentation k (gradedDualPiece I e t.toNat) (kernelPiece t)
      (2 * Nz t).toNat)
  annihilator_case : Ann = ⊤ ∨ GorensteinAnnihilatorData Ann (e - a)

namespace CriticalBranchCertificate

variable {D : GradedResolutionDuality I e β₁ β₂} {d : ℤ}

lemma a_le_e (C : CriticalBranchCertificate D d) : C.a ≤ e := by
  have : (C.a : ℤ) ≤ (e : ℤ) := by
    have ha := C.a_lt_d
    have hde := C.d_le_e
    omega
  exact_mod_cast this

lemma v_ne_zero (C : CriticalBranchCertificate D d) : C.v ≠ 0 := by
  intro hv
  rcases C.v_primitive.ne_zero_or_ne_zero with h0 | h1
  · exact h0 (congrFun hv 0)
  · exact h1 (congrFun hv 1)

/-- The low-degree ideal-piece equality, derived from the homogeneous
membership equivalence supplied by the truncated exactness argument. -/
lemma low_piece_eq (C : CriticalBranchCertificate D d) (n : ℕ)
    (hn : (n : ℤ) ≤ d - (C.a : ℤ)) :
    idealPiece C.J n = idealPiece C.Ann n :=
  idealPiece_eq_of_homogeneous_mem_iff C.J C.Ann n (C.low_mem_iff n hn)

/-- The presentation-dimension formula used in equation (7), derived from
the actual surjective presentation and its certified kernel. -/
lemma presentation_dimension (C : CriticalBranchCertificate D d) :
    ∀ t : ℤ, d - 2 ≤ t → t ≤ d →
      reversedHilb I e t = 2 * Nz t - (finrank k (C.kernelPiece t) : ℤ) := by
  intro t hdt htd
  have ht0 : 0 ≤ t := by
    have hd := C.two_le_d
    omega
  have hte : t.toNat ≤ e := by
    have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
    have : (t.toNat : ℤ) ≤ (e : ℤ) := by
      have hde := C.d_le_e
      omega
    exact_mod_cast this
  obtain P := (C.presentation_exact t hdt htd).some
  have h := P.finrank_add
  have hnonneg : 0 ≤ 2 * Nz t := mul_nonneg (by norm_num) (Nz_nonneg _)
  have hZ :
      (finrank k (gradedDualPiece I e t.toNat) : ℤ) +
          (finrank k (C.kernelPiece t) : ℤ) =
        ((2 * Nz t).toNat : ℤ) := by
    exact_mod_cast h
  rw [Int.toNat_of_nonneg hnonneg] at hZ
  have hfin := finrank_gradedDualPiece I e t.toNat hte
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
  rw [htcast] at hfin
  linarith

lemma idealHilb_eq_annihilator
    (C : CriticalBranchCertificate D d) {z : ℤ}
    (hz : z ≤ d - (C.a : ℤ)) : idealHilb C.J z = idealHilb C.Ann z := by
  by_cases hz0 : 0 ≤ z
  · rw [idealHilb, if_pos hz0, idealHilb, if_pos hz0,
      C.low_piece_eq z.toNat (by rw [Int.toNat_of_nonneg hz0]; exact hz)]
  · rw [idealHilb, if_neg hz0, idealHilb, if_neg hz0]

/-- The dimension form of equation (7), obtained from the actual equality
of graded kernel and `vJ` pieces. -/
lemma kernel_dimension (C : CriticalBranchCertificate D d) :
    ∀ t : ℤ, d - 2 ≤ t → t ≤ d →
      reversedHilb I e t = 2 * Nz t - idealHilb C.J (t - (C.a : ℤ)) := by
  intro t hdt htd
  have h := C.presentation_dimension t hdt htd
  rw [C.equation7 t htd, finrank_vJPiece C.J C.v_ne_zero C.a t] at h
  exact h

/-- Equation (8), obtained from the actual ideals. -/
lemma equation8 (C : CriticalBranchCertificate D d) :
    ∀ t : ℤ, d - 2 ≤ t → t ≤ d →
      reversedHilb I e t = 2 * Nz t - Nz (t - (C.a : ℤ)) +
        hilb C.Ann (t - (C.a : ℤ)) := by
  intro t hdt htd
  have hker := C.kernel_dimension t hdt htd
  have heq := C.idealHilb_eq_annihilator (z := t - (C.a : ℤ)) (by omega)
  have hdim := idealHilb_add_hilb C.Ann (t - (C.a : ℤ))
  linarith

/-- The old critical numerical hypothesis `hr1`, derived from the graded
primitive/annihilator certificate. -/
lemma to_hr1 (C : CriticalBranchCertificate D d) :
    ∃ (a : ℤ) (B : ℤ → ℤ), 0 ≤ a ∧ a < d ∧
      ((∀ t, B t = 0) ∨ GorensteinQuotientHF k B ((e : ℤ) - a)) ∧
      (∀ t, d - 2 ≤ t → t ≤ d →
        reversedHilb I e t = 2 * Nz t - Nz (t - a) + B (t - a)) := by
  refine ⟨(C.a : ℤ), hilb C.Ann, Int.natCast_nonneg _, C.a_lt_d, ?_, ?_⟩
  · rcases C.annihilator_case with htop | hgor
    · left
      intro t
      rw [htop]
      exact hilb_top_ideal t
    · right
      have hg := hgor.toGorensteinQuotientHF
      simpa [Nat.cast_sub C.a_le_e] using hg
  · exact C.equation8

end CriticalBranchCertificate

/-- A single completion object over the unavailable resolution/duality
certificate.  Its critical-branch method returns the graded construction
above only in the branch where the paper needs it. -/
structure ResolutionPackage
    (D : GradedResolutionDuality I e β₁ β₂) : Prop where
  critical : ∀ d : ℤ, 2 ≤ d → d ≤ (e : ℤ) →
    D.resolutionRank d = 1 → D.p d = 0 →
    reversedHilb I e d - 2 * reversedHilb I e (d - 1) +
      reversedHilb I e (d - 2) = 1 →
    Nonempty (CriticalBranchCertificate D d)

end GradedResolutionDuality

end ResolutionBridge

/-- The exact remaining resolution-theoretic existence proposition, with
finite bases normalized to `Fin` types.  A complete formalization modulo
Stanley would prove

`IsTypeTwoLevel I e → HasGradedResolutionPackage I e`.

Naming the boundary prevents the structural construction from being
confused with any of the numerical hypotheses already discharged. -/
def HasGradedResolutionPackage (I : Ideal (R3 k)) (e : ℕ) : Prop :=
  ∃ (n₁ n₂ : ℕ) (D : GradedResolutionDuality I e (Fin n₁) (Fin n₂)),
    D.ResolutionPackage

/-- **End-to-end theorem modulo the resolution/duality existence theorem and
Stanley.**  Starting from the actual type-two level algebra, a single
`GradedResolutionDuality`/`ResolutionPackage` pair constructs every former
hypothesis of `theorem1_full`: `hrev`, `hres`, the Betti nonnegativity,
`hrε`, (3), both shift-specific consequences, the primitive/annihilator
branch, equation (8), and the Gorenstein bounds.  The only published result
left as a hypothesis is Stanley's monotonicity theorem.

The existence of `D` is precisely the block which cannot currently be
derived inside Mathlib because minimal graded free resolutions and graded
Matlis duality are absent. -/
theorem theorem1_of_resolution
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]
    (D : GradedResolutionDuality I e β₁ β₂)
    (P : D.ResolutionPackage)
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 := by
  apply theorem1_full (e : ℤ) (hilb I) (reversedHilb I e) D.p D.q
    D.resolutionRank D.resolutionEpsilon (GorensteinQuotientHF k)
    (hilb_nonneg I) (hilb_le_Nz I) (fun _ => rfl) D.p_nonneg D.q_nonneg
    (D.hilbert_series hA)
  · intro d _ _
    exact D.rank_epsilon_cases d
  · intro d _ _
    exact D.rank_inequality d
  · intro d _ _ hε
    exact D.epsilon_one_full_hilbert d hA.proper hε
  · intro d _ _ hr
    exact D.rank_zero_no_low_shifts d hr
  · intro d hd hde hr hp hΔ
    exact (P.critical d hd hde hr hp hΔ).some.to_hr1
  · intro B E hB
    exact hB.bounds
  · exact hStanley

/-- The end-to-end result with the entire non-Stanley boundary bundled as
the single named existence proposition `HasGradedResolutionPackage`. -/
theorem theorem1_of_hasGradedResolutionPackage
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (hResolution : HasGradedResolutionPackage I e)
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 := by
  obtain ⟨n₁, n₂, D, P⟩ := hResolution
  exact theorem1_of_resolution e I hA D P hStanley

set_option linter.unusedVariables false in
/-- **Theorem 1 from the formal algebra.**  Log-concavity of the Hilbert
function of a formally defined codimension-three, type-two level algebra
`A = R/I` (`hA : IsTypeTwoLevel I e`).

Compared with `theorem1_full`, the hypotheses `hnn`, `hquot`, and `hGor`
are *derived* from the formal algebra (`hilb_nonneg`, `hilb_le_Nz`,
`GorensteinQuotientHF.bounds`), and the abstract predicate `Gor` is
instantiated at the concrete `GorensteinQuotientHF`.  The remaining
hypotheses — `hrev`/`hres` (graded Matlis duality and the dual minimal
resolution, roadmap items 2–3), `hrε`/`h3` (the rank data over `Frac R`,
item 4), `hε1`/`hr0` (the shift-specific consequences, item 5), `hr1`
(the primitive-vector/cyclic-Gorenstein construction and equation (8),
items 6–10) — are now propositions about the concrete Hilbert function
`hilb I` of `A`, i.e. precisely specified open lemmas; `hStanley` is
Stanley's theorem (item 12), the sole imported published result.

The structural hypothesis `hA` is not yet consumed by the numerical
skeleton below; it anchors the statement and is the input from which
items 2–10 will discharge the remaining hypotheses. -/
theorem theorem1_of_level
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (g p q r ε : ℤ → ℤ)
    (hrev : ∀ t, g t = hilb I ((e : ℤ) - t))
    (hp0 : ∀ b, 0 ≤ p b) (hq0 : ∀ b, 0 ≤ q b)
    (hres : ∀ t, t ≤ (e : ℤ) →
      g t = 2 * Nz t - shiftSum ((e : ℤ) + 3) p t + shiftSum ((e : ℤ) + 3) q t
              - Nz (t - ((e : ℤ) + 3)))
    (hrε : ∀ d, 2 ≤ d → d ≤ (e : ℤ) →
      (r d = 0 ∨ r d = 1 ∨ r d = 2) ∧ (ε d = 0 ∨ ε d = 1))
    (h3 : ∀ d, 2 ≤ d → d ≤ (e : ℤ) →
      (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) - ε d
        ≤ (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b) - r d)
    (hε1 : ∀ d, 2 ≤ d → d ≤ (e : ℤ) → ε d = 1 →
      ∀ t, t < (e : ℤ) + 3 - d → hilb I t = Nz t)
    (hr0 : ∀ d, 2 ≤ d → d ≤ (e : ℤ) → r d = 0 →
      ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b = 0)
    (hr1 : ∀ d, 2 ≤ d → d ≤ (e : ℤ) → r d = 1 → p d = 0 →
      g d - 2 * g (d - 1) + g (d - 2) = 1 →
      ∃ (a : ℤ) (B : ℤ → ℤ), 0 ≤ a ∧ a < d ∧
        ((∀ t, B t = 0) ∨ GorensteinQuotientHF k B ((e : ℤ) - a)) ∧
        (∀ t, d - 2 ≤ t → t ≤ d → g t = 2 * Nz t - Nz (t - a) + B (t - a)))
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 :=
  theorem1_full (e : ℤ) (hilb I) g p q r ε (GorensteinQuotientHF k)
    (hilb_nonneg I) (hilb_le_Nz I) hrev hp0 hq0 hres hrε h3 hε1 hr0 hr1
    (fun B E hg => hg.bounds) hStanley

end FormalAlgebra

/-! ## Numerical consistency witness

A theorem from hypotheses is only meaningful if the hypotheses are mutually
consistent.  This section is a **numerical consistency witness**: it
verifies, inside Lean, that the thirteen hypotheses of `theorem1_full` are
jointly satisfiable by concrete numerical data.  (The algebra that this
data is computed from — `A = R / Ann(X², Y² + XZ)`, a standard graded
Artinian level algebra of embedding dimension 3, socle degree `e = 2` and
type two, with Hilbert function `h = (1, 3, 2)`, Hilbert numerator
`(1-t)³(1+3t+2t²) = 1 - 4t² + 2t³ + 3t⁴ - 2t⁵`, minimal resolution
`0 → R(-5)² → R(-3)²⊕R(-4)³ → R(-2)⁴ → R → A`, and dual resolution data
`F₁ = R(-1)³ ⊕ R(-2)²`, `F₂ = R(-3)⁴`, `s = 5`, `r₂ = 2`, `ε₂ = 0` — is
*not* itself constructed in Lean; only its numerical shadow is checked.
What the witness proves formally is exactly consistency of the hypothesis
set, no more.) -/

section NumericalConsistencyWitness

/-- Hilbert function `h = (1, 3, 2)` of `A = R/Ann(X², Y² + XZ)`. -/
def hEx : ℤ → ℤ := fun i =>
  if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 0

/-- Its reindexed Matlis dual, `g t = h (e - t)` with `e = 2`. -/
def gEx : ℤ → ℤ := fun t => hEx (2 - t)

/-- Betti data of `F₁ = R(-1)³ ⊕ R(-2)²`. -/
def pEx : ℤ → ℤ := fun b => if b = 1 then 3 else if b = 2 then 2 else 0

/-- Betti data of `F₂ = R(-3)⁴`. -/
def qEx : ℤ → ℤ := fun b => if b = 3 then 4 else 0

lemma shiftSum_pEx (t : ℤ) :
    shiftSum 5 pEx t = 3 * Nz (t - 1) + 2 * Nz (t - 2) := by
  have hsub : ({1, 2} : Finset ℤ) ⊆ Finset.Icc (0 : ℤ) 5 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    omega
  have hzero : ∀ x ∈ Finset.Icc (0 : ℤ) 5, x ∉ ({1, 2} : Finset ℤ) →
      pEx x * Nz (t - x) = 0 := by
    intro x _ hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    simp [pEx, hnot.1, hnot.2]
  rw [shiftSum, ← Finset.sum_subset hsub hzero,
    Finset.sum_insert (by norm_num), Finset.sum_singleton]
  norm_num [pEx]

lemma shiftSum_qEx (t : ℤ) : shiftSum 5 qEx t = 4 * Nz (t - 3) := by
  have hsub : ({3} : Finset ℤ) ⊆ Finset.Icc (0 : ℤ) 5 := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    omega
  have hzero : ∀ x ∈ Finset.Icc (0 : ℤ) 5, x ∉ ({3} : Finset ℤ) →
      qEx x * Nz (t - x) = 0 := by
    intro x _ hnot
    simp only [Finset.mem_singleton] at hnot
    simp [qEx, hnot]
  rw [shiftSum, ← Finset.sum_subset hsub hzero, Finset.sum_singleton]
  norm_num [qEx]

/-- Rank additivity (paper (1)) holds numerically for this resolution. -/
lemma hresEx : ∀ t : ℤ, t ≤ 2 →
    gEx t = 2 * Nz t - shiftSum 5 pEx t + shiftSum 5 qEx t - Nz (t - 5) := by
  intro t ht
  rw [shiftSum_pEx, shiftSum_qEx]
  by_cases h0 : t = 0
  · subst h0; decide
  by_cases h1 : t = 1
  · subst h1; decide
  by_cases h2 : t = 2
  · subst h2; decide
  · have hneg : t < 0 := by omega
    have z1 : gEx t = 0 := by
      have c0 : ¬(2 - t = 0) := by omega
      have c1 : ¬(2 - t = 1) := by omega
      have c2 : ¬(2 - t = 2) := by omega
      simp [gEx, hEx, c0, c1, c2]
    rw [z1, Nz_neg t hneg, Nz_neg _ (by omega : t - 1 < 0),
      Nz_neg _ (by omega : t - 2 < 0), Nz_neg _ (by omega : t - 3 < 0),
      Nz_neg _ (by omega : t - 5 < 0)]
    ring

/-- The rank estimate (3) holds: `Q₂ - ε₂ = 0 ≤ P_{<2} - r₂ = 3 - 2`. -/
lemma h3Ex : ∀ d : ℤ, 2 ≤ d → d ≤ 2 →
    (∑ b ∈ Finset.Icc (0 : ℤ) d, qEx b) - 0
      ≤ (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), pEx b) - 2 := by
  intro d hd hde
  have hd2 : d = 2 := by omega
  subst hd2
  have hq : (∑ b ∈ Finset.Icc (0 : ℤ) 2, qEx b) = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    simp only [Finset.mem_Icc] at hb
    have : ¬(b = 3) := by omega
    simp [qEx, this]
  have hp : (∑ b ∈ Finset.Icc (0 : ℤ) (2 - 1 : ℤ), pEx b) = 3 := by
    have hicc : Finset.Icc (0 : ℤ) (2 - 1 : ℤ) = {0, 1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hicc, Finset.sum_insert (by norm_num), Finset.sum_singleton]
    norm_num [pEx]
  rw [hq, hp]
  norm_num

/-- **Numerical consistency witness**: all hypotheses of `theorem1_full`
are satisfied by the numerical data computed from
`A = R/Ann(X², Y² + XZ)`, and the theorem delivers log-concavity of its
Hilbert function `(1, 3, 2)`.  Since this instance never enters the
`r_d = 1` failure branch, the Gorenstein predicate can be instantiated
by `False` and Stanley's theorem is not consumed. -/
theorem consistency_witness :
    ∀ i : ℤ, 1 ≤ i → i ≤ 2 - 1 → hEx (i - 1) * hEx (i + 1) ≤ hEx i ^ 2 := by
  refine theorem1_full 2 hEx gEx pEx qEx (fun _ => 2) (fun _ => 0)
    (fun _ _ => False)
    ?_ ?_ (fun _ => rfl) ?_ ?_ hresEx ?_ h3Ex ?_ ?_ ?_
    (fun _ _ hcontra => hcontra.elim) (fun _ _ hcontra => hcontra.elim)
  · intro t; simp only [hEx]; split_ifs <;> norm_num
  · intro t
    by_cases h0 : t = 0
    · subst h0; decide
    by_cases h1 : t = 1
    · subst h1; decide
    by_cases h2 : t = 2
    · subst h2; decide
    · simp only [hEx, if_neg h0, if_neg h1, if_neg h2]
      exact Nz_nonneg t
  · intro b; simp only [pEx]; split_ifs <;> norm_num
  · intro b; simp only [qEx]; split_ifs <;> norm_num
  · intro d _ _; exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩
  · intro d _ _ hcontra; norm_num at hcontra
  · intro d _ _ hcontra; norm_num at hcontra
  · intro d _ _ hcontra; norm_num at hcontra

/-- The concrete inequality delivered: `h₀ h₂ = 2 ≤ 9 = h₁²`. -/
example : hEx 0 * hEx 2 ≤ hEx 1 ^ 2 :=
  consistency_witness 1 (by norm_num) (by norm_num)

example : hEx 0 = 1 ∧ hEx 1 = 3 ∧ hEx 2 = 2 := by decide

end NumericalConsistencyWitness

/-! ## Axiom audit

Only Lean's standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorry`, no extra axioms. -/

#print axioms theorem1_full
#print axioms consistency_witness
#print axioms deep_dispatch
#print axioms theorem1
#print axioms GoodTriple.log_concave
#print axioms shiftSum_second_diff
#print axioms binomial_window_log_concave
#print axioms proper_subfamily_linearIndependent
#print axioms rank_estimate_graded
#print axioms primitive_line_saturated
#print axioms primitive_line_saturated_fraction
#print axioms line_factorization
#print axioms cyclic_submodule_simple_socle
#print axioms finrank_homogeneousSubmodule
#print axioms hilb_le_Nz
#print axioms hilb_zero
#print axioms IsTypeTwoLevel.hilb_one
#print axioms IsTypeTwoLevel.hilb_top
#print axioms IsTypeTwoLevel.hilb_vanish
#print axioms IsTypeTwoLevel.two_le_socleDegree
#print axioms GorensteinQuotientHF.bounds
#print axioms theorem1_of_level
#print axioms finrank_gradedDualPiece
#print axioms GradedResolutionDuality.low_complex
#print axioms GradedResolutionDuality.rank_inequality
#print axioms GradedResolutionDuality.hilbert_series
#print axioms GradedResolutionDuality.ideal_no_low_degree
#print axioms line_coefficient_eq_annihilator_low
#print axioms idealPiece_finrank_add_quotPiece
#print axioms ExactPresentation.finrank_add
#print axioms SurjectivePresentation.finrank_add
#print axioms theorem1_of_resolution

end LogConcavity
