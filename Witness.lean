import LogConcavity

open scoped BigOperators

namespace LogConcavity

universe u
variable {k : Type u} [Field k]

open MvPolynomial Module
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Classical.decEq

/-! # A concrete codimension-three level algebra of type two

`A = k[x,y,z] / (xy, xz, y², z², x³)` is the inverse system `⟨X², YZ⟩`.  Its
Hilbert function is `(1, 3, 2)`: socle degree `2`, type two, level.  We check
`IsTypeTwoLevel` for it, which certifies that the hypothesis is not vacuous.
-/

/-- An exponent vector of `k[x,y,z]`, written by its three exponents. -/
noncomputable def mono (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c]

@[simp] lemma mono_apply_zero (a b c : ℕ) : mono a b c 0 = a := rfl
@[simp] lemma mono_apply_one (a b c : ℕ) : mono a b c 1 = b := rfl
@[simp] lemma mono_apply_two (a b c : ℕ) : mono a b c 2 = c := rfl

/-- The five generating exponent vectors: `xy, xz, y², z², x³`. -/
def witnessExps : Set (Fin 3 →₀ ℕ) :=
  {mono 1 1 0, mono 1 0 1, mono 0 2 0, mono 0 0 2, mono 3 0 0}

/-- `J = (xy, xz, y², z², x³) ⊆ k[x,y,z]`. -/
noncomputable def witnessIdeal (k : Type u) [Field k] : Ideal (R3 k) :=
  Ideal.span ((fun s => MvPolynomial.monomial s (1 : k)) '' witnessExps)

/-- The divisibility predicate cutting out `J`, phrased so `omega` can use it. -/
def witnessPred (m : Fin 3 →₀ ℕ) : Prop :=
  (1 ≤ m 0 ∧ 1 ≤ m 1) ∨ (1 ≤ m 0 ∧ 1 ≤ m 2) ∨
    2 ≤ m 1 ∨ 2 ≤ m 2 ∨ 3 ≤ m 0

lemma mem_witnessIdeal_iff (f : R3 k) :
    f ∈ witnessIdeal k ↔ ∀ m ∈ f.support, witnessPred m := by
  rw [witnessIdeal, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h m hm
    obtain ⟨s, hs, hsm⟩ := h m hm
    have hle : ∀ i, s i ≤ m i := fun i => hsm i
    simp only [witnessExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    unfold witnessPred
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨by simpa using hle 0, by simpa using hle 1⟩
    · exact Or.inr (Or.inl ⟨by simpa using hle 0, by simpa using hle 2⟩)
    · exact Or.inr (Or.inr (Or.inl (by simpa using hle 1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hle 2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hle 0))))
  · intro h m hm
    have hp := h m hm
    unfold witnessPred at hp
    have hle : ∀ (a b c : ℕ), a ≤ m 0 → b ≤ m 1 → c ≤ m 2 → mono a b c ≤ m := by
      intro a b c h0 h1 h2
      intro i
      fin_cases i <;> simpa using ‹_›
    rcases hp with ⟨h0, h1⟩ | ⟨h0, h2⟩ | h1 | h2 | h0
    · exact ⟨mono 1 1 0, by simp [witnessExps], hle 1 1 0 h0 h1 (by omega)⟩
    · exact ⟨mono 1 0 1, by simp [witnessExps], hle 1 0 1 h0 (by omega) h2⟩
    · exact ⟨mono 0 2 0, by simp [witnessExps], hle 0 2 0 (by omega) h1 (by omega)⟩
    · exact ⟨mono 0 0 2, by simp [witnessExps], hle 0 0 2 (by omega) (by omega) h2⟩
    · exact ⟨mono 3 0 0, by simp [witnessExps], hle 3 0 0 h0 (by omega) (by omega)⟩

/-- The total degree of an exponent vector in three variables. -/
lemma weight_one_eq (m : Fin 3 →₀ ℕ) :
    (Finsupp.weight (1 : Fin 3 → ℕ)) m = m 0 + m 1 + m 2 := by
  classical
  rw [Finsupp.weight_apply]
  have h2 : (m.sum fun i c => c • (1 : Fin 3 → ℕ) i) = ∑ i : Fin 3, m i := by
    rw [Finsupp.sum]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simpa using hi
  rw [h2, Fin.sum_univ_three]

lemma isHomogeneous_degree {f : R3 k} {n : ℕ} (hf : f.IsHomogeneous n)
    {m : Fin 3 →₀ ℕ} (hm : m ∈ f.support) : m 0 + m 1 + m 2 = n := by
  have hc : MvPolynomial.coeff m f ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have h := hf hc
  rwa [weight_one_eq] at h

lemma witnessIdeal_isHomogeneous :
    (witnessIdeal k).IsHomogeneous (homogeneousSubmodule (Fin 3) k) := by
  intro n f hf
  have hgoal : MvPolynomial.homogeneousComponent n f ∈ witnessIdeal k := by
    rw [mem_witnessIdeal_iff] at hf ⊢
    intro m hm
    apply hf
    have hc := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_homogeneousComponent] at hc
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hc
    simp at hc
  rw [← MvPolynomial.decomposition.decompose'_apply] at hgoal
  exact hgoal

lemma witnessIdeal_ne_top : witnessIdeal k ≠ ⊤ := by
  intro h
  have h1 : (1 : R3 k) ∈ witnessIdeal k := by rw [h]; trivial
  rw [mem_witnessIdeal_iff] at h1
  have hm : (0 : Fin 3 →₀ ℕ) ∈ (1 : R3 k).support := by
    simp [MvPolynomial.support_one]
  have := h1 0 hm
  unfold witnessPred at this
  simp at this

lemma witnessIdeal_no_linear_forms :
    ∀ f ∈ witnessIdeal k, MvPolynomial.IsHomogeneous f 1 → f = 0 := by
  intro f hfJ hf1
  by_contra hf0
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hf0
  have hdeg := isHomogeneous_degree hf1 hm
  have hp := (mem_witnessIdeal_iff f).mp hfJ m hm
  unfold witnessPred at hp
  omega

/-- Everything of degree at least three is in `J`. -/
lemma witnessIdeal_high_degree {f : R3 k} {n : ℕ} (hn : 2 < n)
    (hf : MvPolynomial.IsHomogeneous f n) : f ∈ witnessIdeal k := by
  rw [mem_witnessIdeal_iff]
  intro m hm
  have hdeg := isHomogeneous_degree hf hm
  unfold witnessPred
  omega

lemma witnessIdeal_vanish_above :
    ∀ n : ℕ, 2 < n → quotPiece (witnessIdeal k) n = ⊥ := by
  intro n hn
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨f, hfhom, rfl⟩ := Submodule.mem_map.mp hx
  change Ideal.Quotient.mk (witnessIdeal k) f = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact witnessIdeal_high_degree hn
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hfhom)

lemma finsupp_degree_eq (m : Fin 3 →₀ ℕ) : m.degree = m 0 + m 1 + m 2 := by
  classical
  have h : m.degree = ∑ i ∈ m.support, m i := rfl
  rw [h]
  have h2 : ∑ i ∈ m.support, m i = ∑ i : Fin 3, m i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simpa using hi
  rw [h2, Fin.sum_univ_three]

lemma finsupp_eq_of (m : Fin 3 →₀ ℕ) (a b c : ℕ)
    (h0 : m 0 = a) (h1 : m 1 = b) (h2 : m 2 = c) : m = mono a b c := by
  ext i
  fin_cases i <;> simpa

/-- Support-level version of `witnessIdeal_high_degree`, with no homogeneity
assumption. -/
lemma witnessIdeal_of_support_high {f : R3 k}
    (h : ∀ m ∈ f.support, 3 ≤ m 0 + m 1 + m 2) : f ∈ witnessIdeal k := by
  rw [mem_witnessIdeal_iff]
  intro m hm
  have := h m hm
  unfold witnessPred
  omega

/-- The `k`-linear quotient map. -/
noncomputable def Q (k : Type u) [Field k] :
    R3 k →ₗ[k] (R3 k ⧸ witnessIdeal k) :=
  (Ideal.Quotient.mkₐ k (witnessIdeal k)).toLinearMap

@[simp] lemma Q_apply (f : R3 k) : Q k f = Ideal.Quotient.mk (witnessIdeal k) f := rfl

lemma sub_components_mem (f : R3 k) :
    f - (MvPolynomial.homogeneousComponent 0 f +
      MvPolynomial.homogeneousComponent 1 f +
      MvPolynomial.homogeneousComponent 2 f) ∈ witnessIdeal k := by
  apply witnessIdeal_of_support_high
  intro m hm
  by_contra hlt
  refine MvPolynomial.mem_support_iff.mp hm ?_
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_add,
    MvPolynomial.coeff_homogeneousComponent, finsupp_degree_eq]
  interval_cases h : (m 0 + m 1 + m 2) <;> simp <;> omega

/-- The degree `≤ 2` part of `R`, a finite-dimensional `k`-subspace. -/
noncomputable def lowPart (k : Type u) [Field k] : Submodule k (R3 k) :=
  homogeneousSubmodule (Fin 3) k 0 ⊔ homogeneousSubmodule (Fin 3) k 1 ⊔
    homogeneousSubmodule (Fin 3) k 2

instance lowPart_finiteDimensional : FiniteDimensional k (lowPart k) := by
  unfold lowPart
  infer_instance

lemma Q_lowPart_surjective :
    Function.Surjective ((Q k).comp (lowPart k).subtype) := by
  intro ā
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective ā
  have hmem : MvPolynomial.homogeneousComponent 0 f +
      MvPolynomial.homogeneousComponent 1 f +
      MvPolynomial.homogeneousComponent 2 f ∈ lowPart k := by
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.mem_sup_left (Submodule.mem_sup_left
          ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.homogeneousComponent_isHomogeneous 0 f)))
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right
          ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.homogeneousComponent_isHomogeneous 1 f)))
    · exact Submodule.mem_sup_right
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.homogeneousComponent_isHomogeneous 2 f))
  refine ⟨⟨_, hmem⟩, ?_⟩
  show Ideal.Quotient.mk (witnessIdeal k) _ = Ideal.Quotient.mk _ f
  rw [eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact sub_components_mem f

instance witnessIdeal_finiteDimensional :
    FiniteDimensional k (R3 k ⧸ witnessIdeal k) :=
  FiniteDimensional.of_surjective _ Q_lowPart_surjective

lemma monomial_mem_iff (m : Fin 3 →₀ ℕ) :
    (MvPolynomial.monomial m (1 : k) : R3 k) ∈ witnessIdeal k ↔ witnessPred m := by
  rw [mem_witnessIdeal_iff]
  constructor
  · intro h
    exact h m (by simp [MvPolynomial.support_monomial])
  · intro h m' hm'
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero] at hm'
    rw [Finset.mem_singleton] at hm'
    exact hm' ▸ h

lemma single_add_apply (j i : Fin 3) (m : Fin 3 →₀ ℕ) :
    ((Finsupp.single j 1 + m : Fin 3 →₀ ℕ)) i = (if j = i then 1 else 0) + m i := by
  simp [Finsupp.single_apply]

lemma fin3_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by revert j; decide

lemma single0_add (m : Fin 3 →₀ ℕ) :
    (Finsupp.single (0 : Fin 3) 1 + m : Fin 3 →₀ ℕ) = mono (m 0 + 1) (m 1) (m 2) := by
  ext i
  fin_cases i <;> simp [single_add_apply] <;> omega

lemma single1_add (m : Fin 3 →₀ ℕ) :
    (Finsupp.single (1 : Fin 3) 1 + m : Fin 3 →₀ ℕ) = mono (m 0) (m 1 + 1) (m 2) := by
  ext i
  fin_cases i <;> simp [single_add_apply] <;> omega

lemma single2_add (m : Fin 3 →₀ ℕ) :
    (Finsupp.single (2 : Fin 3) 1 + m : Fin 3 →₀ ℕ) = mono (m 0) (m 1) (m 2 + 1) := by
  ext i
  fin_cases i <;> simp [single_add_apply] <;> omega

lemma Q_monomial_smul (m : Fin 3 →₀ ℕ) (s : k) :
    Q k (MvPolynomial.monomial m s) = s • Q k (MvPolynomial.monomial m 1) := by
  rw [← map_smul]
  congr 1
  rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/-- The two socle generators: the classes of `x²` and `yz`. -/
noncomputable def wu (k : Type u) [Field k] : R3 k ⧸ witnessIdeal k :=
  Q k (MvPolynomial.monomial (mono 2 0 0) 1)

noncomputable def wv (k : Type u) [Field k] : R3 k ⧸ witnessIdeal k :=
  Q k (MvPolynomial.monomial (mono 0 1 1) 1)

lemma mul_monomial_mk (j : Fin 3) (m : Fin 3 →₀ ℕ) :
    Ideal.Quotient.mk (witnessIdeal k) (MvPolynomial.X j) *
        Q k (MvPolynomial.monomial m 1) =
      Q k (MvPolynomial.monomial (Finsupp.single j 1 + m) 1) := by
  simp only [Q_apply, ← map_mul]
  congr 1
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

lemma wu_mem_socle : wu k ∈ socle (witnessIdeal k) := by
  intro j
  rw [wu, mul_monomial_mk]
  show Ideal.Quotient.mk (witnessIdeal k) _ = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, monomial_mem_iff]
  rcases fin3_cases j with rfl | rfl | rfl
  · rw [single0_add]; unfold witnessPred; simp
  · rw [single1_add]; unfold witnessPred; simp
  · rw [single2_add]; unfold witnessPred; simp

lemma wv_mem_socle : wv k ∈ socle (witnessIdeal k) := by
  intro j
  rw [wv, mul_monomial_mk]
  show Ideal.Quotient.mk (witnessIdeal k) _ = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, monomial_mem_iff]
  rcases fin3_cases j with rfl | rfl | rfl
  · rw [single0_add]; unfold witnessPred; simp
  · rw [single1_add]; unfold witnessPred; simp
  · rw [single2_add]; unfold witnessPred; simp

/-- Membership in the span of the two socle generators, read off the support. -/
lemma Q_mem_span_of_support (f : R3 k)
    (h : ∀ m ∈ f.support, witnessPred m ∨ m = mono 2 0 0 ∨ m = mono 0 1 1) :
    Q k f ∈ Submodule.span k {wu k, wv k} := by
  classical
  have key : Q k (∑ m ∈ f.support,
      MvPolynomial.monomial m (MvPolynomial.coeff m f))
      ∈ Submodule.span k {wu k, wv k} := ?_
  · rwa [← MvPolynomial.as_sum f] at key
  rw [map_sum]
  refine Submodule.sum_mem _ ?_
  intro m hm
  have hsmul : (MvPolynomial.monomial m (MvPolynomial.coeff m f) : R3 k) =
      MvPolynomial.coeff m f • MvPolynomial.monomial m 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsmul, map_smul]
  rcases h m hm with hp | rfl | rfl
  · have : Q k (MvPolynomial.monomial m (1 : k)) = 0 := by
      show Ideal.Quotient.mk (witnessIdeal k) _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, monomial_mem_iff]
      exact hp
    rw [this, smul_zero]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [wu]))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [wv]))

lemma socle_le_span :
    socle (witnessIdeal k) ≤ Submodule.span k {wu k, wv k} := by
  classical
  intro ā hā
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ā
  have hmul : ∀ j : Fin 3, (MvPolynomial.X j : R3 k) * a ∈ witnessIdeal k := by
    intro j
    have := hā j
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  refine Q_mem_span_of_support a ?_
  intro m hm
  have hshift : ∀ j : Fin 3, witnessPred (Finsupp.single j 1 + m) := by
    intro j
    refine (mem_witnessIdeal_iff _).mp (hmul j) _ ?_
    rw [MvPolynomial.support_X_mul]
    exact Finset.mem_map.mpr ⟨m, hm, rfl⟩
  have h0 := hshift 0
  have h1 := hshift 1
  have h2 := hshift 2
  rw [single0_add] at h0
  rw [single1_add] at h1
  rw [single2_add] at h2
  unfold witnessPred at h0 h1 h2 ⊢
  simp only [mono_apply_zero, mono_apply_one, mono_apply_two] at h0 h1 h2
  by_cases hp : (1 ≤ m 0 ∧ 1 ≤ m 1) ∨ (1 ≤ m 0 ∧ 1 ≤ m 2) ∨
      2 ≤ m 1 ∨ 2 ≤ m 2 ∨ 3 ≤ m 0
  · exact Or.inl hp
  · push_neg at hp
    refine Or.inr ?_
    by_cases hz : m 0 = 2
    · exact Or.inl (finsupp_eq_of m 2 0 0 hz (by omega) (by omega))
    · exact Or.inr (finsupp_eq_of m 0 1 1 (by omega) (by omega) (by omega))

lemma not_witnessPred_u : ¬ witnessPred (mono 2 0 0) := by
  unfold witnessPred; simp

lemma not_witnessPred_v : ¬ witnessPred (mono 0 1 1) := by
  unfold witnessPred; simp

lemma mono_u_ne_v : (mono 2 0 0 : Fin 3 →₀ ℕ) ≠ mono 0 1 1 := by
  intro h
  have h0 := congrArg (fun m : Fin 3 →₀ ℕ => m 0) h
  simp at h0

lemma wuv_independent : LinearIndependent k ![wu k, wv k] := by
  classical
  rw [LinearIndependent.pair_iff]
  intro s t hst
  set g : R3 k := MvPolynomial.monomial (mono 2 0 0) s +
    MvPolynomial.monomial (mono 0 1 1) t with hg
  have hQg : Q k g = s • wu k + t • wv k := by
    rw [hg, map_add,
      show Q k (MvPolynomial.monomial (mono 2 0 0) s) = s • wu k from
        Q_monomial_smul _ _,
      show Q k (MvPolynomial.monomial (mono 0 1 1) t) = t • wv k from
        Q_monomial_smul _ _]
  have hgJ : g ∈ witnessIdeal k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Q_apply, hQg, hst]
  rw [mem_witnessIdeal_iff] at hgJ
  constructor
  · by_contra hs
    refine not_witnessPred_u (hgJ (mono 2 0 0) ?_)
    rw [MvPolynomial.mem_support_iff, hg, MvPolynomial.coeff_add,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial,
      if_pos rfl, if_neg (Ne.symm mono_u_ne_v), add_zero]
    exact hs
  · by_contra ht
    refine not_witnessPred_v (hgJ (mono 0 1 1) ?_)
    rw [MvPolynomial.mem_support_iff, hg, MvPolynomial.coeff_add,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial,
      if_neg mono_u_ne_v, if_pos rfl, zero_add]
    exact ht

lemma socle_eq_span : socle (witnessIdeal k) = Submodule.span k {wu k, wv k} := by
  apply le_antisymm socle_le_span
  rw [Submodule.span_le]
  rintro x (rfl | rfl)
  · exact wu_mem_socle
  · exact wv_mem_socle

lemma finrank_socle_witness : finrank k (socle (witnessIdeal k)) = 2 := by
  classical
  rw [socle_eq_span]
  have hspan : ({wu k, wv k} : Set (R3 k ⧸ witnessIdeal k)) =
      Set.range ![wu k, wv k] := by
    simp [Matrix.range_cons, Matrix.range_empty]
    exact Set.pair_comm _ _
  rw [hspan, finrank_span_eq_card wuv_independent]
  simp

lemma monomial_mem_homogeneousSubmodule (a b c : ℕ) :
    (MvPolynomial.monomial (mono a b c) (1 : k) : R3 k) ∈
      homogeneousSubmodule (Fin 3) k (a + b + c) := by
  apply (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
  apply MvPolynomial.isHomogeneous_monomial
  rw [finsupp_degree_eq]
  simp

lemma socle_le_quotPiece :
    socle (witnessIdeal k) ≤ quotPiece (witnessIdeal k) 2 := by
  rw [socle_eq_span, Submodule.span_le]
  rintro x (rfl | rfl)
  · exact Submodule.mem_map.mpr
      ⟨_, monomial_mem_homogeneousSubmodule (k := k) 2 0 0, rfl⟩
  · exact Submodule.mem_map.mpr
      ⟨_, monomial_mem_homogeneousSubmodule (k := k) 0 1 1, rfl⟩

/-- **The witness.**  `k[x,y,z]/(xy, xz, y², z², x³)` — the inverse system
`⟨X², YZ⟩` — is a codimension-three level algebra of type two with socle
degree `2`. -/
theorem isTypeTwoLevel_witness : IsTypeTwoLevel (witnessIdeal k) 2 where
  homogeneous := witnessIdeal_isHomogeneous
  proper := witnessIdeal_ne_top
  no_linear_forms := witnessIdeal_no_linear_forms
  finiteDimensional := witnessIdeal_finiteDimensional
  vanish_above := witnessIdeal_vanish_above
  socle_concentrated := socle_le_quotPiece
  type_two := finrank_socle_witness

/-! ## The Hilbert function of the witness

The repository derives the profile `(1, 3, …, h_e = 2)` from `IsTypeTwoLevel`.
Running those derivations on the concrete algebra pins its Hilbert function to
`(1, 3, 2)` and exhibits the log-concavity inequality at the single interior
degree `i = 1`. -/

lemma witness_hilb_zero : hilb (witnessIdeal k) 0 = 1 :=
  hilb_zero _ witnessIdeal_ne_top

lemma witness_hilb_one : hilb (witnessIdeal k) 1 = 3 :=
  (isTypeTwoLevel_witness (k := k)).hilb_one

lemma witness_hilb_two : hilb (witnessIdeal k) 2 = 2 :=
  (isTypeTwoLevel_witness (k := k)).hilb_top

lemma witness_hilb_above {t : ℤ} (ht : 2 < t) : hilb (witnessIdeal k) t = 0 := by
  rw [hilb, if_pos (by omega)]
  have hn : 2 < t.toNat := by omega
  rw [witnessIdeal_vanish_above t.toNat hn]
  simp

/-- Log-concavity holds on the nose for the witness: `h₀ · h₂ = 2 ≤ 9 = h₁²`. -/
lemma witness_log_concave :
    hilb (witnessIdeal k) 0 * hilb (witnessIdeal k) 2 ≤
      hilb (witnessIdeal k) 1 ^ 2 := by
  rw [witness_hilb_zero, witness_hilb_one, witness_hilb_two]
  norm_num

end LogConcavity

#print axioms LogConcavity.isTypeTwoLevel_witness
#print axioms LogConcavity.witness_log_concave
#print axioms LogConcavity.finrank_socle_witness
