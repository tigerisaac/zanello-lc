import InverseSystem
import FormalDepsBridge

open scoped BigOperators

namespace LogConcavity

universe uk ub ug ud

variable {k : Type uk} [Field k]

open Module
open CategoryTheory
open HomogeneousFirstRelations
open HomogeneousFirstRelations.HomogeneousSecondRelations

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000

/-! ## FormalDeps specialization

The homological port is now part of the ordinary Lake dependency graph.  These
two declarations are the exact input used later when the third syzygy is
localized: Hilbert's syzygy theorem computes the global dimension of the
three-variable polynomial ring, and the corresponding projective-dimension
bound is available for every module (hence for finitely generated modules).
-/

theorem r3_globalDimension [Small.{v, uk} k] :
    _root_.globalDimension.{v} (R3 k) = 3 := by
  simpa [R3] using (FormalDeps.hilbertsSyzygy (k := k) 3)

theorem r3_projectiveDimensionLE [Small.{v, uk} k]
    (M : ModuleCat.{v} (R3 k)) :
    HasProjectiveDimensionLE M 3 := by
  simpa only [R3] using
    (FormalDeps.projectiveDimensionLEOfPolynomial (k := k) 3 M)

#print axioms LogConcavity.r3_globalDimension
#print axioms LogConcavity.r3_projectiveDimensionLE

/-!
This module is the executable home of the graded resolution construction.
`InverseSystem.lean` contains the low-level component and inverse-system lemmas;
the declarations below package those maps as a genuine homogeneous complex
so that later homological arguments can consume one object rather than a
collection of unrelated witnesses.
-/

structure HomogeneousFreeComplexData (I : Ideal (R3 k)) (e : ℕ)
    (hA : IsTypeTwoLevel I e) where
  first : HomogeneousFirstRelations.{uk, ub} hA
  second : HomogeneousSecondRelations.{uk, ug, ub} first
  third : HomogeneousThirdRelations.{uk, ud, ub, ug} second

namespace HomogeneousFreeComplexData

variable {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)

noncomputable def ofLevel : HomogeneousFreeComplexData I e hA :=
  { first := homogeneousFirstRelations hA
    second := homogeneousSecondRelations (homogeneousFirstRelations hA)
    third := homogeneousThirdRelations
      (homogeneousSecondRelations (homogeneousFirstRelations hA)) }

lemma presentation_surjective :
    Function.Surjective (inverseSystemMap hA) :=
  inverseSystemMap_surjective hA

lemma first_range (C : HomogeneousFreeComplexData I e hA) :
    LinearMap.range C.first.d₁ = inverseSystemKernel hA :=
  C.first.range_d₁_eq_kernel

lemma second_range (C : HomogeneousFreeComplexData I e hA) :
    LinearMap.range C.second.d₂ = LinearMap.ker C.first.d₁ :=
  C.second.range_d₂_eq_kernel

lemma third_range (C : HomogeneousFreeComplexData I e hA) :
    LinearMap.range C.third.d₃ = LinearMap.ker C.second.d₂ :=
  C.third.range_d₃_eq_kernel

lemma first_second_complex (C : HomogeneousFreeComplexData I e hA) :
    C.first.d₁.comp C.second.d₂ = 0 :=
  C.second.d₁_comp_d₂

lemma second_third_complex (C : HomogeneousFreeComplexData I e hA) :
    C.second.d₂.comp C.third.d₃ = 0 :=
  C.third.d₂_comp_d₃

lemma finite_free_first (C : HomogeneousFreeComplexData I e hA) :
    Module.Free (R3 k) (C.first.β → R3 k) := by
  letI := C.first.fintype
  infer_instance

lemma finite_free_second (C : HomogeneousFreeComplexData I e hA) :
    Module.Free (R3 k) (C.second.γ → R3 k) := by
  letI := C.second.fintype
  infer_instance

lemma finite_free_third (C : HomogeneousFreeComplexData I e hA) :
    Module.Free (R3 k) (C.third.δ → R3 k) := by
  letI := C.third.fintype
  infer_instance

lemma finite_first (C : HomogeneousFreeComplexData I e hA) :
    Module.Finite (R3 k) (C.first.β → R3 k) := by
  letI := C.first.fintype
  infer_instance

lemma finite_second (C : HomogeneousFreeComplexData I e hA) :
    Module.Finite (R3 k) (C.second.γ → R3 k) := by
  letI := C.second.fintype
  infer_instance

lemma finite_third (C : HomogeneousFreeComplexData I e hA) :
    Module.Finite (R3 k) (C.third.δ → R3 k) := by
  letI := C.third.fintype
  infer_instance

end HomogeneousFreeComplexData

/-! ## Actual shifted bases and minimal differentials

The finite generating families above are deliberately produced before any
minimality choice is made.  The following certificate is the stronger object
needed for a graded minimal resolution: each free module is indexed by an
actual finite basis, each basis vector has a shift, the matrix entries are
homogeneous in the shifted degrees, and every differential has entries in
the irrelevant ideal.  Thus the shifts are multisets (the fibres of the
displayed functions), not merely upper bounds on projective dimensions. -/

noncomputable def irrelevantIdeal (k : Type uk) [Field k] : Ideal (R3 k) :=
  MvPolynomial.idealOfVars (Fin 3) k

attribute [local instance] Classical.decEq

lemma span_columns_eq_range
    {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Fintype ι]
    (f : (ι → R) →ₗ[R] M) :
    Submodule.span R (Set.range (fun i => f (Pi.single i 1))) = LinearMap.range f := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact ⟨Pi.single i 1, rfl⟩
  · rintro y ⟨c, rfl⟩
    have hc : (∑ i, c i • Pi.single i 1) = c := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fintype.sum_eq_single j]
      · simp
      · intro i hij
        simp [hij]
    rw [← hc, map_sum]
    simp only [map_smul]
    apply Submodule.sum_mem
    intro i hi
    have hi' : f (Pi.single i 1) ∈ Set.range (fun i => f (Pi.single i 1)) :=
      ⟨i, rfl⟩
    exact Submodule.smul_mem (Submodule.span R (Set.range (fun i => f (Pi.single i 1))))
      (c i) (Submodule.subset_span hi')

lemma range_le_smul_top_of_entries
    {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : (ι → R) →ₗ[R] (κ → R)) (J : Ideal R)
    (hentry : ∀ i j, f (Pi.single i 1) j ∈ J) :
    LinearMap.range f ≤ J • (⊤ : Submodule R (κ → R)) := by
  rintro y ⟨c, rfl⟩
  have hc : (∑ i, c i • Pi.single i 1) = c := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro i hij
      simp [hij]
  rw [← hc, map_sum]
  apply Submodule.sum_mem
  intro i hi
  have hcolumn : f (Pi.single i 1) ∈ J • (⊤ : Submodule R (κ → R)) := by
    have hsingle :
        (∑ j, f (Pi.single i 1) j • Pi.single j 1) = f (Pi.single i 1) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fintype.sum_eq_single j]
      · simp
      · intro l hlj
        simp [hlj]
    rw [← hsingle]
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.smul_mem_smul (hentry i j) Submodule.mem_top
  rw [f.map_smul]
  exact Submodule.smul_mem (J • (⊤ : Submodule R (κ → R))) (c i) hcolumn

/-! A finite spanning family can be reduced without leaving the class of
homogeneous vectors.  We use this small piece of finite combinatorics at
each stage of the graded resolution: the ambient family is already
homogeneous, so a cardinality-minimal subfamily is still homogeneous. -/

structure MinimalSpanningFamily
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype G]
    (P : Submodule R M) (generator : G → M)
    (hspan : Submodule.span R (Set.range generator) = P) where
  indices : Finset G
  span_eq : Submodule.span R (generator '' (indices : Set G)) = P
  card_min : ∀ s : Finset G,
    Submodule.span R (generator '' (s : Set G)) = P → indices.card ≤ s.card

noncomputable def MinimalSpanningFamily.ofSpan
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype G]
    (P : Submodule R M) (generator : G → M)
    (hspan : Submodule.span R (Set.range generator) = P) :
    MinimalSpanningFamily P generator hspan := by
  classical
  let good : Finset (Finset G) :=
    Finset.univ.filter (fun s =>
      Submodule.span R (generator '' (s : Set G)) = P)
  have hgood : good.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [Set.range] using hspan
  let choice := Finset.exists_min_image good Finset.card hgood
  let s := Classical.choose choice
  have hs : s ∈ good := (Classical.choose_spec choice).1
  have hmin : ∀ s' ∈ good, s.card ≤ s'.card :=
    (Classical.choose_spec choice).2
  refine
    { indices := s
      span_eq := (Finset.mem_filter.mp hs).2
      card_min := ?_ }
  intro t ht
  exact hmin t (by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ht⟩)

noncomputable def firstMinimalSpanningFamily
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    @MinimalSpanningFamily (R3 k) (Fin 2 → R3 k)
      (homogeneousFirstRelations hA).β _ _ _
      (homogeneousFirstRelations hA).fintype
      (inverseSystemKernel hA)
      (homogeneousFirstRelations hA).generator
      (homogeneousFirstRelations hA).span_eq := by
  classical
  let H := homogeneousFirstRelations hA
  letI : Fintype H.β := H.fintype
  exact MinimalSpanningFamily.ofSpan (inverseSystemKernel hA) H.generator H.span_eq

noncomputable def secondMinimalSpanningFamily
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (H : HomogeneousFirstRelations hA) :
    @MinimalSpanningFamily (R3 k) (H.β → R3 k)
      (homogeneousSecondRelations H).γ _ _ _
      (homogeneousSecondRelations H).fintype
      (LinearMap.ker H.d₁)
      (homogeneousSecondRelations H).generator
      (homogeneousSecondRelations H).span_eq := by
  classical
  letI : Fintype H.β := H.fintype
  let S := homogeneousSecondRelations H
  letI : Fintype S.γ := S.fintype
  exact MinimalSpanningFamily.ofSpan (LinearMap.ker H.d₁) S.generator S.span_eq

noncomputable def thirdMinimalSpanningFamily
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    {H : HomogeneousFirstRelations hA}
    (S : HomogeneousSecondRelations H) :
    @MinimalSpanningFamily (R3 k) (S.γ → R3 k)
      (homogeneousThirdRelations S).δ _ _ _
      (homogeneousThirdRelations S).fintype
      (LinearMap.ker S.d₂)
      (homogeneousThirdRelations S).generator
      (homogeneousThirdRelations S).span_eq := by
  classical
  letI : Fintype H.β := H.fintype
  letI : Fintype S.γ := S.fintype
  let T := homogeneousThirdRelations S
  letI : Fintype T.δ := T.fintype
  exact MinimalSpanningFamily.ofSpan (LinearMap.ker S.d₂) T.generator T.span_eq

lemma MinimalSpanningFamily.erase_not_span
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype G] {P : Submodule R M} {generator : G → M}
    {hspan : Submodule.span R (Set.range generator) = P}
    (F : MinimalSpanningFamily P generator hspan) {i : G}
    (hi : i ∈ F.indices) :
    Submodule.span R (generator '' (F.indices.erase i : Set G)) ≠ P := by
  intro h
  have hcard := F.card_min (F.indices.erase i) h
  exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hi)) hcard

lemma MinimalSpanningFamily.mem_span_of_mem
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype G] {P : Submodule R M} {generator : G → M}
    {hspan : Submodule.span R (Set.range generator) = P}
    (F : MinimalSpanningFamily P generator hspan) {i : G}
    (hi : i ∈ F.indices) : generator i ∈ P := by
  rw [← F.span_eq]
  exact Submodule.subset_span ⟨i, hi, rfl⟩

lemma span_subtype_finset_range
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {s : Finset G} (generator : G → M) :
    Submodule.span R (Set.range (fun i : s => generator i.1)) =
      Submodule.span R (generator '' (s : Set G)) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

lemma MinimalSpanningFamily.not_mem_span_erase
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype G] {P : Submodule R M} {generator : G → M}
    {hspan : Submodule.span R (Set.range generator) = P}
    (F : MinimalSpanningFamily P generator hspan) {i : G}
    (hi : i ∈ F.indices) :
    generator i ∉
      Submodule.span R (generator '' (F.indices.erase i : Set G)) := by
  intro hmem
  apply F.erase_not_span hi
  apply le_antisymm
  · calc
      Submodule.span R (generator '' (F.indices.erase i : Set G)) ≤
          Submodule.span R (generator '' (F.indices : Set G)) := by
        apply Submodule.span_mono
        rintro x ⟨j, hj, rfl⟩
        exact ⟨j, Finset.erase_subset _ _ hj, rfl⟩
      _ = P := F.span_eq
  · have hle : Submodule.span R (generator '' (F.indices : Set G)) ≤
        Submodule.span R (generator '' (F.indices.erase i : Set G)) := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, hj, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact hmem
      · apply Submodule.subset_span
        exact ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, rfl⟩
    simpa only [F.span_eq] using hle

lemma MinimalSpanningFamily.mem_span_erase_of_unit_relation
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype G] {P : Submodule R M} {generator : G → M}
    {hspan : Submodule.span R (Set.range generator) = P}
    (F : MinimalSpanningFamily P generator hspan) {i : G}
    (hi : i ∈ F.indices) (coeff : F.indices → R)
    (hunit : IsUnit (coeff ⟨i, hi⟩))
    (hrel : ∑ j, coeff j • generator j.1 = 0) :
    generator i ∈
      Submodule.span R (generator '' (F.indices.erase i : Set G)) := by
  let b : F.indices := ⟨i, hi⟩
  have hsum := Finset.sum_erase_add (Finset.univ : Finset F.indices)
    (fun j => coeff j • generator j.1) (Finset.mem_univ b)
  have hrest : (Finset.univ.erase b).sum (fun j => coeff j • generator j.1) +
      coeff b • generator b.1 = 0 := by
    rw [hsum]
    exact hrel
  have hmem : coeff b • generator b.1 ∈
      Submodule.span R (generator '' (F.indices.erase i : Set G)) := by
    have hterm : coeff b • generator b.1 =
        -((Finset.univ.erase b).sum (fun j => coeff j • generator j.1)) :=
      eq_neg_of_add_eq_zero_right hrest
    rw [hterm]
    apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
      (Submodule.span R (generator '' (F.indices.erase i : Set G)))
      (coeff j)
    apply Submodule.subset_span
    have hjb : j ≠ b := (Finset.mem_erase.mp hj).1
    exact ⟨j.1, Finset.mem_erase.mpr ⟨by
      intro hji
      apply hjb
      exact Subtype.ext hji, j.2⟩, rfl⟩
  simpa [b] using (Submodule.smul_mem_iff_of_isUnit _ hunit).mp hmem

structure GradedMinimalFreeComplex (I : Ideal (R3 k)) (e : ℕ)
    (hA : IsTypeTwoLevel I e) where
  β₁ : Type ub
  β₂ : Type ug
  β₃ : Type ud
  fintype₁ : Fintype β₁
  fintype₂ : Fintype β₂
  fintype₃ : Fintype β₃
  pShift : β₁ → ℕ
  qShift : β₂ → ℕ
  rShift : β₃ → ℕ
  d₁ : (β₁ → R3 k) →ₗ[R3 k] (Fin 2 → R3 k)
  d₂ : (β₂ → R3 k) →ₗ[R3 k] (β₁ → R3 k)
  d₃ : (β₃ → R3 k) →ₗ[R3 k] (β₂ → R3 k)
  d₁_range : LinearMap.range d₁ = inverseSystemKernel hA
  d₂_range : LinearMap.range d₂ = LinearMap.ker d₁
  d₃_range : LinearMap.range d₃ = LinearMap.ker d₂
  d₁_d₂ : d₁.comp d₂ = 0
  d₂_d₃ : d₂.comp d₃ = 0
  d₃_injective : Function.Injective d₃
  d₁_homogeneous : ∀ b i,
    MvPolynomial.IsHomogeneous (d₁ (Pi.single b 1) i) (pShift b)
  d₂_homogeneous : ∀ g b,
    if pShift b ≤ qShift g then
      MvPolynomial.IsHomogeneous (d₂ (Pi.single g 1) b) (qShift g - pShift b)
    else d₂ (Pi.single g 1) b = 0
  d₃_homogeneous : ∀ a g,
    if qShift g ≤ rShift a then
      MvPolynomial.IsHomogeneous (d₃ (Pi.single a 1) g) (rShift a - qShift g)
    else d₃ (Pi.single a 1) g = 0
  d₁_minimal : ∀ b i, d₁ (Pi.single b 1) i ∈ irrelevantIdeal k
  d₂_minimal : ∀ g b, d₂ (Pi.single g 1) b ∈ irrelevantIdeal k
  d₃_minimal : ∀ a g, d₃ (Pi.single a 1) g ∈ irrelevantIdeal k

/-! The first reduction is performed on the already homogeneous family from
`InverseSystem`: only its index set is thinned, so no degree information is lost. -/

noncomputable def minimalFirstRelations {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : HomogeneousFirstRelations hA := by
  classical
  let H := homogeneousFirstRelations hA
  letI : Fintype H.β := H.fintype
  let F := firstMinimalSpanningFamily hA
  let β := F.indices
  letI : Fintype β := inferInstance
  refine
    { β := β
      fintype := inferInstance
      degree := fun b => H.degree b.1
      generator := fun b => H.generator b.1
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro b i
    exact H.homogeneous b.1 i
  · intro b
    exact H.relation b.1
  · calc
      Submodule.span (R3 k) (Set.range (fun b : β => H.generator b.1)) =
          Submodule.span (R3 k) (H.generator '' (F.indices : Set H.β)) :=
        span_subtype_finset_range H.generator
      _ = inverseSystemKernel hA := F.span_eq

noncomputable def minimalSecondRelations
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (H : HomogeneousFirstRelations hA) : HomogeneousSecondRelations H := by
  classical
  letI : Fintype H.β := H.fintype
  let S := homogeneousSecondRelations H
  letI : Fintype S.γ := S.fintype
  let F := secondMinimalSpanningFamily H
  let γ := F.indices
  letI : Fintype γ := inferInstance
  refine
    { γ := γ
      fintype := inferInstance
      degree := fun g => S.degree g.1
      generator := fun g => S.generator g.1
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro g b
    exact S.homogeneous g.1 b
  · intro g
    exact S.relation g.1
  · calc
      Submodule.span (R3 k) (Set.range (fun g : γ => S.generator g.1)) =
          Submodule.span (R3 k) (S.generator '' (F.indices : Set S.γ)) :=
        span_subtype_finset_range S.generator
      _ = LinearMap.ker H.d₁ := F.span_eq

noncomputable def minimalThirdRelations
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    {H : HomogeneousFirstRelations hA}
    (S : HomogeneousSecondRelations H) : HomogeneousThirdRelations S := by
  classical
  letI : Fintype H.β := H.fintype
  letI : Fintype S.γ := S.fintype
  let T := homogeneousThirdRelations S
  letI : Fintype T.δ := T.fintype
  let F := thirdMinimalSpanningFamily S
  let δ := F.indices
  letI : Fintype δ := inferInstance
  refine
    { δ := δ
      fintype := inferInstance
      degree := fun a => T.degree a.1
      generator := fun a => T.generator a.1
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro a g
    exact T.homogeneous a.1 g
  · intro a
    exact T.relation a.1
  · calc
      Submodule.span (R3 k) (Set.range (fun a : δ => T.generator a.1)) =
          Submodule.span (R3 k) (T.generator '' (F.indices : Set T.δ)) :=
        span_subtype_finset_range T.generator
      _ = LinearMap.ker S.d₂ := F.span_eq

/-! The finite indexing sets above are subtypes of the original scratch
families.  For the homological argument it is useful to replace those
subtypes by `Fin` explicitly: all free modules then live in the universe of
the coefficient ring, so the ordinary `ModuleCat` projective-dimension API
can be applied without a universe lift. -/

noncomputable def minimalFirstRelationsFin {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) :
    HomogeneousFirstRelations.{uk, 0} hA := by
  classical
  let H := homogeneousFirstRelations hA
  letI : Fintype H.β := H.fintype
  let F := firstMinimalSpanningFamily hA
  let eF : F.indices ≃ Fin (Fintype.card F.indices) := Fintype.equivFin F.indices
  refine
    { β := Fin (Fintype.card F.indices)
      fintype := inferInstance
      degree := fun b => H.degree (eF.symm b).1
      generator := fun b => H.generator (eF.symm b).1
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro b i
    exact H.homogeneous (eF.symm b).1 i
  · intro b
    exact H.relation (eF.symm b).1
  · have hrange :
        Set.range (fun b : Fin (Fintype.card F.indices) => H.generator (eF.symm b).1) =
          Set.range (fun b : F.indices => H.generator b.1) := by
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨eF.symm b, rfl⟩
      · rintro ⟨b, rfl⟩
        exact ⟨eF b, by simp⟩
    calc
      Submodule.span (R3 k)
          (Set.range (fun b : Fin (Fintype.card F.indices) => H.generator (eF.symm b).1)) =
          Submodule.span (R3 k)
            (Set.range (fun b : F.indices => H.generator b.1)) := by rw [hrange]
      _ = Submodule.span (R3 k)
          (H.generator '' (F.indices : Set H.β)) :=
        span_subtype_finset_range H.generator
      _ = inverseSystemKernel hA := F.span_eq

noncomputable def minimalSecondRelationsFin
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (H : HomogeneousFirstRelations.{uk, 0} hA) :
    HomogeneousFirstRelations.HomogeneousSecondRelations.{uk, 0, 0} H := by
  classical
  letI : Fintype H.β := H.fintype
  let S := homogeneousSecondRelations H
  letI : Fintype S.γ := S.fintype
  let F := secondMinimalSpanningFamily H
  let eF : F.indices ≃ Fin (Fintype.card F.indices) := Fintype.equivFin F.indices
  refine
    { γ := Fin (Fintype.card F.indices)
      fintype := inferInstance
      degree := fun g => S.degree (eF.symm g).1
      generator := fun g => S.generator (eF.symm g).1
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro g b
    exact S.homogeneous (eF.symm g).1 b
  · intro g
    exact S.relation (eF.symm g).1
  · have hrange :
        Set.range (fun g : Fin (Fintype.card F.indices) => S.generator (eF.symm g).1) =
          Set.range (fun g : F.indices => S.generator g.1) := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨eF.symm g, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨eF g, by simp⟩
    calc
      Submodule.span (R3 k)
          (Set.range (fun g : Fin (Fintype.card F.indices) => S.generator (eF.symm g).1)) =
          Submodule.span (R3 k)
            (Set.range (fun g : F.indices => S.generator g.1)) := by rw [hrange]
      _ = Submodule.span (R3 k)
          (S.generator '' (F.indices : Set S.γ)) :=
        span_subtype_finset_range S.generator
      _ = LinearMap.ker H.d₁ := F.span_eq

noncomputable def minimalThirdRelationsFin
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    {H : HomogeneousFirstRelations.{uk, 0} hA}
    (S : HomogeneousFirstRelations.HomogeneousSecondRelations.{uk, 0, 0} H) :
    HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations.{uk, 0, 0, 0} S := by
  classical
  letI : Fintype H.β := H.fintype
  letI : Fintype S.γ := S.fintype
  let T := homogeneousThirdRelations S
  letI : Fintype T.δ := T.fintype
  let F := thirdMinimalSpanningFamily S
  let eF : F.indices ≃ Fin (Fintype.card F.indices) := Fintype.equivFin F.indices
  refine
    { δ := Fin (Fintype.card F.indices)
      fintype := inferInstance
      degree := fun a => T.degree (eF.symm a).1
      generator := fun a => T.generator (eF.symm a).1
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro a g
    exact T.homogeneous (eF.symm a).1 g
  · intro a
    exact T.relation (eF.symm a).1
  · have hrange :
        Set.range (fun a : Fin (Fintype.card F.indices) => T.generator (eF.symm a).1) =
          Set.range (fun a : F.indices => T.generator a.1) := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨eF.symm a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨eF a, by simp⟩
    calc
      Submodule.span (R3 k)
          (Set.range (fun a : Fin (Fintype.card F.indices) => T.generator (eF.symm a).1)) =
          Submodule.span (R3 k)
            (Set.range (fun a : F.indices => T.generator a.1)) := by rw [hrange]
      _ = Submodule.span (R3 k)
          (T.generator '' (F.indices : Set T.δ)) :=
        span_subtype_finset_range T.generator
      _ = LinearMap.ker S.d₂ := F.span_eq

/-! The third family needs the same shifted homogeneous decomposition that
`InverseSystem` supplies for the first two families.  It is used only to turn an
arbitrary relation into a degree-zero relation, where minimality detects a
unit coefficient. -/

namespace HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations

variable {I : Ideal (R3 k)} {e : ℕ}
  {hA : IsTypeTwoLevel I e}
  {H : HomogeneousFirstRelations hA}
  {S : HomogeneousSecondRelations H}

noncomputable def shiftedComponent (T : HomogeneousThirdRelations S) (q : ℕ)
    (c : T.δ → R3 k) : T.δ → R3 k := fun a =>
  if T.degree a ≤ q then
    MvPolynomial.homogeneousComponent (q - T.degree a) (c a) else 0

@[simp] lemma shiftedComponent_apply (T : HomogeneousThirdRelations S)
    (q : ℕ) (c : T.δ → R3 k) (a : T.δ) :
    shiftedComponent T q c a = if T.degree a ≤ q then
      MvPolynomial.homogeneousComponent (q - T.degree a) (c a) else 0 := rfl

noncomputable def shiftedTotalDegree (T : HomogeneousThirdRelations S)
    (c : T.δ → R3 k) : ℕ := by
  letI := T.fintype
  exact Finset.univ.sup fun a => T.degree a + MvPolynomial.totalDegree (c a)

lemma degree_add_totalDegree_le_shiftedTotalDegree
    (T : HomogeneousThirdRelations S) (c : T.δ → R3 k) (a : T.δ) :
    T.degree a + MvPolynomial.totalDegree (c a) ≤ T.shiftedTotalDegree c := by
  classical
  letI := T.fintype
  unfold shiftedTotalDegree
  exact Finset.le_sup (f := fun j => T.degree j + MvPolynomial.totalDegree (c j))
    (Finset.mem_univ a)

lemma sum_shiftedComponent (T : HomogeneousThirdRelations S)
    (c : T.δ → R3 k) :
    (∑ q ∈ Finset.range (T.shiftedTotalDegree c + 1),
      T.shiftedComponent q c) = c := by
  apply funext
  intro a
  simp only [Finset.sum_apply, shiftedComponent_apply]
  exact HomogeneousFirstRelations.sum_shifted_homogeneousComponent_to (c a)
    (T.degree_add_totalDegree_le_shiftedTotalDegree c a)

lemma d₃_shiftedComponent (T : HomogeneousThirdRelations S)
    (q : ℕ) (c : T.δ → R3 k) :
    T.d₃ (T.shiftedComponent q c) =
      S.shiftedComponent q (T.d₃ c) := by
  classical
  letI := T.fintype
  apply funext
  intro g
  rw [HomogeneousThirdRelations.d₃_apply,
    HomogeneousSecondRelations.shiftedComponent_apply,
    HomogeneousThirdRelations.d₃_apply]
  simp only [shiftedComponent_apply,
    HomogeneousSecondRelations.shiftedComponent_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hgq : S.degree g ≤ q
  · rw [if_pos hgq, map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hga : S.degree g ≤ T.degree a
    · have hhom := T.homogeneous a g
      rw [if_pos hga] at hhom
      by_cases haq : T.degree a ≤ q
      · rw [if_pos haq]
        have hsub : (q - S.degree g) - (T.degree a - S.degree g) =
            q - T.degree a := by omega
        rw [homogeneousComponent_mul_right hhom (by omega)]
        rw [hsub]
      · rw [if_neg haq, zero_mul]
        exact (homogeneousComponent_mul_right_eq_zero hhom (by omega)).symm
    · have hzero := T.homogeneous a g
      rw [if_neg hga] at hzero
      simp [hzero]
  · rw [if_neg hgq]
    apply Finset.sum_eq_zero
    intro a ha
    by_cases haq : T.degree a ≤ q
    · have hga : ¬ S.degree g ≤ T.degree a := by omega
      have hzero := T.homogeneous a g
      rw [if_neg hga] at hzero
      simp [haq, hzero]
    · simp [haq]

lemma ker_d₃_shiftedComponent_mem (T : HomogeneousThirdRelations S)
    (q : ℕ) {c : T.δ → R3 k} (hc : T.d₃ c = 0) :
    T.d₃ (T.shiftedComponent q c) = 0 := by
  have h := T.d₃_shiftedComponent q c
  rw [hc] at h
  simpa using h

end HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations

lemma isUnit_of_isHomogeneous_zero {f : R3 k}
    (hf : MvPolynomial.IsHomogeneous f 0) (hf0 : f ≠ 0) : IsUnit f := by
  have hdeg : MvPolynomial.totalDegree f = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3) (p := f)).mpr hf
  obtain ⟨c, hc⟩ : ∃ c : k, f = MvPolynomial.C c :=
    ⟨f.coeff 0, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg⟩
  have hc0 : c ≠ 0 := by
    intro h
    apply hf0
    rw [hc, h, map_zero]
  rw [hc]
  simpa only [MvPolynomial.algebraMap_eq] using
    (isUnit_iff_ne_zero.mpr hc0).map (MvPolynomial.C : k →+* R3 k)

lemma sum_indicator_attach
    {M G : Type*} [AddCommMonoid M] [Fintype G]
    (s : Finset G) (f : G → M) :
    (@Finset.univ G _).sum (fun a => if a ∈ s then f a else 0) =
      s.attach.sum (fun a => f a.1) := by
  classical
  have hfilter : (Finset.univ.filter (fun a : G => a ∈ s)) = s := by
    ext a
    simp
  calc
    (@Finset.univ G _).sum (fun a => if a ∈ s then f a else 0) =
        (Finset.univ.filter (fun a : G => a ∈ s)).sum f := by
      rw [Finset.sum_filter]
    _ = s.sum f := by rw [hfilter]
    _ = s.attach.sum (fun a => f a.1) := by
      symm
      exact s.sum_attach f

lemma first_minimal_relation_mem_irrelevant
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (H : HomogeneousFirstRelations hA)
    [fintypeH : Fintype H.β]
    {F : MinimalSpanningFamily (inverseSystemKernel hA) H.generator H.span_eq}
    (c : F.indices → R3 k)
    (hrel : ∑ a, c a • H.generator a.1 = 0) :
    ∀ a, c a ∈ irrelevantIdeal k := by
  classical
  let lift : H.β → R3 k := fun a =>
    if ha : a ∈ F.indices then c ⟨a, ha⟩ else 0
  have hlift_rel : (@Finset.univ H.β H.fintype).sum
      (fun a => lift a • H.generator a) = 0 := by
    have hrel' : F.indices.attach.sum
        (fun a => c a • H.generator a.1) = 0 := by
      simpa only [Finset.univ_eq_attach] using hrel
    calc
      (@Finset.univ H.β H.fintype).sum (fun a => lift a • H.generator a) =
          F.indices.attach.sum (fun a => c a • H.generator a.1) := by
        let f : H.β → (Fin 2 → R3 k) := fun a =>
          if ha : a ∈ F.indices then c ⟨a, ha⟩ • H.generator a else 0
        have hsum := @sum_indicator_attach (Fin 2 → R3 k) H.β _ H.fintype
          F.indices f
        calc
          (@Finset.univ H.β H.fintype).sum (fun a => lift a • H.generator a) =
              (@Finset.univ H.β H.fintype).sum
                (fun a => if ha : a ∈ F.indices then f a else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : a ∈ F.indices <;> simp [lift, f, h]
          _ = F.indices.attach.sum (fun a => f a.1) := hsum
          _ = F.indices.attach.sum (fun a => c a • H.generator a.1) := by
            apply Finset.sum_congr rfl
            intro a ha
            simp [f]
      _ = 0 := hrel'
  intro b
  by_contra hb
  have hdecomp : lift b.1 =
      ∑ q ∈ Finset.range (H.shiftedTotalDegree lift + 1),
        H.shiftedComponent q lift b.1 := by
    have hsum := congrFun (H.sum_shiftedComponent lift) b.1
    simpa only [Finset.sum_apply] using hsum.symm
  obtain ⟨q, hq, hqnot⟩ :
      ∃ q ∈ Finset.range (H.shiftedTotalDegree lift + 1),
        H.shiftedComponent q lift b.1 ∉ irrelevantIdeal k := by
    by_contra hnone
    push_neg at hnone
    apply hb
    have hbc : lift b.1 = c b := by simp [lift, b.2]
    rw [← hbc, hdecomp]
    apply Submodule.sum_mem
    intro q hq
    exact hnone q hq
  have hqdeg : H.degree b = q := by
    by_cases hle : H.degree b ≤ q
    · rw [HomogeneousFirstRelations.shiftedComponent_apply, if_pos hle] at hqnot
      by_contra hneq
      have hpos : 1 ≤ q - H.degree b := by omega
      have hhom := MvPolynomial.homogeneousComponent_isHomogeneous
        (q - H.degree b) (lift b.1)
      have hmem : MvPolynomial.homogeneousComponent (q - H.degree b) (lift b.1) ∈
          irrelevantIdeal k := by
        simpa [irrelevantIdeal, pow_one] using
          (isHomogeneous_mem_pow_idealOfVars hhom hpos)
      exact hqnot hmem
    · simp [HomogeneousFirstRelations.shiftedComponent, hle] at hqnot
  have hcomponent_hom :
      MvPolynomial.IsHomogeneous (H.shiftedComponent q lift b.1) 0 := by
    rw [HomogeneousFirstRelations.shiftedComponent_apply, if_pos (by omega)]
    simpa [hqdeg] using
      (MvPolynomial.isHomogeneous_C (Fin 3) (MvPolynomial.coeff 0 (lift b.1)))
  have hcomponent_ne : H.shiftedComponent q lift b.1 ≠ 0 := by
    intro hzero
    apply hqnot
    rw [hzero]
    exact Submodule.zero_mem _
  have hunit : IsUnit (H.shiftedComponent q lift b.1) :=
    isUnit_of_isHomogeneous_zero hcomponent_hom hcomponent_ne
  have hrel0 : H.d₁ lift = 0 := by
    change (@Finset.univ H.β H.fintype).sum
        (fun a => lift a • H.generator a) = 0
    exact hlift_rel
  have hrelq : H.d₁ (H.shiftedComponent q lift) = 0 :=
    H.ker_d₁_shiftedComponent_mem q hrel0
  have hrelq' : (@Finset.univ H.β H.fintype).sum
      (fun a => (H.shiftedComponent q lift) a • H.generator a) = 0 := by
    change (@Finset.univ H.β H.fintype).sum
        (fun a => (H.shiftedComponent q lift) a • H.generator a) = 0 at hrelq
    exact hrelq
  have hrelq'' : ∑ a : F.indices,
      (H.shiftedComponent q lift) a.1 • H.generator a.1 = 0 := by
    let f : H.β → (Fin 2 → R3 k) := fun a =>
      if ha : a ∈ F.indices then
        (H.shiftedComponent q lift) a • H.generator a else 0
    have hsum := @sum_indicator_attach (Fin 2 → R3 k) H.β _ H.fintype
      F.indices f
    have hfull : (@Finset.univ H.β H.fintype).sum
        (fun a => (H.shiftedComponent q lift) a • H.generator a) =
        (@Finset.univ H.β H.fintype).sum
          (fun a => if ha : a ∈ F.indices then f a else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a ∈ F.indices
      · simp [f, h]
      · simp [HomogeneousFirstRelations.shiftedComponent, lift, f, h]
    have hsum' : F.indices.attach.sum
        (fun a => (H.shiftedComponent q lift) a.1 • H.generator a.1) = 0 := by
      calc
        F.indices.attach.sum
            (fun a => (H.shiftedComponent q lift) a.1 • H.generator a.1) =
            F.indices.attach.sum (fun a => f a.1) := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [f]
        _ = (@Finset.univ H.β H.fintype).sum
            (fun a => if ha : a ∈ F.indices then f a else 0) := hsum.symm
        _ = (@Finset.univ H.β H.fintype).sum
            (fun a => (H.shiftedComponent q lift) a • H.generator a) := hfull.symm
        _ = 0 := hrelq'
    simpa only [Finset.univ_eq_attach] using hsum'
  have hmem := MinimalSpanningFamily.mem_span_erase_of_unit_relation F b.2
    (fun a => (H.shiftedComponent q lift) a.1) hunit hrelq''
  exact (MinimalSpanningFamily.not_mem_span_erase F b.2) hmem

lemma second_minimal_relation_mem_irrelevant
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    {H : HomogeneousFirstRelations hA}
    (S : HomogeneousSecondRelations H)
    [fintypeS : Fintype S.γ]
    {F : MinimalSpanningFamily (LinearMap.ker H.d₁) S.generator S.span_eq}
    (c : F.indices → R3 k)
    (hrel : ∑ a, c a • S.generator a.1 = 0) :
    ∀ a, c a ∈ irrelevantIdeal k := by
  classical
  let lift : S.γ → R3 k := fun a =>
    if ha : a ∈ F.indices then c ⟨a, ha⟩ else 0
  have hlift_rel : (@Finset.univ S.γ S.fintype).sum
      (fun a => lift a • S.generator a) = 0 := by
    have hrel' : F.indices.attach.sum
        (fun a => c a • S.generator a.1) = 0 := by
      simpa only [Finset.univ_eq_attach] using hrel
    calc
      (@Finset.univ S.γ S.fintype).sum (fun a => lift a • S.generator a) =
          F.indices.attach.sum (fun a => c a • S.generator a.1) := by
        let f : S.γ → (H.β → R3 k) := fun a =>
          if ha : a ∈ F.indices then c ⟨a, ha⟩ • S.generator a else 0
        have hsum := @sum_indicator_attach (H.β → R3 k) S.γ _ S.fintype
          F.indices f
        calc
          (@Finset.univ S.γ S.fintype).sum (fun a => lift a • S.generator a) =
              (@Finset.univ S.γ S.fintype).sum
                (fun a => if ha : a ∈ F.indices then f a else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : a ∈ F.indices <;> simp [lift, f, h]
          _ = F.indices.attach.sum (fun a => f a.1) := hsum
          _ = F.indices.attach.sum (fun a => c a • S.generator a.1) := by
            apply Finset.sum_congr rfl
            intro a ha
            simp [f]
      _ = 0 := hrel'
  intro b
  by_contra hb
  have hdecomp : lift b.1 =
      ∑ q ∈ Finset.range (S.shiftedTotalDegree lift + 1),
        S.shiftedComponent q lift b.1 := by
    have hsum := congrFun (S.sum_shiftedComponent lift) b.1
    simpa only [Finset.sum_apply] using hsum.symm
  obtain ⟨q, hq, hqnot⟩ :
      ∃ q ∈ Finset.range (S.shiftedTotalDegree lift + 1),
        S.shiftedComponent q lift b.1 ∉ irrelevantIdeal k := by
    by_contra hnone
    push_neg at hnone
    apply hb
    have hbc : lift b.1 = c b := by simp [lift, b.2]
    rw [← hbc, hdecomp]
    apply Submodule.sum_mem
    intro q hq
    exact hnone q hq
  have hqdeg : S.degree b = q := by
    by_cases hle : S.degree b ≤ q
    · rw [HomogeneousFirstRelations.HomogeneousSecondRelations.shiftedComponent_apply,
        if_pos hle] at hqnot
      by_contra hneq
      have hpos : 1 ≤ q - S.degree b := by omega
      have hhom := MvPolynomial.homogeneousComponent_isHomogeneous
        (q - S.degree b) (lift b.1)
      have hmem : MvPolynomial.homogeneousComponent (q - S.degree b) (lift b.1) ∈
          irrelevantIdeal k := by
        simpa [irrelevantIdeal, pow_one] using
          (isHomogeneous_mem_pow_idealOfVars hhom hpos)
      exact hqnot hmem
    · simp [HomogeneousFirstRelations.HomogeneousSecondRelations.shiftedComponent,
        hle] at hqnot
  have hcomponent_hom :
      MvPolynomial.IsHomogeneous (S.shiftedComponent q lift b.1) 0 := by
    rw [HomogeneousFirstRelations.HomogeneousSecondRelations.shiftedComponent_apply,
      if_pos (by omega)]
    simpa [hqdeg] using
      (MvPolynomial.isHomogeneous_C (Fin 3) (MvPolynomial.coeff 0 (lift b.1)))
  have hcomponent_ne : S.shiftedComponent q lift b.1 ≠ 0 := by
    intro hzero
    apply hqnot
    rw [hzero]
    exact Submodule.zero_mem _
  have hunit : IsUnit (S.shiftedComponent q lift b.1) :=
    isUnit_of_isHomogeneous_zero hcomponent_hom hcomponent_ne
  have hrel0 : S.d₂ lift = 0 := by
    change (@Finset.univ S.γ S.fintype).sum
        (fun a => lift a • S.generator a) = 0
    exact hlift_rel
  have hrelq : S.d₂ (S.shiftedComponent q lift) = 0 :=
    S.ker_d₂_shiftedComponent_mem q hrel0
  have hrelq' : (@Finset.univ S.γ S.fintype).sum
      (fun a => (S.shiftedComponent q lift) a • S.generator a) = 0 := by
    change (@Finset.univ S.γ S.fintype).sum
        (fun a => (S.shiftedComponent q lift) a • S.generator a) = 0 at hrelq
    exact hrelq
  have hrelq'' : ∑ a : F.indices,
      (S.shiftedComponent q lift) a.1 • S.generator a.1 = 0 := by
    let f : S.γ → (H.β → R3 k) := fun a =>
      if ha : a ∈ F.indices then
        (S.shiftedComponent q lift) a • S.generator a else 0
    have hsum := @sum_indicator_attach (H.β → R3 k) S.γ _ S.fintype
      F.indices f
    have hfull : (@Finset.univ S.γ S.fintype).sum
        (fun a => (S.shiftedComponent q lift) a • S.generator a) =
        (@Finset.univ S.γ S.fintype).sum
          (fun a => if ha : a ∈ F.indices then f a else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a ∈ F.indices
      · simp [f, h]
      · simp [HomogeneousFirstRelations.HomogeneousSecondRelations.shiftedComponent,
          lift, f, h]
    have hsum' : F.indices.attach.sum
        (fun a => (S.shiftedComponent q lift) a.1 • S.generator a.1) = 0 := by
      calc
        F.indices.attach.sum
            (fun a => (S.shiftedComponent q lift) a.1 • S.generator a.1) =
            F.indices.attach.sum (fun a => f a.1) := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [f]
        _ = (@Finset.univ S.γ S.fintype).sum
            (fun a => if ha : a ∈ F.indices then f a else 0) := hsum.symm
        _ = (@Finset.univ S.γ S.fintype).sum
            (fun a => (S.shiftedComponent q lift) a • S.generator a) := hfull.symm
        _ = 0 := hrelq'
    simpa only [Finset.univ_eq_attach] using hsum'
  have hmem := MinimalSpanningFamily.mem_span_erase_of_unit_relation F b.2
    (fun a => (S.shiftedComponent q lift) a.1) hunit hrelq''
  exact (MinimalSpanningFamily.not_mem_span_erase F b.2) hmem

lemma inverseSystemKernel_no_constant
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    {u : Fin 2 → R3 k}
    (hu : inverseSystemMap hA u = 0)
    (hhom : ∀ i, MvPolynomial.IsHomogeneous (u i) 0) :
    u = 0 := by
  let coeff : Fin 2 → k := fun i => u i |>.coeff 0
  have huC : ∀ i, u i = MvPolynomial.C (coeff i) := by
    intro i
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3) (p := u i)).mpr
        (hhom i))
  have hsumM : ∑ i : Fin 2,
      (MvPolynomial.C (coeff i) : R3 k) • matlisGenerator hA i = 0 := by
    simpa only [inverseSystemMap_apply, huC, Pi.zero_apply] using hu
  have hsum : ∑ i : Fin 2, coeff i • (matlisTopBasis hA i) = 0 := by
    apply Subtype.ext
    change ∑ i : Fin 2, coeff i • matlisGenerator hA i = 0
    simpa only [matlisDual_C_smul] using hsumM
  have hcoeff : ∀ i : Fin 2, coeff i = 0 := by
    exact (Fintype.linearIndependent_iff.mp (matlisTopBasis hA).linearIndependent)
      coeff hsum
  funext i
  simpa [huC i, hcoeff i]

lemma second_syzygy_projective
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    {H : HomogeneousFirstRelations.{uk, 0} hA}
    (S : HomogeneousSecondRelations.{uk, 0, 0} H) :
    Module.Projective (R3 k) (LinearMap.ker S.d₂) := by
  classical
  letI : Small.{uk, uk} k := small_max k
  letI : Fintype H.β := H.fintype
  letI : Fintype S.γ := S.fintype
  let R := R3 k
  let K0 := LinearMap.ker (inverseSystemMap hA)
  let f0 : (Fin 2 → R) →ₗ[R] MatlisDual I := inverseSystemMap hA
  let f1 : (H.β → R) →ₗ[R] K0 :=
    H.d₁.codRestrict K0 (by
      intro c
      have hc := congrArg (fun f => f c) H.inverseSystemMap_comp_d₁
      exact LinearMap.mem_ker.mpr (by simpa [LinearMap.comp_apply] using hc))
  let K1 := LinearMap.ker H.d₁
  let f2 : (S.γ → R) →ₗ[R] K1 :=
    S.d₂.codRestrict K1 (by
      intro c
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun f => f c) S.d₁_comp_d₂
      simpa [LinearMap.comp_apply] using hc)
  have hf0 : Function.Surjective f0 := inverseSystemMap_surjective hA
  have hf1 : Function.Surjective f1 := by
    intro y
    have hy : y.1 ∈ LinearMap.range H.d₁ := by
      rw [H.range_d₁_eq_kernel]
      exact y.2
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc
  have hf2 : Function.Surjective f2 := by
    intro y
    have hy : y.1 ∈ LinearMap.ker H.d₁ := by
      exact y.2
    have hy' : y.1 ∈ LinearMap.range S.d₂ := by
      rw [S.range_d₂_eq_kernel]
      exact hy
    obtain ⟨c, hc⟩ := hy'
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc
  let C0 : ShortComplex (ModuleCat.{uk} R) :=
    ShortComplex.mk (ModuleCat.ofHom.{uk} (LinearMap.ker f0).subtype)
      (ModuleCat.ofHom.{uk} f0) (by
        ext
        simp)
  let C1 : ShortComplex (ModuleCat.{uk} R) :=
    ShortComplex.mk
      (ModuleCat.ofHom.{uk} (LinearMap.ker H.d₁).subtype)
      (ModuleCat.ofHom.{uk} f1) (by
        ext
        simp [f1, LinearMap.comp_apply])
  let C2 : ShortComplex (ModuleCat.{uk} R) :=
    ShortComplex.mk
      (ModuleCat.ofHom.{uk} (LinearMap.ker S.d₂).subtype)
      (ModuleCat.ofHom.{uk} f2) (by
        ext
        simp [f2, LinearMap.comp_apply, S.d₁_comp_d₂])
  have hC0 : C0.ShortExact := by
    change f0.shortComplexKer.ShortExact
    exact LinearMap.shortExact_shortComplexKer hf0
  have hker_f1 : LinearMap.ker f1 = LinearMap.ker H.d₁ := by
    apply Submodule.ext
    intro c
    constructor
    · intro hc
      exact LinearMap.mem_ker.mpr (by
        have := congrArg Subtype.val (LinearMap.mem_ker.mp hc)
        exact this)
    · intro hc
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact LinearMap.mem_ker.mp hc
  have hC1 : C1.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · change Function.Exact (LinearMap.ker H.d₁).subtype f1
      rw [LinearMap.exact_iff, Submodule.range_subtype, hker_f1]
    · exact (LinearMap.ker H.d₁).injective_subtype
    · exact hf1
  have hker_f2 : LinearMap.ker f2 = LinearMap.ker S.d₂ := by
    apply Submodule.ext
    intro c
    constructor
    · intro hc
      exact LinearMap.mem_ker.mpr (by
        have := congrArg Subtype.val (LinearMap.mem_ker.mp hc)
        exact this)
    · intro hc
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact LinearMap.mem_ker.mp hc
  have hC2 : C2.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · change Function.Exact (LinearMap.ker S.d₂).subtype f2
      rw [LinearMap.exact_iff, Submodule.range_subtype, hker_f2]
    · exact (LinearMap.ker S.d₂).injective_subtype
    · exact hf2
  letI : CategoryTheory.Projective
      (ModuleCat.of R (Fin 2 → R)) :=
    ModuleCat.projective_of_free (Pi.basisFun R (Fin 2))
  letI : CategoryTheory.Projective
      (ModuleCat.of R (H.β → R)) :=
    ModuleCat.projective_of_free (Pi.basisFun R H.β)
  letI : CategoryTheory.Projective
      (ModuleCat.of R (S.γ → R)) :=
    ModuleCat.projective_of_free (Pi.basisFun R S.γ)
  have hM : HasProjectiveDimensionLT
      (ModuleCat.of R (MatlisDual I)) 4 := by
    exact r3_projectiveDimensionLE (k := k)
      (M := ModuleCat.of R (MatlisDual I))
  have hK0 : HasProjectiveDimensionLT
      (ModuleCat.of R K0) 3 :=
    hC0.hasProjectiveDimensionLT_X₁ (n := 3) (by infer_instance) hM
  have hK1 : HasProjectiveDimensionLT
      (ModuleCat.of R K1) 2 :=
    hC1.hasProjectiveDimensionLT_X₁ (n := 2) (by infer_instance) hK0
  have hK2 : HasProjectiveDimensionLT
      (ModuleCat.of R (LinearMap.ker S.d₂)) 1 :=
    hC2.hasProjectiveDimensionLT_X₁ (n := 1) (by infer_instance) hK1
  exact (IsProjective.iff_projective (R := R) _).mpr
    (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr hK2)

/-! A direct summand of a finite free polynomial module cannot be contained
in the irrelevant ideal.  This is the small graded-local argument needed to
turn projectivity of the last syzygy into injectivity of its minimal
generating map.  The determinant proof avoids imposing a false global
local-ring instance on the polynomial ring. -/

lemma idempotent_mem_irrelevant_eq_zero
    {ι : Type*} [Fintype ι]
    (r : (ι → R3 k) →ₗ[R3 k] (ι → R3 k))
    (hidem : r.comp r = r)
    (hmem : ∀ i j, r (Pi.single j 1) i ∈ irrelevantIdeal k) :
    r = 0 := by
  classical
  let b : Basis ι (R3 k) (ι → R3 k) := Pi.basisFun (R3 k) ι
  let A : Matrix ι ι (R3 k) := LinearMap.toMatrix b b r
  have hA : A * A = A := by
    have hcomp := LinearMap.toMatrix_comp b b b r r
    rw [hidem] at hcomp
    simpa [A] using hcomp.symm
  let B : Matrix ι ι (R3 k) := 1 - A
  have hB : B * B = B := by
    dsimp [B]
    calc
      (1 - A) * (1 - A) = 1 - A - A + A * A := by noncomm_ring
      _ = 1 - A := by rw [hA]; abel
  have hdetB : Matrix.det B = 1 := by
    have hdetidem : (Matrix.det B) ^ 2 = Matrix.det B := by
      rw [pow_two, ← Matrix.det_mul, hB]
    obtain hzero | hone := eq_zero_or_one_of_sq_eq_self hdetidem
    · let ε : R3 k →+* k :=
        MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 3 => 0)
      have hεA : ∀ i j, ε (A i j) = 0 := by
        intro i j
        have hc : MvPolynomial.coeff 0 (r (Pi.single j 1) i) = 0 :=
          (MvPolynomial.mem_pow_idealOfVars_iff' 1
            (r (Pi.single j 1) i)).mp
            (by simpa [irrelevantIdeal] using hmem i j) 0 (by simp)
        have heval : ε (r (Pi.single j 1) i) = 0 := by
          simp [ε, MvPolynomial.eval₂Hom_zero_apply,
            MvPolynomial.constantCoeff_eq, hc]
        simpa [A, b, LinearMap.toMatrix_apply] using heval
      have hε : ε (Matrix.det B) = 1 := by
        rw [RingHom.map_det]
        have hmat : ε.mapMatrix B = 1 := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp [B, hεA]
          · simp [B, hij, hεA]
        rw [hmat, Matrix.det_one]
      rw [hzero] at hε
      simpa using hε
    · exact hone
  have hBunit : IsUnit B := by
    apply (Matrix.isUnit_iff_isUnit_det B).mpr
    rw [hdetB]
    exact isUnit_one
  have hA0 : A = 0 := by
    have hprod : (1 - B) * B = 0 := by
      rw [sub_mul, one_mul, hB]
      abel
    have hsub : 1 - B = 0 := by
      apply hBunit.mul_right_cancel
      simpa using hprod
    simpa [B] using hsub
  apply LinearMap.ext
  intro c
  have hc : (∑ j : ι, c j • Pi.single j 1) = c := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro i hij
      simp [hij]
  rw [← hc, map_sum]
  simp only [map_smul]
  apply Finset.sum_eq_zero
  intro j hj
  have hcol : r (Pi.single j 1) = 0 := by
    apply funext
    intro i
    have hz := congrFun (congrFun hA0 i) j
    simpa [A, LinearMap.toMatrix_apply, b] using hz
  rw [hcol, smul_zero]

lemma third_minimal_relation_mem_irrelevant
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    {H : HomogeneousFirstRelations hA}
    {S : HomogeneousSecondRelations H}
    (T : HomogeneousThirdRelations S)
    [fintypeT : Fintype T.δ]
    {F : MinimalSpanningFamily (LinearMap.ker S.d₂) T.generator T.span_eq}
    (c : F.indices → R3 k)
    (hrel : ∑ a, c a • T.generator a.1 = 0) :
    ∀ a, c a ∈ irrelevantIdeal k := by
  classical
  let lift : T.δ → R3 k := fun a =>
    if ha : a ∈ F.indices then c ⟨a, ha⟩ else 0
  have hlift_rel : (@Finset.univ T.δ T.fintype).sum
      (fun a => lift a • T.generator a) = 0 := by
    have hrel' : F.indices.attach.sum
        (fun a => c a • T.generator a.1) = 0 := by
      simpa only [Finset.univ_eq_attach] using hrel
    calc
      (@Finset.univ T.δ T.fintype).sum (fun a => lift a • T.generator a) =
          F.indices.attach.sum (fun a => c a • T.generator a.1) := by
        let f : T.δ → (S.γ → R3 k) := fun a =>
          if ha : a ∈ F.indices then c ⟨a, ha⟩ • T.generator a else 0
        have hsum := @sum_indicator_attach (S.γ → R3 k) T.δ _ T.fintype
          F.indices f
        calc
          (@Finset.univ T.δ T.fintype).sum (fun a => lift a • T.generator a) =
              (@Finset.univ T.δ T.fintype).sum
                (fun a => if ha : a ∈ F.indices then f a else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : a ∈ F.indices <;> simp [lift, f, h]
          _ = F.indices.attach.sum (fun a => f a.1) := hsum
          _ = F.indices.attach.sum (fun a => c a • T.generator a.1) := by
            apply Finset.sum_congr rfl
            intro a ha
            simp [f]
      _ = 0 := hrel'
  intro b
  by_contra hb
  have hdecomp : lift b.1 =
      ∑ q ∈ Finset.range (T.shiftedTotalDegree lift + 1),
        T.shiftedComponent q lift b.1 := by
    have hsum := congrFun (T.sum_shiftedComponent lift) b.1
    simpa only [Finset.sum_apply] using hsum.symm
  obtain ⟨q, hq, hqnot⟩ :
      ∃ q ∈ Finset.range (T.shiftedTotalDegree lift + 1),
        T.shiftedComponent q lift b.1 ∉ irrelevantIdeal k := by
    by_contra hnone
    push_neg at hnone
    apply hb
    have hbc : lift b.1 = c b := by simp [lift, b.2]
    rw [← hbc, hdecomp]
    apply Submodule.sum_mem
    intro q hq
    exact hnone q hq
  have hqdeg : T.degree b = q := by
    by_cases hle : T.degree b ≤ q
    · rw [HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations.shiftedComponent_apply,
        if_pos hle] at hqnot
      by_contra hneq
      have hpos : 1 ≤ q - T.degree b := by omega
      have hhom := MvPolynomial.homogeneousComponent_isHomogeneous
        (q - T.degree b) (lift b.1)
      have hmem : MvPolynomial.homogeneousComponent (q - T.degree b) (lift b.1) ∈
          irrelevantIdeal k := by
        simpa [irrelevantIdeal, pow_one] using
          (isHomogeneous_mem_pow_idealOfVars hhom hpos)
      exact hqnot hmem
    · simp [HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations.shiftedComponent,
        hle] at hqnot
  have hcomponent_hom :
      MvPolynomial.IsHomogeneous (T.shiftedComponent q lift b.1) 0 := by
    rw [HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations.shiftedComponent_apply,
      if_pos (by omega)]
    simpa [hqdeg] using
      (MvPolynomial.isHomogeneous_C (Fin 3) (MvPolynomial.coeff 0 (lift b.1)))
  have hcomponent_ne : T.shiftedComponent q lift b.1 ≠ 0 := by
    intro hzero
    apply hqnot
    rw [hzero]
    exact Submodule.zero_mem _
  have hunit : IsUnit (T.shiftedComponent q lift b.1) :=
    isUnit_of_isHomogeneous_zero hcomponent_hom hcomponent_ne
  have hrel0 : T.d₃ lift = 0 := by
    change (@Finset.univ T.δ T.fintype).sum
        (fun a => lift a • T.generator a) = 0
    exact hlift_rel
  have hrelq : T.d₃ (T.shiftedComponent q lift) = 0 :=
    T.ker_d₃_shiftedComponent_mem q hrel0
  have hrelq' : (@Finset.univ T.δ T.fintype).sum
      (fun a => (T.shiftedComponent q lift) a • T.generator a) = 0 := by
    change (@Finset.univ T.δ T.fintype).sum
        (fun a => (T.shiftedComponent q lift) a • T.generator a) = 0 at hrelq
    exact hrelq
  have hrelq'' : ∑ a : F.indices,
      (T.shiftedComponent q lift) a.1 • T.generator a.1 = 0 := by
    let f : T.δ → (S.γ → R3 k) := fun a =>
      if ha : a ∈ F.indices then
        (T.shiftedComponent q lift) a • T.generator a else 0
    have hsum := @sum_indicator_attach (S.γ → R3 k) T.δ _ T.fintype
      F.indices f
    have hfull : (@Finset.univ T.δ T.fintype).sum
        (fun a => (T.shiftedComponent q lift) a • T.generator a) =
        (@Finset.univ T.δ T.fintype).sum
          (fun a => if ha : a ∈ F.indices then f a else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a ∈ F.indices
      · simp [f, h]
      · simp [HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations.shiftedComponent,
          lift, f, h]
    have hsum' : F.indices.attach.sum
        (fun a => (T.shiftedComponent q lift) a.1 • T.generator a.1) = 0 := by
      calc
        F.indices.attach.sum
            (fun a => (T.shiftedComponent q lift) a.1 • T.generator a.1) =
            F.indices.attach.sum (fun a => f a.1) := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [f]
        _ = (@Finset.univ T.δ T.fintype).sum
            (fun a => if ha : a ∈ F.indices then f a else 0) := hsum.symm
        _ = (@Finset.univ T.δ T.fintype).sum
            (fun a => (T.shiftedComponent q lift) a • T.generator a) := hfull.symm
        _ = 0 := hrelq'
    simpa only [Finset.univ_eq_attach] using hsum'
  have hmem := MinimalSpanningFamily.mem_span_erase_of_unit_relation F b.2
    (fun a => (T.shiftedComponent q lift) a.1) hunit hrelq''
  exact (MinimalSpanningFamily.not_mem_span_erase F b.2) hmem

lemma minimalThirdFin_relation_mem_irrelevant
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    {H : HomogeneousFirstRelations.{uk, 0} hA}
    (S : HomogeneousSecondRelations.{uk, 0, 0} H) :
    letI : Fintype H.β := H.fintype
    letI : Fintype S.γ := S.fintype
    let T := homogeneousThirdRelations S
    letI : Fintype T.δ := T.fintype
    let F := thirdMinimalSpanningFamily S
    let eF : F.indices ≃ Fin (Fintype.card F.indices) :=
      Fintype.equivFin F.indices
    ∀ (c : Fin (Fintype.card F.indices) → R3 k),
      (∑ a, c a • (minimalThirdRelationsFin S).generator a = 0) →
        ∀ a, c a ∈ irrelevantIdeal k := by
  classical
  dsimp
  intro c hrel
  letI : Fintype H.β := H.fintype
  letI : Fintype S.γ := S.fintype
  let T := homogeneousThirdRelations S
  letI : Fintype T.δ := T.fintype
  let F := thirdMinimalSpanningFamily S
  let eF : F.indices ≃ Fin (Fintype.card F.indices) :=
    Fintype.equivFin F.indices
  let c' : F.indices → R3 k := fun a => c (eF a)
  have hsum :
      ∑ a : F.indices, c' a • T.generator a.1 =
        ∑ b : Fin (Fintype.card F.indices),
          c b • (minimalThirdRelationsFin S).generator b := by
    apply Fintype.sum_equiv eF
    intro a
    simp [c', T, F, eF, minimalThirdRelationsFin]
  have hraw : ∑ a : F.indices, c' a • T.generator a.1 = 0 := by
    rw [hsum, hrel]
  have hmem := third_minimal_relation_mem_irrelevant T c' hraw
  intro a
  simpa [c'] using hmem (eF.symm a)

lemma minimalFirstFin_generator_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (b : (minimalFirstRelationsFin hA).β) :
    (minimalFirstRelationsFin hA).generator b ≠ 0 := by
  classical
  let H0 := homogeneousFirstRelations hA
  letI : Fintype H0.β := H0.fintype
  let F := firstMinimalSpanningFamily hA
  let eF : F.indices ≃ Fin (Fintype.card F.indices) :=
    Fintype.equivFin F.indices
  have hgen :
      H0.generator (eF.symm b).1 ≠ 0 := by
    intro hb
    have hmem :
        H0.generator (eF.symm b).1 ∈
          Submodule.span (R3 k)
            (H0.generator '' (F.indices.erase (eF.symm b).1 : Set H0.β)) := by
      rw [hb]
      exact Submodule.zero_mem _
    exact (MinimalSpanningFamily.not_mem_span_erase F (eF.symm b).2) hmem
  simpa [minimalFirstRelationsFin, H0, F, eF] using hgen

lemma minimalSecondFin_generator_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (g : (minimalSecondRelationsFin (minimalFirstRelationsFin hA)).γ) :
    (minimalSecondRelationsFin (minimalFirstRelationsFin hA)).generator g ≠ 0 := by
  classical
  let H := minimalFirstRelationsFin hA
  letI : Fintype H.β := H.fintype
  let S := minimalSecondRelationsFin H
  letI : Fintype (homogeneousSecondRelations H).γ :=
    (homogeneousSecondRelations H).fintype
  let F := secondMinimalSpanningFamily H
  let eF : F.indices ≃ Fin (Fintype.card F.indices) :=
    Fintype.equivFin F.indices
  have hgen :
      (homogeneousSecondRelations H).generator (eF.symm g).1 ≠ 0 := by
    intro hg
    have hmem :
        (homogeneousSecondRelations H).generator (eF.symm g).1 ∈
          Submodule.span (R3 k)
            ((homogeneousSecondRelations H).generator ''
              (F.indices.erase (eF.symm g).1 : Set _)) := by
      rw [hg]
      exact Submodule.zero_mem _
    exact (MinimalSpanningFamily.not_mem_span_erase F (eF.symm g).2) hmem
  simpa [minimalSecondRelationsFin, S, F, eF] using hgen

lemma minimalThirdFin_generator_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (a : (minimalThirdRelationsFin
      (minimalSecondRelationsFin (minimalFirstRelationsFin hA))).δ) :
    (minimalThirdRelationsFin
      (minimalSecondRelationsFin (minimalFirstRelationsFin hA))).generator a ≠ 0 := by
  classical
  let H := minimalFirstRelationsFin hA
  letI : Fintype H.β := H.fintype
  let S := minimalSecondRelationsFin H
  letI : Fintype (homogeneousSecondRelations H).γ :=
    (homogeneousSecondRelations H).fintype
  let T := minimalThirdRelationsFin S
  letI : Fintype (homogeneousThirdRelations S).δ :=
    (homogeneousThirdRelations S).fintype
  let F := thirdMinimalSpanningFamily S
  let eF : F.indices ≃ Fin (Fintype.card F.indices) :=
    Fintype.equivFin F.indices
  have hgen :
      (homogeneousThirdRelations S).generator (eF.symm a).1 ≠ 0 := by
    intro hg
    have hmem :
        (homogeneousThirdRelations S).generator (eF.symm a).1 ∈
          Submodule.span (R3 k)
            ((homogeneousThirdRelations S).generator ''
              (F.indices.erase (eF.symm a).1 : Set _)) := by
      rw [hg]
      exact Submodule.zero_mem _
    exact (MinimalSpanningFamily.not_mem_span_erase F (eF.symm a).2) hmem
  simpa [minimalThirdRelationsFin, T, F, eF] using hgen

lemma minimalSecondFin_entry_mem_irrelevant
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    let H := minimalFirstRelationsFin hA
    letI : Fintype H.β := H.fintype
    let S := minimalSecondRelationsFin H
    letI : Fintype S.γ := S.fintype
    ∀ g b, S.d₂ (Pi.single g 1) b ∈ irrelevantIdeal k := by
  classical
  dsimp
  let H := minimalFirstRelationsFin hA
  letI : Fintype H.β := H.fintype
  let S := minimalSecondRelationsFin H
  letI : Fintype S.γ := S.fintype
  let H0 := homogeneousFirstRelations hA
  letI : Fintype H0.β := H0.fintype
  let S0 := homogeneousSecondRelations H
  letI : Fintype S0.γ := S0.fintype
  let F1 := firstMinimalSpanningFamily hA
  let e1 : F1.indices ≃ Fin (Fintype.card F1.indices) :=
    Fintype.equivFin F1.indices
  let F2 := secondMinimalSpanningFamily H
  let e2 : F2.indices ≃ Fin (Fintype.card F2.indices) :=
    Fintype.equivFin F2.indices
  intro g b
  let rawg : S0.γ := (e2.symm g).1
  let c : F1.indices → R3 k := fun a => S0.generator rawg (e1 a)
  have hrel : ∑ a : F1.indices, c a • H0.generator a.1 = 0 := by
    have hr := S0.relation rawg
    rw [LinearMap.mem_ker] at hr
    have hsum :
        ∑ a : F1.indices, c a • H0.generator a.1 =
          ∑ x : H.β, S0.generator rawg x • H.generator x := by
      apply Fintype.sum_equiv e1
      intro a
      simp [c, H, H0, F1, e1, minimalFirstRelationsFin]
    rw [hsum]
    simpa [HomogeneousFirstRelations.d₁_apply] using hr
  have hm := first_minimal_relation_mem_irrelevant H0 c hrel
  have hb := hm (e1.symm b)
  have hsingle : S.d₂ (Pi.single g 1) = S.generator g := by
    change (∑ x : S.γ, Pi.single g 1 x • S.generator x) = S.generator g
    calc
      (∑ x : S.γ, Pi.single g 1 x • S.generator x) =
          Pi.single g 1 g • S.generator g := by
        apply Fintype.sum_eq_single g
        intro x hx
        simp [Pi.single, hx]
      _ = S.generator g := by simp
  change S.d₂ (Pi.single g 1) b ∈ irrelevantIdeal k
  rw [hsingle]
  simpa [S, S0, rawg, c, e1, e2, minimalSecondRelationsFin] using hb

lemma minimalThirdFin_entry_mem_irrelevant
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    let H := minimalFirstRelationsFin hA
    letI : Fintype H.β := H.fintype
    let S := minimalSecondRelationsFin H
    letI : Fintype S.γ := S.fintype
    let T := minimalThirdRelationsFin S
    letI : Fintype T.δ := T.fintype
    letI : DecidableEq T.δ := Classical.decEq _
    ∀ a g, T.d₃ (Pi.single a 1) g ∈ irrelevantIdeal k := by
  classical
  dsimp
  let H := minimalFirstRelationsFin hA
  letI : Fintype H.β := H.fintype
  let S := minimalSecondRelationsFin H
  letI : Fintype S.γ := S.fintype
  let T := minimalThirdRelationsFin S
  letI : Fintype T.δ := T.fintype
  let S0 := homogeneousSecondRelations H
  letI : Fintype S0.γ := S0.fintype
  let T0 := homogeneousThirdRelations S
  letI : Fintype T0.δ := T0.fintype
  let F2 := secondMinimalSpanningFamily H
  let e2 : F2.indices ≃ Fin (Fintype.card F2.indices) :=
    Fintype.equivFin F2.indices
  let F3 := thirdMinimalSpanningFamily S
  let e3 : F3.indices ≃ Fin (Fintype.card F3.indices) :=
    Fintype.equivFin F3.indices
  intro a g
  let rawa : T0.δ := (e3.symm a).1
  let c : F2.indices → R3 k := fun x => T0.generator rawa (e2 x)
  have hrel : ∑ x : F2.indices, c x • S0.generator x.1 = 0 := by
    have hr := T0.relation rawa
    rw [LinearMap.mem_ker] at hr
    have hsum :
        ∑ x : F2.indices, c x • S0.generator x.1 =
          ∑ y : S.γ, T0.generator rawa y • S.generator y := by
      apply Fintype.sum_equiv e2
      intro x
      simp [c, S, S0, F2, e2, minimalSecondRelationsFin]
    rw [hsum]
    simpa [HomogeneousSecondRelations.d₂_apply] using hr
  have hm := second_minimal_relation_mem_irrelevant S0 c hrel
  have hg := hm (e2.symm g)
  have hsingle : T.d₃ (Pi.single a 1) = T.generator a := by
    change (∑ x : T.δ, Pi.single a 1 x • T.generator x) = T.generator a
    calc
      (∑ x : T.δ, Pi.single a 1 x • T.generator x) =
          Pi.single a 1 a • T.generator a := by
        apply Fintype.sum_eq_single a
        intro b hb
        simp [Pi.single, hb]
      _ = T.generator a := by simp
  change T.d₃ (Pi.single a 1) g ∈ irrelevantIdeal k
  rw [hsingle]
  simpa [T, T0, rawa, c, e2, e3, minimalThirdRelationsFin] using hg

namespace GradedMinimalFreeComplex

variable {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}

noncomputable def ofLevel
    {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) :
    GradedMinimalFreeComplex.{uk, 0, 0, 0} I e hA := by
  classical
  let H := minimalFirstRelationsFin hA
  letI : Fintype H.β := H.fintype
  let S := minimalSecondRelationsFin H
  letI : Fintype S.γ := S.fintype
  let T := minimalThirdRelationsFin S
  letI : Fintype T.δ := T.fintype
  have hHsingle (b : H.β) : H.d₁ (Pi.single b 1) = H.generator b := by
    change (∑ x : H.β, Pi.single b 1 x • H.generator x) = H.generator b
    calc
      (∑ x : H.β, Pi.single b 1 x • H.generator x) =
          Pi.single b 1 b • H.generator b := by
        apply Fintype.sum_eq_single b
        intro x hx
        simp [Pi.single, hx]
      _ = H.generator b := by simp
  have hSsingle (g : S.γ) : S.d₂ (Pi.single g 1) = S.generator g := by
    change (∑ x : S.γ, Pi.single g 1 x • S.generator x) = S.generator g
    calc
      (∑ x : S.γ, Pi.single g 1 x • S.generator x) =
          Pi.single g 1 g • S.generator g := by
        apply Fintype.sum_eq_single g
        intro x hx
        simp [Pi.single, hx]
      _ = S.generator g := by simp
  have hTsingle (a : T.δ) : T.d₃ (Pi.single a 1) = T.generator a := by
    change (∑ x : T.δ, Pi.single a 1 x • T.generator x) = T.generator a
    calc
      (∑ x : T.δ, Pi.single a 1 x • T.generator x) =
          Pi.single a 1 a • T.generator a := by
        apply Fintype.sum_eq_single a
        intro x hx
        simp [Pi.single, hx]
      _ = T.generator a := by simp
  have hd3_injective : Function.Injective T.d₃ := by
    let K2 := LinearMap.ker S.d₂
    letI : Module.Projective (R3 k) K2 := second_syzygy_projective S
    let d3K : (T.δ → R3 k) →ₗ[R3 k] K2 :=
      T.d₃.codRestrict K2 (by
        intro c
        apply LinearMap.mem_ker.mpr
        have hc := congrArg (fun f => f c) T.d₂_comp_d₃
        simpa [LinearMap.comp_apply] using hc)
    have hd3K_surj : Function.Surjective d3K := by
      intro y
      have hy : (y : S.γ → R3 k) ∈ LinearMap.range T.d₃ := by
        rw [T.range_d₃_eq_kernel]
        exact y.property
      obtain ⟨c, hc⟩ := hy
      refine ⟨c, ?_⟩
      apply Subtype.ext
      exact hc
    obtain ⟨sec, hsec⟩ :=
      d3K.exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr hd3K_surj)
    have hsec_apply (y : K2) : d3K (sec y) = y := by
      have hy := congrArg (fun f => f y) hsec
      simpa [LinearMap.comp_apply] using hy
    let r : (T.δ → R3 k) →ₗ[R3 k] (T.δ → R3 k) :=
      LinearMap.id - sec.comp d3K
    have hrcomp : d3K.comp r = 0 := by
      ext c
      simp [r, LinearMap.comp_apply, hsec_apply]
    have hidem : r.comp r = r := by
      ext c
      simp [r, LinearMap.comp_apply, hsec_apply]
    have hmem : ∀ i j, r (Pi.single j 1) i ∈ irrelevantIdeal k := by
      intro i j
      have hrel : T.d₃ (r (Pi.single j 1)) = 0 := by
        have hz := congrArg (fun f => f (Pi.single j 1)) hrcomp
        have hz' := congrArg Subtype.val hz
        simpa [d3K, LinearMap.comp_apply] using hz'
      have hrel' :
          ∑ a : T.δ, r (Pi.single j 1) a • T.generator a = 0 := by
        simpa [HomogeneousThirdRelations.d₃_apply] using hrel
      have hthird := minimalThirdFin_relation_mem_irrelevant S
      have hcoeff := hthird (r (Pi.single j 1)) hrel' i
      exact hcoeff
    have hrzero : r = 0 := idempotent_mem_irrelevant_eq_zero r hidem hmem
    have hker : ∀ c, T.d₃ c = 0 → c = 0 := by
      intro c hc
      have hdc : d3K c = 0 := by
        apply Subtype.ext
        simpa [d3K] using hc
      have hrc : r c = c := by
        simp [r, hdc]
      rw [hrzero] at hrc
      simpa using hrc.symm
    intro c₁ c₂ h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, h, sub_self]
  refine
    { β₁ := H.β
      β₂ := S.γ
      β₃ := T.δ
      fintype₁ := H.fintype
      fintype₂ := S.fintype
      fintype₃ := T.fintype
      pShift := H.degree
      qShift := S.degree
      rShift := T.degree
      d₁ := H.d₁
      d₂ := S.d₂
      d₃ := T.d₃
      d₁_range := H.range_d₁_eq_kernel
      d₂_range := S.range_d₂_eq_kernel
      d₃_range := T.range_d₃_eq_kernel
      d₁_d₂ := S.d₁_comp_d₂
      d₂_d₃ := T.d₂_comp_d₃
      d₃_injective := hd3_injective
      d₁_homogeneous := ?_
      d₂_homogeneous := ?_
      d₃_homogeneous := ?_
      d₁_minimal := ?_
      d₂_minimal := ?_
      d₃_minimal := ?_ }
  · intro b i
    rw [hHsingle b]
    exact H.homogeneous b i
  · intro g b
    by_cases hle : H.degree b ≤ S.degree g
    · rw [if_pos hle, hSsingle g]
      have hh := S.homogeneous g b
      rw [if_pos hle] at hh
      exact hh
    · rw [if_neg hle, hSsingle g]
      have hh := S.homogeneous g b
      rw [if_neg hle] at hh
      exact hh
  · intro a g
    by_cases hle : S.degree g ≤ T.degree a
    · rw [if_pos hle, hTsingle a]
      have hh := T.homogeneous a g
      rw [if_pos hle] at hh
      exact hh
    · rw [if_neg hle, hTsingle a]
      have hh := T.homogeneous a g
      rw [if_neg hle] at hh
      exact hh
  · intro b i
    rw [hHsingle b]
    by_cases hdeg : H.degree b = 0
    · have hvec : H.generator b = 0 := by
        apply inverseSystemKernel_no_constant hA
        · exact LinearMap.mem_ker.mp (H.relation b)
        · intro j
          simpa [hdeg] using H.homogeneous b j
      exfalso
      apply minimalFirstFin_generator_ne_zero hA b
      simpa [H] using hvec
    · have hpos : 1 ≤ H.degree b := by omega
      simpa [irrelevantIdeal, pow_one] using
        (isHomogeneous_mem_pow_idealOfVars (H.homogeneous b i) hpos)
  · intro g b
    have hmin := minimalSecondFin_entry_mem_irrelevant hA
    exact hmin g b
  · intro a g
    have hmin := minimalThirdFin_entry_mem_irrelevant hA
    exact hmin a g

noncomputable def firstBasis (C : GradedMinimalFreeComplex I e hA) :
    Basis C.β₁ (R3 k) (C.β₁ → R3 k) := by
  letI := C.fintype₁
  exact Pi.basisFun (R3 k) C.β₁

noncomputable def secondBasis (C : GradedMinimalFreeComplex I e hA) :
    Basis C.β₂ (R3 k) (C.β₂ → R3 k) := by
  letI := C.fintype₂
  exact Pi.basisFun (R3 k) C.β₂

noncomputable def thirdBasis (C : GradedMinimalFreeComplex I e hA) :
    Basis C.β₃ (R3 k) (C.β₃ → R3 k) := by
  letI := C.fintype₃
  exact Pi.basisFun (R3 k) C.β₃

@[simp] lemma firstBasis_apply (C : GradedMinimalFreeComplex I e hA) (b : C.β₁) :
    C.firstBasis b = Pi.single b 1 := by
  letI := C.fintype₁
  simp [firstBasis]

@[simp] lemma secondBasis_apply (C : GradedMinimalFreeComplex I e hA) (g : C.β₂) :
    C.secondBasis g = Pi.single g 1 := by
  letI := C.fintype₂
  simp [secondBasis]

@[simp] lemma thirdBasis_apply (C : GradedMinimalFreeComplex I e hA) (a : C.β₃) :
    C.thirdBasis a = Pi.single a 1 := by
  letI := C.fintype₃
  simp [thirdBasis]

lemma presentation_exact (C : GradedMinimalFreeComplex I e hA) :
    LinearMap.range C.d₁ = LinearMap.ker (inverseSystemMap hA) := by
  exact C.d₁_range

lemma first_free (C : GradedMinimalFreeComplex I e hA) :
    Module.Free (R3 k) (C.β₁ → R3 k) := by
  letI := C.fintype₁
  infer_instance

lemma second_free (C : GradedMinimalFreeComplex I e hA) :
    Module.Free (R3 k) (C.β₂ → R3 k) := by
  letI := C.fintype₂
  infer_instance

lemma third_free (C : GradedMinimalFreeComplex I e hA) :
    Module.Free (R3 k) (C.β₃ → R3 k) := by
  letI := C.fintype₃
  infer_instance

lemma first_finite (C : GradedMinimalFreeComplex I e hA) :
    Module.Finite (R3 k) (C.β₁ → R3 k) := by
  letI := C.fintype₁
  infer_instance

lemma second_finite (C : GradedMinimalFreeComplex I e hA) :
    Module.Finite (R3 k) (C.β₂ → R3 k) := by
  letI := C.fintype₂
  infer_instance

lemma third_finite (C : GradedMinimalFreeComplex I e hA) :
    Module.Finite (R3 k) (C.β₃ → R3 k) := by
  letI := C.fintype₃
  infer_instance

lemma first_range_minimal (C : GradedMinimalFreeComplex I e hA) :
    LinearMap.range C.d₁ ≤
      irrelevantIdeal k • (⊤ : Submodule (R3 k) (Fin 2 → R3 k)) := by
  letI := C.fintype₁
  apply range_le_smul_top_of_entries C.d₁ (irrelevantIdeal k)
  exact C.d₁_minimal

lemma second_range_minimal (C : GradedMinimalFreeComplex I e hA) :
    LinearMap.range C.d₂ ≤
      irrelevantIdeal k • (⊤ : Submodule (R3 k) (C.β₁ → R3 k)) := by
  letI := C.fintype₁
  letI := C.fintype₂
  apply range_le_smul_top_of_entries C.d₂ (irrelevantIdeal k)
  exact C.d₂_minimal

lemma third_range_minimal (C : GradedMinimalFreeComplex I e hA) :
    LinearMap.range C.d₃ ≤
      irrelevantIdeal k • (⊤ : Submodule (R3 k) (C.β₂ → R3 k)) := by
  letI := C.fintype₂
  letI := C.fintype₃
  apply range_le_smul_top_of_entries C.d₃ (irrelevantIdeal k)
  exact C.d₃_minimal

/-! The shift functions induce the Betti multiplicities used by the
resolution numerics.  Since the indices are finite, these are genuine
finite shift multisets rather than arbitrary integer-valued functions. -/

noncomputable def pMultiplicity (C : GradedMinimalFreeComplex I e hA) : ℤ → ℤ := by
  letI := C.fintype₁
  exact shiftMultiplicity (fun b => (C.pShift b : ℤ))

noncomputable def qMultiplicity (C : GradedMinimalFreeComplex I e hA) : ℤ → ℤ := by
  letI := C.fintype₂
  exact shiftMultiplicity (fun g => (C.qShift g : ℤ))

noncomputable def rMultiplicity (C : GradedMinimalFreeComplex I e hA) : ℤ → ℤ := by
  letI := C.fintype₃
  exact shiftMultiplicity (fun a => (C.rShift a : ℤ))

lemma pMultiplicity_nonneg (C : GradedMinimalFreeComplex I e hA) (b : ℤ) :
    0 ≤ C.pMultiplicity b := by
  letI := C.fintype₁
  exact shiftMultiplicity_nonneg _ _

lemma qMultiplicity_nonneg (C : GradedMinimalFreeComplex I e hA) (b : ℤ) :
    0 ≤ C.qMultiplicity b := by
  letI := C.fintype₂
  exact shiftMultiplicity_nonneg _ _

lemma rMultiplicity_nonneg (C : GradedMinimalFreeComplex I e hA) (b : ℤ) :
    0 ≤ C.rMultiplicity b := by
  letI := C.fintype₃
  exact shiftMultiplicity_nonneg _ _

noncomputable def thirdKernelEquiv (C : GradedMinimalFreeComplex I e hA) :
    (C.β₃ → R3 k) ≃ₗ[R3 k] LinearMap.ker C.d₂ :=
  (LinearEquiv.ofInjective C.d₃ C.d₃_injective).trans
    (LinearEquiv.ofEq _ _ C.d₃_range)

noncomputable def thirdKernelBasis (C : GradedMinimalFreeComplex I e hA) :
    Basis C.β₃ (R3 k) (LinearMap.ker C.d₂) :=
  C.thirdBasis.map C.thirdKernelEquiv

lemma third_kernel_free (C : GradedMinimalFreeComplex I e hA) :
    Module.Free (R3 k) (LinearMap.ker C.d₂) := by
  exact Module.Free.of_basis C.thirdKernelBasis

lemma third_kernel_finite (C : GradedMinimalFreeComplex I e hA) :
    Module.Finite (R3 k) (LinearMap.ker C.d₂) := by
  letI := C.fintype₃
  exact Module.Finite.of_basis C.thirdKernelBasis

lemma third_kernel_finrank (C : GradedMinimalFreeComplex I e hA) :
    Module.finrank (R3 k) (LinearMap.ker C.d₂) =
      @Fintype.card C.β₃ C.fintype₃ := by
  letI := C.fintype₃
  exact Module.finrank_eq_card_basis C.thirdKernelBasis

@[reducible] noncomputable def firstRelations (C : GradedMinimalFreeComplex I e hA) :
    HomogeneousFirstRelations hA := by
  refine
    { β := C.β₁
      fintype := C.fintype₁
      degree := C.pShift
      generator := fun b => C.d₁ (Pi.single b 1)
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro b i
    exact C.d₁_homogeneous b i
  · intro b
    have hb : C.d₁ (Pi.single b 1) ∈ LinearMap.range C.d₁ :=
      ⟨Pi.single b 1, rfl⟩
    rw [C.d₁_range] at hb
    exact hb
  · letI := C.fintype₁
    rw [span_columns_eq_range, C.d₁_range]

lemma firstRelations_d₁_eq (C : GradedMinimalFreeComplex I e hA) :
    C.firstRelations.d₁ = C.d₁ := by
  letI := C.firstRelations.fintype
  apply LinearMap.ext
  intro c
  have hc : (∑ b, c b • Pi.single b 1) = c := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro b hbj
      simp [hbj]
  have hsingle (b : C.firstRelations.β) :
      C.firstRelations.d₁ (Pi.single b 1) = C.firstRelations.generator b := by
    rw [HomogeneousFirstRelations.d₁_apply]
    simp
  calc
    C.firstRelations.d₁ c =
        C.firstRelations.d₁ (∑ b, c b • Pi.single b 1) := by rw [hc]
    _ = ∑ b, c b • C.firstRelations.d₁ (Pi.single b 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ b, c b • C.d₁ (Pi.single b 1) := by
      simp only [hsingle]
    _ = C.d₁ (∑ b, c b • Pi.single b 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = C.d₁ c := by rw [hc]

@[reducible] noncomputable def secondRelations (C : GradedMinimalFreeComplex I e hA) :
    HomogeneousSecondRelations C.firstRelations := by
  letI := C.fintype₁
  letI := C.firstRelations.fintype
  refine
    { γ := C.β₂
      fintype := C.fintype₂
      degree := C.qShift
      generator := fun g => C.d₂ (Pi.single g 1)
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro g b
    exact C.d₂_homogeneous g b
  · intro g
    rw [LinearMap.mem_ker, C.firstRelations_d₁_eq]
    change C.d₁ (C.d₂ (Pi.single g 1)) = 0
    have hg := congrArg (fun f => f (Pi.single g 1)) C.d₁_d₂
    simpa [LinearMap.comp_apply] using hg
  · letI := C.fintype₂
    change Submodule.span (R3 k) (Set.range (fun g => C.d₂ (Pi.single g 1))) =
      LinearMap.ker C.firstRelations.d₁
    rw [span_columns_eq_range, C.d₂_range, C.firstRelations_d₁_eq]

lemma secondRelations_d₂_eq (C : GradedMinimalFreeComplex I e hA) :
    C.secondRelations.d₂ = C.d₂ := by
  letI := C.firstRelations.fintype
  letI := C.secondRelations.fintype
  apply LinearMap.ext
  intro c
  have hc : (∑ g, c g • Pi.single g 1) = c := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro g hgj
      simp [hgj]
  have hsingle (g : C.secondRelations.γ) :
      C.secondRelations.d₂ (Pi.single g 1) = C.secondRelations.generator g := by
    rw [HomogeneousSecondRelations.d₂_apply]
    simp
  calc
    C.secondRelations.d₂ c =
        C.secondRelations.d₂ (∑ g, c g • Pi.single g 1) := by rw [hc]
    _ = ∑ g, c g • C.secondRelations.d₂ (Pi.single g 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ g, c g • C.d₂ (Pi.single g 1) := by
      simp only [hsingle]
    _ = C.d₂ (∑ g, c g • Pi.single g 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = C.d₂ c := by rw [hc]

/-! The FormalDeps input is used at the last syzygy itself, not only while
constructing the minimal complex.  The third kernel is projective over the
three-variable polynomial ring; `third_kernel_free` below is the concrete
finite minimal model used by the graded construction. -/

lemma third_kernel_projective
    (C : GradedMinimalFreeComplex.{uk, 0, 0, 0} I e hA) :
    Module.Projective (R3 k) (LinearMap.ker C.d₂) := by
  rw [← C.secondRelations_d₂_eq]
  exact second_syzygy_projective C.secondRelations

@[reducible] noncomputable def thirdRelations (C : GradedMinimalFreeComplex I e hA) :
    HomogeneousThirdRelations C.secondRelations := by
  letI := C.fintype₁
  letI := C.fintype₂
  letI := C.firstRelations.fintype
  letI := C.secondRelations.fintype
  refine
    { δ := C.β₃
      fintype := C.fintype₃
      degree := C.rShift
      generator := fun a => C.d₃ (Pi.single a 1)
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro a g
    exact C.d₃_homogeneous a g
  · intro a
    rw [LinearMap.mem_ker, C.secondRelations_d₂_eq]
    change C.d₂ (C.d₃ (Pi.single a 1)) = 0
    have ha := congrArg (fun f => f (Pi.single a 1)) C.d₂_d₃
    simpa [LinearMap.comp_apply] using ha
  · letI := C.fintype₃
    change Submodule.span (R3 k) (Set.range (fun a => C.d₃ (Pi.single a 1))) =
      LinearMap.ker C.secondRelations.d₂
    rw [span_columns_eq_range, C.d₃_range, C.secondRelations_d₂_eq]

lemma thirdRelations_d₃_eq (C : GradedMinimalFreeComplex I e hA) :
    C.thirdRelations.d₃ = C.d₃ := by
  letI := C.secondRelations.fintype
  letI := C.thirdRelations.fintype
  apply LinearMap.ext
  intro c
  have hc : (∑ a, c a • Pi.single a 1) = c := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro a haj
      simp [haj]
  have hsingle (a : C.thirdRelations.δ) :
      C.thirdRelations.d₃ (Pi.single a 1) = C.thirdRelations.generator a := by
    rw [HomogeneousThirdRelations.d₃_apply]
    simp
  calc
    C.thirdRelations.d₃ c =
        C.thirdRelations.d₃ (∑ a, c a • Pi.single a 1) := by rw [hc]
    _ = ∑ a, c a • C.thirdRelations.d₃ (Pi.single a 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ a, c a • C.d₃ (Pi.single a 1) := by
      simp only [hsingle]
    _ = C.d₃ (∑ a, c a • Pi.single a 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = C.d₃ c := by rw [hc]

noncomputable def toHomogeneousFreeComplexData (C : GradedMinimalFreeComplex I e hA) :
    HomogeneousFreeComplexData I e hA :=
  { first := C.firstRelations
    second := C.secondRelations
    third := C.thirdRelations }

end GradedMinimalFreeComplex

/-! ## Localized Euler bookkeeping

After tensoring a graded free resolution with the fraction field, the
finite-dimensional complex has the form

`0 → K^(m₃) → K^(m₂) → K^(m₁) → K² → 0`.

The following interface isolates the exact rank calculation.  It is useful
even before choosing polynomial bases: once the third kernel is known to be
free, this lemma is the step which forces its rank to be one. -/

structure LocalizedThreeStepResolution (K : Type*) [Field K]
    (m₃ m₂ m₁ : ℕ) where
  d₃ : (Fin m₃ → K) →ₗ[K] (Fin m₂ → K)
  d₂ : (Fin m₂ → K) →ₗ[K] (Fin m₁ → K)
  d₁ : (Fin m₁ → K) →ₗ[K] (Fin 2 → K)
  d₃_injective : Function.Injective d₃
  exact₃₂ : LinearMap.range d₃ = LinearMap.ker d₂
  exact₂₁ : LinearMap.range d₂ = LinearMap.ker d₁
  d₁_surjective : Function.Surjective d₁

namespace LocalizedThreeStepResolution

variable {K : Type*} [Field K] {m₃ m₂ m₁ : ℕ}

lemma euler_characteristic (E : LocalizedThreeStepResolution K m₃ m₂ m₁) :
    m₃ + m₁ = m₂ + 2 := by
  have h₃ := LinearMap.finrank_range_add_finrank_ker E.d₃
  have h₂ := LinearMap.finrank_range_add_finrank_ker E.d₂
  have h₁ := LinearMap.finrank_range_add_finrank_ker E.d₁
  have hker₃ : LinearMap.ker E.d₃ = ⊥ :=
    LinearMap.ker_eq_bot.mpr E.d₃_injective
  have hrange₁ : LinearMap.range E.d₁ = ⊤ :=
    LinearMap.range_eq_top.mpr E.d₁_surjective
  rw [hker₃, finrank_bot,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h₃
  rw [← E.exact₃₂] at h₂
  rw [← E.exact₂₁] at h₁
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h₂ h₁
  rw [hrange₁, finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h₁
  omega

lemma third_rank_eq_one_of_euler (E : LocalizedThreeStepResolution K m₃ m₂ m₁)
    (hEuler : m₁ = m₂ + 1) : m₃ = 1 := by
  have h := E.euler_characteristic
  omega

lemma third_kernel_finrank (E : LocalizedThreeStepResolution K m₃ m₂ m₁) :
    finrank K (LinearMap.ker E.d₂) = m₃ := by
  rw [← E.exact₃₂]
  have h := LinearMap.finrank_range_add_finrank_ker E.d₃
  rw [LinearMap.ker_eq_bot.mpr E.d₃_injective, finrank_bot,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, add_zero] at h
  exact h

lemma third_kernel_finrank_eq_one_of_euler
    (E : LocalizedThreeStepResolution K m₃ m₂ m₁)
    (hEuler : m₁ = m₂ + 1) :
    finrank K (LinearMap.ker E.d₂) = 1 := by
  rw [E.third_kernel_finrank, E.third_rank_eq_one_of_euler hEuler]

lemma third_kernel_basis_fin_one_of_euler
    (E : LocalizedThreeStepResolution K m₃ m₂ m₁)
    (hEuler : m₁ = m₂ + 1) :
    Nonempty (Basis (Fin 1) K (LinearMap.ker E.d₂)) := by
  letI : FiniteDimensional K (LinearMap.ker E.d₂) :=
    FiniteDimensional.of_injective (LinearMap.ker E.d₂).subtype
      (LinearMap.ker E.d₂).injective_subtype
  exact ⟨Module.finBasisOfFinrankEq K _
    (E.third_kernel_finrank_eq_one_of_euler hEuler)⟩

end LocalizedThreeStepResolution

namespace GradedResolutionDuality

variable {I : Ideal (R3 k)} {e : ℕ}
variable {β₁ : Type ub} {β₂ : Type ug} [Fintype β₁] [Fintype β₂]

noncomputable def localizedδ₁
    (D : GradedResolutionDuality I e β₁ β₂) :
    (β₁ → FractionRing (R3 k)) →ₗ[FractionRing (R3 k)]
      (Fin 2 → FractionRing (R3 k)) :=
  Fintype.linearCombination (FractionRing (R3 k))
    (fun i z => algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i z))

@[simp] lemma localizedδ₁_apply
    (D : GradedResolutionDuality I e β₁ β₂)
    (c : β₁ → FractionRing (R3 k)) :
    D.localizedδ₁ c = ∑ i, c i •
      (fun z => algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i z)) := rfl

lemma localizedδ₁_comp_δ₂
    (D : GradedResolutionDuality I e β₁ β₂) :
    D.localizedδ₁.comp D.δ₂ = 0 := by
  classical
  apply LinearMap.ext
  intro c
  rw [LinearMap.comp_apply, δ₂_apply, localizedδ₁_apply]
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply]
  change (∑ i, (∑ j, c j • D.δ₂K j i) •
      algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i z)) = 0
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  simp_rw [smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]
  have hz := congrFun (D.δ₁δ₂ j) z
  have hz' : (∑ x, D.δ₂K j x *
      algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ x z)) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hz
  rw [hz', mul_zero]

/-! The circuit is the coefficient vector of the last differential after
localization.  Giving it a named interface makes the full-support assertion
and its consequence for every proper subfamily available independently of
the numerical bridge. -/

noncomputable def lastDifferentialVector
    (D : GradedResolutionDuality I e β₁ β₂) : β₂ → FractionRing (R3 k) :=
  D.circuit

lemma lastDifferentialVector_full
    (D : GradedResolutionDuality I e β₁ β₂) (j : β₂) :
    D.lastDifferentialVector j ≠ 0 :=
  D.circuit_full j

lemma lastDifferentialVector_dependency
    (D : GradedResolutionDuality I e β₁ β₂) :
    D.δ₂ D.lastDifferentialVector = 0 := by
  rw [δ₂_apply]
  simpa [lastDifferentialVector] using D.circuit_dependency

lemma lastDifferentialVector_eq_generator
    (D : GradedResolutionDuality I e β₁ β₂) (j : β₂) :
    D.lastDifferentialVector j =
      algebraMap (R3 k) (FractionRing (R3 k)) (D.idealGenerator j) :=
  D.circuit_eq_generator j

lemma proper_subfamily_delta₂
    (D : GradedResolutionDuality I e β₁ β₂) (s : Finset β₂)
    (hs : s ≠ Finset.univ) :
    LinearIndependent (FractionRing (R3 k))
      (fun j : s => D.δ₂K j.1) := by
  apply proper_subfamily_linearIndependent
    (f := fun j => D.δ₂K j) (c := D.lastDifferentialVector)
    D.kernel_line D.lastDifferentialVector_full s hs

lemma critical_branch_equation8
    (D : GradedResolutionDuality I e β₁ β₂) (P : D.ResolutionPackage)
    (d : ℤ) (hd : 2 ≤ d) (hde : d ≤ (e : ℤ))
    (hr : D.resolutionRank d = 1) (hp : D.p d = 0)
    (hΔ : reversedHilb I e d - 2 * reversedHilb I e (d - 1) +
      reversedHilb I e (d - 2) = 1) :
    ∃ C : CriticalBranchCertificate D d, ∀ t : ℤ, d - 2 ≤ t → t ≤ d →
      reversedHilb I e t = 2 * Nz t - Nz (t - (C.a : ℤ)) +
        hilb C.Ann (t - (C.a : ℤ)) := by
  obtain ⟨C⟩ := P.critical d hd hde hr hp hΔ
  exact ⟨C, C.equation8⟩

end GradedResolutionDuality

/-! A free rank-one module has an actual one-element basis, not merely
projective dimension zero.  This is the small freeness conclusion consumed
by the last-differential construction. -/

lemma exists_basis_fin_one_of_free_rank_one
    {R M : Type*} [CommRing R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (h : Module.finrank R M = 1) : Nonempty (Basis (Fin 1) R M) := by
  obtain ⟨ι, b⟩ := Module.Free.exists_basis R M
  obtain ⟨hu⟩ := b.nonempty_unique_index_of_finrank_eq_one h
  letI := hu
  exact ⟨b.reindex (Equiv.ofUnique _ _)⟩

namespace GradedMinimalFreeComplex

variable {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}

lemma third_kernel_basis_fin_one (C : GradedMinimalFreeComplex I e hA)
    (hcard : @Fintype.card C.β₃ C.fintype₃ = 1) :
    Nonempty (Basis (Fin 1) (R3 k) (LinearMap.ker C.d₂)) := by
  letI : Module.Free (R3 k) (LinearMap.ker C.d₂) := C.third_kernel_free
  letI : Module.Finite (R3 k) (LinearMap.ker C.d₂) := C.third_kernel_finite
  apply exists_basis_fin_one_of_free_rank_one
  rw [C.third_kernel_finrank, hcard]

end GradedMinimalFreeComplex

/-! A compact certificate for the graded Nakayama step.  The generators are
recorded together with their homogeneous shifts and with the exact statement
that their residue classes span the corresponding quotient by the irrelevant
ideal.  The final equality is proved by the ordinary Nakayama lemma in the
completion theorem, so this is not a numerical stand-in for minimality. -/

structure GradedNakayamaCertificate (R M G : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Fintype G] where
  irrelevant : Ideal R
  generator : G → M
  span : Submodule.span R (Set.range generator) = ⊤
  residueIndependent :
    ∀ c : G → R,
      (∑ i, c i • generator i) ∈ irrelevant • (⊤ : Submodule R M) →
        ∀ i, c i ∈ irrelevant

structure HomogeneousMinimalGenerators
    (R M G : Type*) (isHomogeneous : G → M → Prop)
    [CommRing R] [AddCommGroup M] [Module R M] [Fintype G] where
  irrelevant : Ideal R
  degree : G → ℕ
  generator : G → M
  homogeneous : ∀ g, isHomogeneous g (generator g)
  span : Submodule.span R (Set.range generator) = ⊤
  residueIndependent :
    ∀ c : G → R,
      (∑ i, c i • generator i) ∈ irrelevant • (⊤ : Submodule R M) →
        ∀ i, c i ∈ irrelevant

namespace GradedNakayamaCertificate

variable {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype G]

/-! The coefficient map and its residue map are the actual maps behind the
certificate.  Keeping them explicit lets the graded Nakayama statement be
used as a kernel/range theorem, rather than only as a record of hypotheses. -/

noncomputable def generatorMap (N : GradedNakayamaCertificate R M G) :
    (G → R) →ₗ[R] M :=
  Fintype.linearCombination R N.generator

@[simp] lemma generatorMap_apply (N : GradedNakayamaCertificate R M G)
    (c : G → R) :
    N.generatorMap c = ∑ i, c i • N.generator i := rfl

lemma generatorMap_range_eq_top (N : GradedNakayamaCertificate R M G) :
    LinearMap.range N.generatorMap = (⊤ : Submodule R M) := by
  calc
    LinearMap.range N.generatorMap =
        Submodule.span R (Set.range (fun i => N.generatorMap (Pi.single i 1))) :=
      (span_columns_eq_range N.generatorMap).symm
    _ = Submodule.span R (Set.range N.generator) := by
      congr 1
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, by simp [generatorMap]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, by simp [generatorMap]⟩
    _ = ⊤ := N.span

noncomputable def residueMap (N : GradedNakayamaCertificate R M G) :
    (G → R) →ₗ[R]
      M ⧸ (N.irrelevant • (⊤ : Submodule R M)) :=
  (N.irrelevant • (⊤ : Submodule R M)).mkQ.comp N.generatorMap

lemma residueMap_surjective (N : GradedNakayamaCertificate R M G) :
    Function.Surjective N.residueMap := by
  have hgen : Function.Surjective N.generatorMap :=
    LinearMap.range_eq_top.mp N.generatorMap_range_eq_top
  intro y
  obtain ⟨m, hm⟩ := (N.irrelevant • (⊤ : Submodule R M)).mkQ_surjective y
  obtain ⟨c, hc⟩ := hgen m
  refine ⟨c, ?_⟩
  change (N.irrelevant • (⊤ : Submodule R M)).mkQ (N.generatorMap c) = y
  rw [hc]
  exact hm

lemma residueMap_ker_eq_smul_top (N : GradedNakayamaCertificate R M G) :
    LinearMap.ker N.residueMap =
      N.irrelevant • (⊤ : Submodule R (G → R)) := by
  apply le_antisymm
  · intro c hc
    have hmem : N.generatorMap c ∈
        N.irrelevant • (⊤ : Submodule R M) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact LinearMap.mem_ker.mp hc
    have hcoeff : ∀ i, c i ∈ N.irrelevant := by
      exact N.residueIndependent c hmem
    have hsum : (∑ i, c i • Pi.single i 1) = c := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fintype.sum_eq_single j]
      · simp
      · intro i hij
        simp [hij]
    rw [← hsum]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem_smul (hcoeff i) Submodule.mem_top
  · intro c hc
    apply LinearMap.mem_ker.mpr
    change (N.irrelevant • (⊤ : Submodule R M)).mkQ (N.generatorMap c) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine Submodule.smul_induction_on hc ?_ ?_
    · intro r hr m hm
      rw [N.generatorMap.map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x y hx hy
      rw [N.generatorMap.map_add]
      exact (N.irrelevant • (⊤ : Submodule R M)).add_mem hx hy

lemma mem_smul_top_iff_coeff (J : Ideal R) (c : G → R) :
    c ∈ J • (⊤ : Submodule R (G → R)) ↔ ∀ i, c i ∈ J := by
  constructor
  · intro hc
    refine Submodule.smul_induction_on hc ?_ ?_
    · intro r hr v hv i
      change r * v i ∈ J
      simpa [mul_comm] using J.mul_mem_left (v i) hr
    · intro x y hx hy i
      exact J.add_mem (hx i) (hy i)
  · intro hc
    have hsum : (∑ i, c i • Pi.single i 1) = c := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fintype.sum_eq_single j]
      · simp
      · intro i hij
        simp [hij]
    rw [← hsum]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem_smul (hc i) Submodule.mem_top

noncomputable def columnGenerator
    {M G : Type*} [AddCommGroup M] [Module R M] [Fintype G]
    (f : (G → R) →ₗ[R] M) (i : G) : LinearMap.range f :=
  ⟨f (Pi.single i 1), ⟨Pi.single i 1, rfl⟩⟩

lemma columnGenerator_span_eq_top
    {M G : Type*} [AddCommGroup M] [Module R M] [Fintype G]
    (f : (G → R) →ₗ[R] M) :
    Submodule.span R (Set.range (columnGenerator f)) =
      (⊤ : Submodule R (LinearMap.range f)) := by
  apply le_antisymm le_top
  rintro y hy
  obtain ⟨c, hc⟩ := y.property
  have hsum : (∑ i, c i • Pi.single i 1) = c := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro i hij
      simp [hij]
  have heq :
      (∑ i, c i • columnGenerator f i) = y := by
    apply Subtype.ext
    calc
      (↑(∑ i, c i • columnGenerator f i) : M) =
          ∑ i, c i • f (Pi.single i 1) := by
            simp [columnGenerator]
      _ = f (∑ i, c i • Pi.single i 1) := by
        rw [map_sum]
        simp only [map_smul]
      _ = f c := by rw [hsum]
      _ = (y : M) := hc
  rw [← heq]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

noncomputable def columnMap
    {M G : Type*} [AddCommGroup M] [Module R M] [Fintype G]
    (f : (G → R) →ₗ[R] M) :
    (G → R) →ₗ[R] LinearMap.range f :=
  Fintype.linearCombination R (columnGenerator f)

@[simp] lemma columnMap_apply
    {M G : Type*} [AddCommGroup M] [Module R M] [Fintype G]
    (f : (G → R) →ₗ[R] M) (c : G → R) :
    columnMap f c = ∑ i, c i • columnGenerator f i := rfl

lemma column_residue_independent_of_exact
    {M G H : Type*} [AddCommGroup M] [Module R M]
    [Fintype G] [Fintype H]
    (f : (G → R) →ₗ[R] M) (g : (H → R) →ₗ[R] (G → R)) (J : Ideal R)
    (hexact : LinearMap.range g = LinearMap.ker f)
    (hminimal : LinearMap.range g ≤ J • (⊤ : Submodule R (G → R))) :
    ∀ c : G → R, columnMap f c ∈ J • (⊤ : Submodule R (LinearMap.range f)) →
      ∀ i, c i ∈ J := by
  classical
  let fr : (G → R) →ₗ[R] LinearMap.range f :=
    { toFun := fun c => ⟨f c, ⟨c, rfl⟩⟩
      map_add' := by
        intro c c'
        apply Subtype.ext
        simp
      map_smul' := by
        intro r c
        apply Subtype.ext
        simp }
  have hfr_surj : Function.Surjective fr := by
    rintro ⟨m, ⟨c, rfl⟩⟩
    exact ⟨c, rfl⟩
  have hfr_kernel : LinearMap.ker fr = LinearMap.ker f := by
    apply Submodule.ext
    intro c
    constructor
    · intro hc
      apply LinearMap.mem_ker.mpr
      have hc' := congrArg Subtype.val (LinearMap.mem_ker.mp hc)
      exact hc'
    · intro hc
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact LinearMap.mem_ker.mp hc
  have hmap :
      (J • (⊤ : Submodule R (G → R))).map fr =
        J • (⊤ : Submodule R (LinearMap.range f)) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr hfr_surj]
  intro c hc
  have hsum : (∑ i, c i • Pi.single i 1) = c := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro i hij
      simp [hij]
  have hcolumnMap : columnMap f c = fr c := by
    apply Subtype.ext
    rw [columnMap_apply]
    calc
      (↑(∑ i, c i • columnGenerator f i) : M) =
          ∑ i, c i • f (Pi.single i 1) := by
            simp [columnGenerator]
      _ = f (∑ i, c i • Pi.single i 1) := by
        rw [map_sum]
        simp only [map_smul]
      _ = f c := by rw [hsum]
      _ = (fr c : M) := rfl
  rw [hcolumnMap] at hc
  rw [← hmap] at hc
  obtain ⟨c', hc', hcc'⟩ := Submodule.mem_map.mp hc
  have hdiff_fr : c - c' ∈ LinearMap.ker fr := by
    apply LinearMap.mem_ker.mpr
    rw [fr.map_sub, sub_eq_zero]
    exact hcc'.symm
  have hdiff : c - c' ∈ LinearMap.ker f := by
    rw [← hfr_kernel]
    exact hdiff_fr
  have hdiffJ : c - c' ∈ J • (⊤ : Submodule R (G → R)) := by
    have hdiffRange : c - c' ∈ LinearMap.range g := by
      rw [hexact]
      exact hdiff
    exact hminimal hdiffRange
  have hcJ : c ∈ J • (⊤ : Submodule R (G → R)) := by
    have hrewrite : c = (c - c') + c' := by abel
    rw [hrewrite]
    exact (J • (⊤ : Submodule R (G → R))).add_mem hdiffJ hc'
  exact (mem_smul_top_iff_coeff J c).mp hcJ

def toHomogeneousMinimalGenerators (N : GradedNakayamaCertificate R M G)
    (degree : G → ℕ) (isHomogeneous : G → M → Prop)
    (hh : ∀ g, isHomogeneous g (N.generator g)) :
    HomogeneousMinimalGenerators R M G isHomogeneous :=
  { irrelevant := N.irrelevant
    degree := degree
    generator := N.generator
    homogeneous := hh
    span := N.span
    residueIndependent := N.residueIndependent }

end GradedNakayamaCertificate

namespace GradedMinimalFreeComplex

variable {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}

noncomputable def firstNakayamaCertificate
    (C : GradedMinimalFreeComplex I e hA) :
    @GradedNakayamaCertificate (R3 k) (LinearMap.range C.d₁) C.β₁
      _ _ _ C.fintype₁ := by
  letI := C.fintype₁
  letI := C.fintype₂
  refine
    { irrelevant := irrelevantIdeal k
      generator := GradedNakayamaCertificate.columnGenerator C.d₁
      span := GradedNakayamaCertificate.columnGenerator_span_eq_top C.d₁
      residueIndependent := ?_ }
  intro c hc
  exact GradedNakayamaCertificate.column_residue_independent_of_exact
    C.d₁ C.d₂ (irrelevantIdeal k) C.d₂_range C.second_range_minimal c hc

noncomputable def secondNakayamaCertificate
    (C : GradedMinimalFreeComplex I e hA) :
    @GradedNakayamaCertificate (R3 k) (LinearMap.range C.d₂) C.β₂
      _ _ _ C.fintype₂ := by
  letI := C.fintype₂
  letI := C.fintype₃
  refine
    { irrelevant := irrelevantIdeal k
      generator := GradedNakayamaCertificate.columnGenerator C.d₂
      span := GradedNakayamaCertificate.columnGenerator_span_eq_top C.d₂
      residueIndependent := ?_ }
  intro c hc
  exact GradedNakayamaCertificate.column_residue_independent_of_exact
    C.d₂ C.d₃ (irrelevantIdeal k) C.d₃_range C.third_range_minimal c hc

noncomputable def thirdNakayamaCertificate
    (C : GradedMinimalFreeComplex I e hA) :
    @GradedNakayamaCertificate (R3 k) (LinearMap.range C.d₃) C.β₃
      _ _ _ C.fintype₃ := by
  letI := C.fintype₂
  letI := C.fintype₃
  let z : (Fin 0 → R3 k) →ₗ[R3 k] (C.β₃ → R3 k) := 0
  have hz : LinearMap.range z = LinearMap.ker C.d₃ := by
    rw [show z = 0 from rfl, LinearMap.range_zero,
      LinearMap.ker_eq_bot.mpr C.d₃_injective]
  have hminimal : LinearMap.range z ≤
      irrelevantIdeal k • (⊤ : Submodule (R3 k) (C.β₃ → R3 k)) := by
    rw [show z = 0 from rfl, LinearMap.range_zero]
    exact bot_le
  refine
    { irrelevant := irrelevantIdeal k
      generator := GradedNakayamaCertificate.columnGenerator C.d₃
      span := GradedNakayamaCertificate.columnGenerator_span_eq_top C.d₃
      residueIndependent := ?_ }
  intro c hc
  exact GradedNakayamaCertificate.column_residue_independent_of_exact
    C.d₃ z (irrelevantIdeal k) hz hminimal c hc

lemma one_not_mem_irrelevantIdeal :
    (1 : R3 k) ∉ irrelevantIdeal k := by
  intro h
  have h' : (1 : k) = 0 ∨ (1 : ℕ) = 0 := by
    apply (MvPolynomial.C_mem_pow_idealOfVars_iff
      (σ := Fin 3) (R := k) 1 (1 : k)).mp
    simpa [irrelevantIdeal] using h
  exact one_ne_zero (h'.resolve_right (by decide))

lemma isHomogeneous_mem_irrelevant_eq_zero {f : R3 k}
    (hmem : f ∈ irrelevantIdeal k)
    (hhom : MvPolynomial.IsHomogeneous f 0) : f = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : k, f = MvPolynomial.C c :=
    ⟨f.coeff 0,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr hhom)⟩
  have hcmem : MvPolynomial.C c ∈ MvPolynomial.idealOfVars (Fin 3) k := by
    simpa [irrelevantIdeal, hc] using hmem
  have hc' : c = 0 ∨ (1 : ℕ) = 0 :=
    (MvPolynomial.C_mem_pow_idealOfVars_iff
      (σ := Fin 3) (R := k) 1 c).mp (by simpa using hcmem)
  rcases hc' with rfl | hbad
  · rw [hc]
    simp
  · omega

lemma first_column_ne_zero (C : GradedMinimalFreeComplex I e hA)
    (b : C.β₁) : C.d₁ (Pi.single b 1) ≠ 0 := by
  letI := C.fintype₁
  letI := C.fintype₂
  intro hzero
  let N := C.firstNakayamaCertificate
  let c : C.β₁ → R3 k := Pi.single b 1
  have hsum0 : ∑ i, c i • C.d₁ (Pi.single i 1) = 0 := by
    have hsingle : (∑ i, c i • Pi.single i 1) = Pi.single b 1 := by
      funext j
      rw [Fintype.sum_eq_single b]
      · simp [c]
      · intro i hib
        simp [c, hib]
    calc
      (∑ i, c i • C.d₁ (Pi.single i 1)) =
          C.d₁ (∑ i, c i • Pi.single i 1) := by
        rw [map_sum]
        simp only [map_smul]
      _ = C.d₁ (Pi.single b 1) := by rw [hsingle]
      _ = 0 := hzero
  have hsum : ∑ i, c i • N.generator i = 0 := by
    apply Subtype.ext
    simpa [N, firstNakayamaCertificate,
      GradedNakayamaCertificate.columnGenerator] using hsum0
  have hmem :
      (∑ i, c i • N.generator i) ∈
        N.irrelevant • (⊤ : Submodule (R3 k) (LinearMap.range C.d₁)) := by
    rw [hsum]
    exact Submodule.zero_mem _
  have hcoeff := N.residueIndependent c hmem b
  have hcoeff' : c b ∈ irrelevantIdeal k := by
    simpa [N, firstNakayamaCertificate] using hcoeff
  exact one_not_mem_irrelevantIdeal (by simpa [c] using hcoeff')

lemma second_column_ne_zero (C : GradedMinimalFreeComplex I e hA)
    (g : C.β₂) : C.d₂ (Pi.single g 1) ≠ 0 := by
  letI := C.fintype₂
  letI := C.fintype₃
  intro hzero
  let N := C.secondNakayamaCertificate
  let c : C.β₂ → R3 k := Pi.single g 1
  have hsum0 : ∑ i, c i • C.d₂ (Pi.single i 1) = 0 := by
    have hsingle : (∑ i, c i • Pi.single i 1) = Pi.single g 1 := by
      funext j
      rw [Fintype.sum_eq_single g]
      · simp [c]
      · intro i hig
        simp [c, hig]
    calc
      (∑ i, c i • C.d₂ (Pi.single i 1)) =
          C.d₂ (∑ i, c i • Pi.single i 1) := by
        rw [map_sum]
        simp only [map_smul]
      _ = C.d₂ (Pi.single g 1) := by rw [hsingle]
      _ = 0 := hzero
  have hsum : ∑ i, c i • N.generator i = 0 := by
    apply Subtype.ext
    simpa [N, secondNakayamaCertificate,
      GradedNakayamaCertificate.columnGenerator] using hsum0
  have hmem :
      (∑ i, c i • N.generator i) ∈
        N.irrelevant • (⊤ : Submodule (R3 k) (LinearMap.range C.d₂)) := by
    rw [hsum]
    exact Submodule.zero_mem _
  have hcoeff := N.residueIndependent c hmem g
  have hcoeff' : c g ∈ irrelevantIdeal k := by
    simpa [N, secondNakayamaCertificate] using hcoeff
  exact one_not_mem_irrelevantIdeal (by simpa [c] using hcoeff')

lemma third_column_ne_zero (C : GradedMinimalFreeComplex I e hA)
    (a : C.β₃) : C.d₃ (Pi.single a 1) ≠ 0 := by
  letI := C.fintype₂
  letI := C.fintype₃
  intro hzero
  let N := C.thirdNakayamaCertificate
  let c : C.β₃ → R3 k := Pi.single a 1
  have hsum0 : ∑ i, c i • C.d₃ (Pi.single i 1) = 0 := by
    have hsingle : (∑ i, c i • Pi.single i 1) = Pi.single a 1 := by
      funext j
      rw [Fintype.sum_eq_single a]
      · simp [c]
      · intro i hia
        simp [c, hia]
    calc
      (∑ i, c i • C.d₃ (Pi.single i 1)) =
          C.d₃ (∑ i, c i • Pi.single i 1) := by
        rw [map_sum]
        simp only [map_smul]
      _ = C.d₃ (Pi.single a 1) := by rw [hsingle]
      _ = 0 := hzero
  have hsum : ∑ i, c i • N.generator i = 0 := by
    apply Subtype.ext
    simpa [N, thirdNakayamaCertificate,
      GradedNakayamaCertificate.columnGenerator] using hsum0
  have hmem :
      (∑ i, c i • N.generator i) ∈
        N.irrelevant • (⊤ : Submodule (R3 k) (LinearMap.range C.d₃)) := by
    rw [hsum]
    exact Submodule.zero_mem _
  have hcoeff := N.residueIndependent c hmem a
  have hcoeff' : c a ∈ irrelevantIdeal k := by
    simpa [N, thirdNakayamaCertificate] using hcoeff
  exact one_not_mem_irrelevantIdeal (by simpa [c] using hcoeff')

lemma pShift_pos (C : GradedMinimalFreeComplex I e hA) (b : C.β₁) :
    0 < C.pShift b := by
  by_contra hb
  have hb0 : C.pShift b = 0 := Nat.eq_zero_of_not_pos hb
  have hzero : ∀ i, C.d₁ (Pi.single b 1) i = 0 := by
    intro i
    apply isHomogeneous_mem_irrelevant_eq_zero
      (C.d₁_minimal b i)
    simpa [hb0] using C.d₁_homogeneous b i
  apply first_column_ne_zero C b
  funext i
  exact hzero i

lemma qShift_pos (C : GradedMinimalFreeComplex I e hA) (g : C.β₂) :
    0 < C.qShift g := by
  by_contra hg
  have hg0 : C.qShift g = 0 := Nat.eq_zero_of_not_pos hg
  have hzero : ∀ b, C.d₂ (Pi.single g 1) b = 0 := by
    intro b
    have hbpos := pShift_pos C b
    have hnot : ¬ C.pShift b ≤ C.qShift g := by omega
    have hhom := C.d₂_homogeneous g b
    rw [if_neg hnot] at hhom
    exact hhom
  apply second_column_ne_zero C g
  funext b
  exact hzero b

lemma rShift_pos (C : GradedMinimalFreeComplex I e hA) (a : C.β₃) :
    0 < C.rShift a := by
  by_contra ha
  have ha0 : C.rShift a = 0 := Nat.eq_zero_of_not_pos ha
  have hzero : ∀ g, C.d₃ (Pi.single a 1) g = 0 := by
    intro g
    have hgpos := qShift_pos C g
    have hnot : ¬ C.qShift g ≤ C.rShift a := by omega
    have hhom := C.d₃_homogeneous a g
    rw [if_neg hnot] at hhom
    exact hhom
  apply third_column_ne_zero C a
  funext g
  exact hzero g

noncomputable def firstHomogeneousMinimalGenerators
    (C : GradedMinimalFreeComplex I e hA) :
    @HomogeneousMinimalGenerators (R3 k) (LinearMap.range C.d₁) C.β₁
      (fun b v => ∀ i, MvPolynomial.IsHomogeneous (v.1 i) (C.pShift b))
      _ _ _ C.fintype₁ := by
  letI := C.fintype₁
  let N := C.firstNakayamaCertificate
  exact GradedNakayamaCertificate.toHomogeneousMinimalGenerators N C.pShift _ (by
    intro b i
    change MvPolynomial.IsHomogeneous (C.d₁ (Pi.single b 1) i) (C.pShift b)
    exact C.d₁_homogeneous b i)

noncomputable def secondHomogeneousMinimalGenerators
    (C : GradedMinimalFreeComplex I e hA) :
    @HomogeneousMinimalGenerators (R3 k) (LinearMap.range C.d₂) C.β₂
      (fun g v => ∀ b, if C.pShift b ≤ C.qShift g then
        MvPolynomial.IsHomogeneous (v.1 b) (C.qShift g - C.pShift b)
      else v.1 b = 0)
      _ _ _ C.fintype₂ := by
  letI := C.fintype₂
  letI := C.fintype₁
  let N := C.secondNakayamaCertificate
  exact GradedNakayamaCertificate.toHomogeneousMinimalGenerators N C.qShift _ (by
    intro g b
    change (if C.pShift b ≤ C.qShift g then
      MvPolynomial.IsHomogeneous (C.d₂ (Pi.single g 1) b)
        (C.qShift g - C.pShift b)
      else C.d₂ (Pi.single g 1) b = 0)
    exact C.d₂_homogeneous g b)

noncomputable def thirdHomogeneousMinimalGenerators
    (C : GradedMinimalFreeComplex I e hA) :
    @HomogeneousMinimalGenerators (R3 k) (LinearMap.range C.d₃) C.β₃
      (fun a v => ∀ g, if C.qShift g ≤ C.rShift a then
        MvPolynomial.IsHomogeneous (v.1 g) (C.rShift a - C.qShift g)
      else v.1 g = 0)
      _ _ _ C.fintype₃ := by
  letI := C.fintype₃
  letI := C.fintype₂
  let N := C.thirdNakayamaCertificate
  exact GradedNakayamaCertificate.toHomogeneousMinimalGenerators N C.rShift _ (by
    intro a g
    change (if C.qShift g ≤ C.rShift a then
      MvPolynomial.IsHomogeneous (C.d₃ (Pi.single a 1) g)
        (C.rShift a - C.qShift g)
      else C.d₃ (Pi.single a 1) g = 0)
    exact C.d₃_homogeneous a g)

end GradedMinimalFreeComplex

/-! The actual graded Matlis-dual output used by the resolution bridge. -/

structure GradedMatlisDualData (I : Ideal (R3 k)) (e : ℕ)
    (hA : IsTypeTwoLevel I e) where
  top_basis : Basis (Fin 2) k (reversedMatlisPiece hA 0)
  presentation : (Fin 2 → R3 k) →ₗ[R3 k] MatlisDual I
  presentation_surjective : Function.Surjective presentation
  kernel : Submodule (R3 k) (Fin 2 → R3 k)
  kernel_eq : kernel = LinearMap.ker presentation
  component_equiv : ∀ d : ℕ, d ≤ e →
    reversedMatlisPiece hA d ≃ₗ[k] gradedDualPiece I e d

namespace GradedMatlisDualData

variable {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)

noncomputable def ofLevel : GradedMatlisDualData I e hA :=
  { top_basis := matlisTopBasis hA
    presentation := inverseSystemMap hA
    presentation_surjective := inverseSystemMap_surjective hA
    kernel := inverseSystemKernel hA
    kernel_eq := rfl
    component_equiv := fun _ hd => reversedMatlisPieceEquiv hA hd }

lemma component_finrank (D : GradedMatlisDualData I e hA) (d : ℕ) (hd : d ≤ e) :
    finrank k (reversedMatlisPiece hA d) = finrank k (quotPiece I (e - d)) := by
  rw [(D.component_equiv d hd).finrank_eq, Subspace.dual_finrank_eq]

lemma component_finrank_hilbert (D : GradedMatlisDualData I e hA)
    (d : ℕ) (hd : d ≤ e) :
    (finrank k (reversedMatlisPiece hA d) : ℤ) = reversedHilb I e (d : ℤ) := by
  have hdual := finrank_gradedDualPiece I e d hd
  calc
    (finrank k (reversedMatlisPiece hA d) : ℤ) =
        (finrank k (gradedDualPiece I e d) : ℤ) := by
      exact_mod_cast (D.component_equiv d hd).finrank_eq
    _ = reversedHilb I e (d : ℤ) := hdual

lemma component_finrank_original_hilbert (D : GradedMatlisDualData I e hA)
    (d : ℕ) (hd : d ≤ e) :
    (finrank k (reversedMatlisPiece hA d) : ℤ) =
      hilb I ((e - d : ℕ) : ℤ) := by
  simpa [reversedHilb, Nat.cast_sub hd] using
    component_finrank_hilbert hA D d hd

lemma component_presentation_surjective (d : ℕ) (hd : d ≤ e) :
    Function.Surjective (inverseSystemPieceMap hA d) :=
  inverseSystemPieceMap_surjective hA hd

end GradedMatlisDualData

end LogConcavity

#print axioms LogConcavity.GradedMinimalFreeComplex.third_kernel_finrank
#print axioms LogConcavity.LocalizedThreeStepResolution.third_kernel_basis_fin_one_of_euler
#print axioms LogConcavity.GradedNakayamaCertificate.column_residue_independent_of_exact
#print axioms LogConcavity.GradedMinimalFreeComplex.firstHomogeneousMinimalGenerators
#print axioms LogConcavity.GradedMatlisDualData.component_finrank_original_hilbert
#print axioms LogConcavity.GradedResolutionDuality.lastDifferentialVector_full
