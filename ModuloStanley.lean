import LogConcavity
import GradedResolution
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Algebra.Polynomial.RingDivision
import FormalDeps.Port.Mathlib.RingTheory.Regular.Depth

open scoped BigOperators

namespace LogConcavity

universe u
variable {k : Type u} [Field k]

open MvPolynomial Module
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Classical.decEq
attribute [local instance] GradedMinimalFreeComplex.fintype₁
attribute [local instance] GradedMinimalFreeComplex.fintype₂
attribute [local instance] GradedMinimalFreeComplex.fintype₃

noncomputable def shiftedSubmodule {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) (b : β) : Submodule k (R3 k) :=
  if h : degree b ≤ n then
    homogeneousSubmodule (Fin 3) k (n - degree b)
  else ⊥

noncomputable def shiftedProjection {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) :
    (β → R3 k) →ₗ[k] (β → R3 k) where
  toFun c b :=
    if h : degree b ≤ n then
      MvPolynomial.homogeneousComponent (n - degree b) (c b)
    else 0
  map_add' := by
    intro c c'
    funext b
    by_cases h : degree b ≤ n
    · simp [h, map_add]
    · simp [h]
  map_smul' := by
    intro a c
    funext b
    by_cases h : degree b ≤ n
    · simp [h, map_smul]
    · simp [h]

noncomputable instance shiftedSubmodule_finite {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) (b : β) :
    Module.Finite k (shiftedSubmodule (k := k) degree n b) := by
  classical
  by_cases h : degree b ≤ n
  · rw [shiftedSubmodule, dif_pos h]
    infer_instance
  · rw [shiftedSubmodule, dif_neg h]
    infer_instance
lemma shiftedProjection_apply {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) (c : β → R3 k) (b : β) :
    shiftedProjection degree n c b =
      if degree b ≤ n then
        MvPolynomial.homogeneousComponent (n - degree b) (c b)
      else 0 := rfl

noncomputable def shiftedRangeEquiv {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) :
    LinearMap.range (shiftedProjection (k := k) degree n) ≃ₗ[k]
      (∀ b : β, shiftedSubmodule (k := k) degree n b) := by
  let P := shiftedProjection (k := k) degree n
  let f : LinearMap.range P → (∀ b : β, shiftedSubmodule (k := k) degree n b) :=
    fun x b => ⟨x.1 b, by
      let c := Classical.choose x.2
      have hc : P c = x.1 := Classical.choose_spec x.2
      by_cases h : degree b ≤ n
      · rw [shiftedSubmodule, dif_pos h]
        rw [← congrFun hc b]
        simpa [P, shiftedProjection_apply, h] using
          (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.homogeneousComponent_isHomogeneous
              (n - degree b) (c b))
      · rw [shiftedSubmodule, dif_neg h]
        rw [← congrFun hc b]
        simp [P, shiftedProjection_apply, h]⟩
  let g : (∀ b : β, shiftedSubmodule (k := k) degree n b) → LinearMap.range P :=
    fun y => ⟨fun b => (y b).1, by
      refine ⟨fun b => (y b).1, ?_⟩
      funext b
      by_cases h : degree b ≤ n
      · have hy : (y b).1 ∈ homogeneousSubmodule (Fin 3) k (n - degree b) := by
          simpa [shiftedSubmodule, h] using (y b).2
        rw [shiftedProjection_apply, if_pos h]
        simpa [if_pos rfl] using
          (MvPolynomial.homogeneousComponent_of_mem (m := n - degree b) hy)
      · have hy : (y b).1 ∈ (⊥ : Submodule k (R3 k)) := by
          simpa [shiftedSubmodule, h] using (y b).2
        have hy0 : (y b).1 = 0 := by simpa using hy
        rw [shiftedProjection_apply, if_neg h, hy0]⟩
  have hleft : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    funext b
    rfl
  have hright : Function.RightInverse g f := by
    intro y
    funext b
    apply Subtype.ext
    rfl
  exact
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright
      map_add' := by
        intro x y
        funext b
        apply Subtype.ext
        simp [f]
      map_smul' := by
        intro a x
        funext b
        apply Subtype.ext
        simp [f] }

lemma shiftedRange_finrank {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) :
    (finrank k (LinearMap.range (shiftedProjection (k := k) degree n)) : ℤ) =
      ∑ b ∈ Finset.univ,
        if degree b ≤ n then N (n - degree b) else 0 := by
  let e := shiftedRangeEquiv (k := k) degree n
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  classical
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : degree b ≤ n
  · rw [shiftedSubmodule, dif_pos h, finrank_homogeneousSubmodule]
    simp only [if_pos h, N]
  · rw [shiftedSubmodule, dif_neg h, finrank_bot]
    simp [h]

lemma shiftedRange_finrank_shiftSum {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) (u : ℤ)
    (hu : ∀ b, (degree b : ℤ) ≤ u) :
    (finrank k (LinearMap.range (shiftedProjection (k := k) degree n)) : ℤ) =
      shiftSum u (shiftMultiplicity (fun b => (degree b : ℤ))) (n : ℤ) := by
  classical
  rw [shiftedRange_finrank]
  unfold shiftSum shiftMultiplicity
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Nat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hbn : degree b ≤ n
  · have hbu : (degree b : ℤ) ∈ Finset.Icc (0 : ℤ) u := by
      refine Finset.mem_Icc.mpr ⟨Int.natCast_nonneg _, hu b⟩
    conv_rhs =>
      rw [Finset.sum_eq_single_of_mem (s := Finset.Icc (0 : ℤ) u)
        (degree b) hbu (by
          intro z hz hzneq
          by_cases heq : (degree b : ℤ) = z
          · exact (hzneq heq.symm).elim
          · simp [heq])]
    simp only [if_pos rfl, one_mul]
    rw [← Nat.cast_sub hbn, Nz_natCast]
    simp [hbn]
  · have hbn' : n < degree b := by omega
    have hzero : ∀ z : ℤ, z ∈ Finset.Icc (0 : ℤ) u →
        (if (degree b : ℤ) = z then 1 else 0) * Nz ((n : ℤ) - z) = 0 := by
      intro z hz
      by_cases hz' : (degree b : ℤ) = z
      · subst z
        have hneg : (n : ℤ) - (degree b : ℤ) < 0 := by
          exact sub_neg.mpr (by exact_mod_cast hbn')
        simp [Nz_neg _ hneg]
      · simp [hz']
    rw [Finset.sum_eq_zero (by
      intro z hz
      simpa using hzero z hz)]
    simp [hbn]

lemma shiftedRange_finrank_shiftSum_of_nonneg {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) (u : ℤ)
    (hdegree : ∀ b, 0 ≤ (degree b : ℤ)) (hnu : (n : ℤ) ≤ u) :
    (finrank k (LinearMap.range (shiftedProjection (k := k) degree n)) : ℤ) =
      shiftSum u (shiftMultiplicity (fun b => (degree b : ℤ))) (n : ℤ) := by
  classical
  rw [shiftedRange_finrank]
  unfold shiftSum shiftMultiplicity
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Nat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hbn : degree b ≤ n
  · have hbu : (degree b : ℤ) ∈ Finset.Icc (0 : ℤ) u := by
      refine Finset.mem_Icc.mpr ⟨hdegree b, ?_⟩
      exact le_trans (by exact_mod_cast hbn) hnu
    conv_rhs =>
      rw [Finset.sum_eq_single_of_mem (s := Finset.Icc (0 : ℤ) u)
        (degree b) hbu (by
          intro z hz hzneq
          by_cases heq : (degree b : ℤ) = z
          · exact (hzneq heq.symm).elim
          · simp [heq])]
    simp only [if_pos rfl, one_mul]
    rw [← Nat.cast_sub hbn, Nz_natCast]
    simp [hbn]
  · have hbn' : n < degree b := by omega
    have hzero : ∀ z : ℤ, z ∈ Finset.Icc (0 : ℤ) u →
        (if (degree b : ℤ) = z then 1 else 0) * Nz ((n : ℤ) - z) = 0 := by
      intro z hz
      by_cases hz' : (degree b : ℤ) = z
      · subst z
        have hneg : (n : ℤ) - (degree b : ℤ) < 0 := by
          exact sub_neg.mpr (by exact_mod_cast hbn')
        simp [Nz_neg _ hneg]
      · simp [hz']
    rw [Finset.sum_eq_zero (by
      intro z hz
      simpa using hzero z hz)]
    simp [hbn]

noncomputable def rangeMap
    {U V : Type*} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V]
    (f : U →ₗ[k] V) (P : U →ₗ[k] U) (Q : V →ₗ[k] V)
    (h : f.comp P = Q.comp f) :
    LinearMap.range P →ₗ[k] LinearMap.range Q := by
  refine
    { toFun := fun x => ⟨f x.1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · obtain ⟨c, hc⟩ := x.2
    refine ⟨f c, ?_⟩
    have hh := congrArg (fun g => g c) h
    simpa [LinearMap.comp_apply] using hh.symm.trans (congrArg f hc)
  · intro x y
    apply Subtype.ext
    exact f.map_add x.1 y.1
  · intro a x
    apply Subtype.ext
    exact f.map_smul a x.1

@[simp] lemma rangeMap_apply_val
    {U V : Type*} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V]
    (f : U →ₗ[k] V) (P : U →ₗ[k] U) (Q : V →ₗ[k] V)
    (h : f.comp P = Q.comp f) (x : LinearMap.range P) :
    (rangeMap f P Q h x).1 = f x.1 := rfl

lemma rangeMap_injective
    {U V : Type*} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V]
    (f : U →ₗ[k] V) (P : U →ₗ[k] U) (Q : V →ₗ[k] V)
    (h : f.comp P = Q.comp f) (hf : Function.Injective f) :
    Function.Injective (rangeMap f P Q h) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val hxy

lemma rangeMap_range_eq_ker
    {U₂ U₁ U₀ : Type*}
    [AddCommGroup U₂] [Module k U₂]
    [AddCommGroup U₁] [Module k U₁]
    [AddCommGroup U₀] [Module k U₀]
    (f₂ : U₂ →ₗ[k] U₁) (f₁ : U₁ →ₗ[k] U₀)
    (P₂ : U₂ →ₗ[k] U₂) (P₁ : U₁ →ₗ[k] U₁) (P₀ : U₀ →ₗ[k] U₀)
    (h₂ : f₂.comp P₂ = P₁.comp f₂)
    (h₁ : f₁.comp P₁ = P₀.comp f₁)
    (hidem₁ : P₁.comp P₁ = P₁)
    (h₂₁ : LinearMap.range f₂ = LinearMap.ker f₁) :
    LinearMap.range (rangeMap f₂ P₂ P₁ h₂) =
      LinearMap.ker (rangeMap f₁ P₁ P₀ h₁) := by
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    have hcomp : f₁ (f₂ x.1) = 0 := by
      have hm : f₂ x.1 ∈ LinearMap.range f₂ := by
        exact ⟨x.1, rfl⟩
      rw [h₂₁] at hm
      exact LinearMap.mem_ker.mp hm
    change f₁ (f₂ x.1) = 0
    exact hcomp
  · intro hy
    have hyker : f₁ y.1 = 0 := by
      have := LinearMap.mem_ker.mp hy
      exact congrArg Subtype.val this
    have hymem : y.1 ∈ LinearMap.range f₂ := by
      rw [h₂₁]
      exact LinearMap.mem_ker.mpr hyker
    obtain ⟨c, hc⟩ := hymem
    have hfixed : P₁ y.1 = y.1 := by
      obtain ⟨c', hc'⟩ := y.2
      have hh := congrArg (fun g => g c') hidem₁
      simpa [LinearMap.comp_apply, hc'] using hh
    let x : LinearMap.range P₂ := ⟨P₂ c, ⟨c, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    have hh : f₂ (P₂ c) = P₁ (f₂ c) := by
      simpa [LinearMap.comp_apply] using congrArg (fun g => g c) h₂
    change f₂ (P₂ c) = y.1
    rw [hh, hc, hfixed]

lemma shiftedProjection_idem {β : Type*} [Fintype β]
    (degree : β → ℕ) (n : ℕ) :
    (shiftedProjection (k := k) degree n).comp
        (shiftedProjection (k := k) degree n) =
      shiftedProjection (k := k) degree n := by
  classical
  apply LinearMap.ext
  intro c
  funext b
  by_cases h : degree b ≤ n
  · rw [LinearMap.comp_apply, shiftedProjection_apply,
      shiftedProjection_apply, if_pos h, if_pos h]
    have hh := MvPolynomial.homogeneousComponent_isHomogeneous
      (n - degree b) (c b)
    have hm := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hh
    rw [MvPolynomial.homogeneousComponent_of_mem hm]
    simp
  · simp [LinearMap.comp_apply, shiftedProjection_apply, h]

lemma vectorProjection_eq_shifted (n : ℕ) :
    shiftedProjection (k := k) (fun _ : Fin 2 => 0) n =
      vectorHomogeneousComponent n := by
  ext c i
  simp [shiftedProjection_apply, vectorHomogeneousComponent_apply]

noncomputable def exactPresentationOfLinearData
    {V₂ V₁ V₀ M : Type*}
    [AddCommGroup V₂] [Module k V₂]
    [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₀] [Module k V₀]
    [AddCommGroup M] [Module k M]
    [FiniteDimensional k V₂] [FiniteDimensional k V₁]
    [FiniteDimensional k V₀]
    (f₂ : V₂ →ₗ[k] V₁) (f₁ : V₁ →ₗ[k] V₀) (f₀ : V₀ →ₗ[k] M)
    (hf₂ : Function.Injective f₂)
    (h₂₁ : LinearMap.range f₂ = LinearMap.ker f₁)
    (h₁₀ : LinearMap.range f₁ = LinearMap.ker f₀)
    (hf₀ : Function.Surjective f₀)
    {m₂ m₁ m₀ : ℕ}
    (hfr₂ : finrank k V₂ = m₂)
    (hfr₁ : finrank k V₁ = m₁)
    (hfr₀ : finrank k V₀ = m₀) :
    ExactPresentation k M m₂ m₁ m₀ := by
  let b₂ : Basis (Fin m₂) k V₂ := Module.finBasisOfFinrankEq k V₂ hfr₂
  let b₁ : Basis (Fin m₁) k V₁ := Module.finBasisOfFinrankEq k V₁ hfr₁
  let b₀ : Basis (Fin m₀) k V₀ := Module.finBasisOfFinrankEq k V₀ hfr₀
  let e₂ := b₂.equivFun
  let e₁ := b₁.equivFun
  let e₀ := b₀.equivFun
  let g₂ : (Fin m₂ → k) →ₗ[k] (Fin m₁ → k) :=
    e₁.toLinearMap.comp (f₂.comp e₂.symm.toLinearMap)
  let g₁ : (Fin m₁ → k) →ₗ[k] (Fin m₀ → k) :=
    e₀.toLinearMap.comp (f₁.comp e₁.symm.toLinearMap)
  let g₀ : (Fin m₀ → k) →ₗ[k] M :=
    f₀.comp e₀.symm.toLinearMap
  have hcomp₂₁ : f₁.comp f₂ = 0 := by
    apply LinearMap.ext
    intro x
    have hx : f₂ x ∈ LinearMap.ker f₁ := by
      rw [← h₂₁]
      exact LinearMap.mem_range_self f₂ x
    exact LinearMap.mem_ker.mp hx
  have hcomp₁₀ : f₀.comp f₁ = 0 := by
    apply LinearMap.ext
    intro x
    have hx : f₁ x ∈ LinearMap.ker f₀ := by
      rw [← h₁₀]
      exact LinearMap.mem_range_self f₁ x
    exact LinearMap.mem_ker.mp hx
  have hg₂ : Function.Injective g₂ := by
    intro x y hxy
    apply e₂.symm.injective
    apply hf₂
    apply e₁.injective
    simpa [g₂, LinearMap.comp_apply] using hxy
  have hex₂₁ : LinearMap.range g₂ = LinearMap.ker g₁ := by
    apply Submodule.ext
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hx : f₁ (f₂ (e₂.symm x)) = 0 := by
        simpa [LinearMap.comp_apply] using congrArg (fun z => z (e₂.symm x)) hcomp₂₁
      simpa [g₁, g₂, LinearMap.comp_apply] using congrArg e₀ hx
    · intro hy
      have hy' : f₁ (e₁.symm y) = 0 := by
        apply e₀.injective
        simpa [g₁, LinearMap.comp_apply] using hy
      have hymem : e₁.symm y ∈ LinearMap.range f₂ := by
        rw [h₂₁]
        exact LinearMap.mem_ker.mpr hy'
      obtain ⟨x, hx⟩ := hymem
      refine ⟨e₂ x, ?_⟩
      apply e₁.symm.injective
      simpa [g₂, LinearMap.comp_apply] using hx
  have hex₁₀ : LinearMap.range g₁ = LinearMap.ker g₀ := by
    apply Submodule.ext
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hx : f₀ (f₁ (e₁.symm x)) = 0 := by
        simpa [LinearMap.comp_apply] using congrArg (fun z => z (e₁.symm x)) hcomp₁₀
      simpa [g₀, g₁, LinearMap.comp_apply] using hx
    · intro hy
      have hy' : e₀.symm y ∈ LinearMap.ker f₀ := by
        apply LinearMap.mem_ker.mpr
        simpa [g₀, LinearMap.comp_apply] using hy
      have hymem : e₀.symm y ∈ LinearMap.range f₁ := by
        rw [h₁₀]
        exact hy'
      obtain ⟨x, hx⟩ := hymem
      refine ⟨e₁ x, ?_⟩
      apply e₀.symm.injective
      simpa [g₁, LinearMap.comp_apply] using hx
  have hg₀ : Function.Surjective g₀ := by
    intro y
    obtain ⟨x, hx⟩ := hf₀ y
    refine ⟨e₀ x, ?_⟩
    simpa [g₀, LinearMap.comp_apply] using hx
  exact
    { d₂ := g₂
      d₁ := g₁
      d₀ := g₀
      d₂_injective := hg₂
      exact₂₁ := hex₂₁
      exact₁₀ := hex₁₀
      d₀_surjective := hg₀ }

noncomputable def ExactPresentation.postcompEquiv
    {M M' : Type*} [Field k] [AddCommGroup M] [Module k M]
    [AddCommGroup M'] [Module k M']
    {m₂ m₁ m₀ : ℕ}
    (P : ExactPresentation k M m₂ m₁ m₀) (E : M ≃ₗ[k] M') :
    ExactPresentation k M' m₂ m₁ m₀ := by
  have hker : LinearMap.ker (E.toLinearMap.comp P.d₀) = LinearMap.ker P.d₀ := by
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      apply LinearMap.mem_ker.mpr
      apply E.injective
      simpa [LinearMap.comp_apply] using LinearMap.mem_ker.mp hx
    · intro hx
      apply LinearMap.mem_ker.mpr
      simp [LinearMap.comp_apply, LinearMap.mem_ker.mp hx]
  refine
    { d₂ := P.d₂
      d₁ := P.d₁
      d₀ := E.toLinearMap.comp P.d₀
      d₂_injective := P.d₂_injective
      exact₂₁ := P.exact₂₁
      exact₁₀ := by rw [hker, P.exact₁₀]
      d₀_surjective := by
        intro y
        obtain ⟨x, hx⟩ := E.surjective y
        obtain ⟨z, hz⟩ := P.d₀_surjective x
        refine ⟨z, ?_⟩
        simp [LinearMap.comp_apply, hz, hx] }

lemma degreewise_exact_of_minimal
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    (hlast : ∀ a, (e : ℤ) + 3 ≤ (C.rShift a : ℤ)) :
    ∀ n : ℕ, n ≤ e → Nonempty
      (ExactPresentation k (gradedDualPiece I e n)
        (shiftSum ((e : ℤ) + 3)
          (@shiftMultiplicity C.β₂ C.fintype₂ (fun g => (C.qShift g : ℤ)))
          (n : ℤ)).toNat
        (shiftSum ((e : ℤ) + 3)
          (@shiftMultiplicity C.β₁ C.fintype₁ (fun b => (C.pShift b : ℤ)))
          (n : ℤ)).toNat
        (2 * Nz (n : ℤ)).toNat) := by
  classical
  letI : Fintype C.β₁ := C.fintype₁
  letI : Fintype C.β₂ := C.fintype₂
  letI : Fintype C.β₃ := C.fintype₃
  let H := C.firstRelations
  letI : Fintype H.β := H.fintype
  let S := C.secondRelations
  letI : Fintype S.γ := S.fintype
  let T := C.thirdRelations
  letI : Fintype T.δ := T.fintype
  have hHdeg : H.degree = C.pShift := by rfl
  have hSdeg : S.degree = C.qShift := by rfl
  have hTdeg : T.degree = C.rShift := by rfl
  intro n hne
  let P₀ : (Fin 2 → R3 k) →ₗ[k] (Fin 2 → R3 k) :=
    shiftedProjection (fun _ : Fin 2 => 0) n
  let P₁ : (H.β → R3 k) →ₗ[k] (H.β → R3 k) :=
    shiftedProjection H.degree n
  let P₂ : (S.γ → R3 k) →ₗ[k] (S.γ → R3 k) :=
    shiftedProjection S.degree n
  let f₀ : (Fin 2 → R3 k) →ₗ[k] MatlisDual I :=
    (inverseSystemMap hA).restrictScalars k
  let f₁ : (H.β → R3 k) →ₗ[k] (Fin 2 → R3 k) :=
    H.d₁.restrictScalars k
  let f₂ : (S.γ → R3 k) →ₗ[k] (H.β → R3 k) :=
    S.d₂.restrictScalars k
  let Q₀ : MatlisDual I →ₗ[k] MatlisDual I :=
    matlisComponent I hA.homogeneous (e - n)
  have hP₁def : H.shiftedComponent n = P₁ := by
    apply LinearMap.ext
    intro c
    funext b
    rfl
  have hP₂def : S.shiftedComponent n = P₂ := by
    apply LinearMap.ext
    intro c
    funext b
    rfl
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₀) := by
    exact (shiftedRangeEquiv (k := k) (fun _ : Fin 2 => 0) n).symm.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₁) := by
    exact (shiftedRangeEquiv (k := k) H.degree n).symm.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₂) := by
    exact (shiftedRangeEquiv (k := k) S.degree n).symm.finiteDimensional
  have hP₀ : P₀.comp P₀ = P₀ := by
    exact shiftedProjection_idem (k := k) (fun _ : Fin 2 => 0) n
  have hP₁ : P₁.comp P₁ = P₁ := by
    exact shiftedProjection_idem (k := k) H.degree n
  have hP₂ : P₂.comp P₂ = P₂ := by
    exact shiftedProjection_idem (k := k) S.degree n
  have hcomm₀ : f₀.comp P₀ = Q₀.comp f₀ := by
    apply LinearMap.ext
    intro u
    simpa [f₀, P₀, Q₀, vectorProjection_eq_shifted (k := k) n] using
      inverseSystemMap_vectorComponent hA hne u
  have hcomm₁ : f₁.comp P₁ = P₀.comp f₁ := by
    apply LinearMap.ext
    intro c
    simpa [f₁, P₀, P₁, shiftedProjection, vectorProjection_eq_shifted (k := k) n,
      HomogeneousFirstRelations.shiftedComponent] using
      H.d₁_shiftedComponent n c
  have hcomm₂ : f₂.comp P₂ = P₁.comp f₂ := by
    apply LinearMap.ext
    intro c
    have hh := S.d₂_shiftedComponent n c
    rw [hP₂def, hP₁def] at hh
    simpa [f₂] using hh
  have hrange₁₀ : LinearMap.range f₁ = LinearMap.ker f₀ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun g => g c) H.inverseSystemMap_comp_d₁
      change inverseSystemMap hA (H.d₁ c) = 0
      simpa [LinearMap.comp_apply] using hc
    · intro hx
      have hxR : x ∈ LinearMap.ker (inverseSystemMap hA) := by
        change inverseSystemMap hA x = 0
        exact LinearMap.mem_ker.mp hx
      change x ∈ inverseSystemKernel hA at hxR
      rw [← H.range_d₁_eq_kernel] at hxR
      obtain ⟨c, hc⟩ := hxR
      refine ⟨c, ?_⟩
      exact hc
  have hrange₂₁ : LinearMap.range f₂ = LinearMap.ker f₁ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun g => g c) S.d₁_comp_d₂
      change H.d₁ (S.d₂ c) = 0
      exact hc
    · intro hx
      have hxR : x ∈ LinearMap.ker H.d₁ := by
        exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)
      rw [← S.range_d₂_eq_kernel] at hxR
      obtain ⟨c, hc⟩ := hxR
      refine ⟨c, ?_⟩
      exact hc
  have hrange₁ : LinearMap.range (rangeMap f₁ P₁ P₀ hcomm₁) =
      LinearMap.ker (rangeMap f₀ P₀ Q₀ hcomm₀) :=
    rangeMap_range_eq_ker f₁ f₀ P₁ P₀ Q₀
      hcomm₁ hcomm₀ hP₀ hrange₁₀
  have hrange₂ : LinearMap.range (rangeMap f₂ P₂ P₁ hcomm₂) =
      LinearMap.ker (rangeMap f₁ P₁ P₀ hcomm₁) :=
    rangeMap_range_eq_ker f₂ f₁ P₂ P₁ P₀ hcomm₂ hcomm₁ hP₁ hrange₂₁
  have hinj₂ : Function.Injective (rangeMap f₂ P₂ P₁ hcomm₂) := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : f₂ (x.1 - y.1) = 0 := by
      have := congrArg Subtype.val hxy
      simpa [rangeMap_apply_val] using sub_eq_zero.mpr this
    have hker : x.1 - y.1 ∈ LinearMap.ker S.d₂ := by
      exact LinearMap.mem_ker.mpr hxy'
    rw [← T.range_d₃_eq_kernel] at hker
    obtain ⟨c, hc⟩ := hker
    let z := T.shiftedComponent n c
    have hz : z = 0 := by
      funext a
      have hlt : ¬ T.degree a ≤ n := by
        have ha := hlast a
        intro hle
        have : (C.rShift a : ℤ) ≤ (n : ℤ) := by
          simpa [hTdeg] using (show T.degree a ≤ n from hle)
        omega
      simp [z,
        HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations.shiftedComponent,
        hlt]
    have hdz := T.d₃_shiftedComponent n c
    have hxyker : f₂ (x.1 - y.1) = 0 := hxy'
    have hdc : T.d₃ z = x.1 - y.1 := by
      have hxfix : P₂ x.1 = x.1 := by
        obtain ⟨w, hw⟩ := x.2
        have hh := congrArg (fun g => g w)
          (show P₂.comp P₂ = P₂ from hP₂)
        simpa [hw, LinearMap.comp_apply] using hh
      have hyfix : P₂ y.1 = y.1 := by
        obtain ⟨w, hw⟩ := y.2
        have hh := congrArg (fun g => g w)
          (show P₂.comp P₂ = P₂ from hP₂)
        simpa [hw, LinearMap.comp_apply] using hh
      have hfix : P₂ (x.1 - y.1) = x.1 - y.1 := by
        rw [map_sub, hxfix, hyfix]
      rw [hdz, hc]
      rw [hP₂def]
      exact hfix
    rw [hz, map_zero] at hdc
    exact sub_eq_zero.mp hdc.symm
  have hfin₂ : (finrank k (LinearMap.range P₂) : ℤ) =
      shiftSum ((e : ℤ) + 3)
        (shiftMultiplicity (fun g => (C.qShift g : ℤ))) (n : ℤ) := by
    simpa [P₂, hSdeg] using
      shiftedRange_finrank_shiftSum_of_nonneg (k := k) S.degree n
        ((e : ℤ) + 3) (fun g => Int.natCast_nonneg _) (by omega)
  have hfin₁ : (finrank k (LinearMap.range P₁) : ℤ) =
      shiftSum ((e : ℤ) + 3)
        (shiftMultiplicity (fun b => (C.pShift b : ℤ))) (n : ℤ) := by
    simpa [P₁, hHdeg] using
      shiftedRange_finrank_shiftSum_of_nonneg (k := k) H.degree n
        ((e : ℤ) + 3) (fun b => Int.natCast_nonneg _) (by omega)
  have hfin₀ : (finrank k (LinearMap.range P₀) : ℤ) =
      2 * Nz (n : ℤ) := by
    simpa [P₀, Nz_natCast] using
      (show (finrank k (LinearMap.range
          (shiftedProjection (k := k) (fun _ : Fin 2 => 0) n)) : ℤ) =
        2 * Nz (n : ℤ) by
        rw [shiftedRange_finrank]
        simp [Nz_natCast])
  let E : LinearMap.range Q₀ ≃ₗ[k] gradedDualPiece I e n := by
    simpa [Q₀, matlisPiece] using
      (matlisPieceEquiv I hA.homogeneous (e - n))
  letI : FiniteDimensional k (LinearMap.range Q₀) := E.symm.finiteDimensional
  have hsurj₀ : Function.Surjective (rangeMap f₀ P₀ Q₀ hcomm₀) := by
    intro y
    have hne' : e - n ≤ e := Nat.sub_le _ _
    obtain ⟨u, hu⟩ := inverseSystemPieceMap_surjective hA hne' (E y)
    have huHom : ∀ i, MvPolynomial.IsHomogeneous (u i).1 n := by
      intro i
      have huMem : (u i).1 ∈
          MvPolynomial.homogeneousSubmodule (Fin 3) k n := by
        simpa [Nat.sub_sub_self hne] using (u i).2
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp huMem
    let c : Fin 2 → R3 k := fun i => (u i).1
    have hcP : P₀ c = c := by
      funext i
      change MvPolynomial.homogeneousComponent n (u i).1 = (u i).1
      rw [MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (huHom i))]
      simp
    let x : LinearMap.range P₀ := ⟨c, ⟨c, hcP⟩⟩
    refine ⟨x, ?_⟩
    apply E.injective
    have hleft := matlisPieceRestrict_inverseSystemMap hA hne' u
    have hmemc : inverseSystemMap hA c ∈ LinearMap.range Q₀ := by
      have hcQ : Q₀ (f₀ c) = inverseSystemMap hA c := by
        have hh := congrArg (fun g => g c) hcomm₀
        simpa [LinearMap.comp_apply, hcP, f₀] using hh.symm
      rw [← hcQ]
      change Q₀ (f₀ c) ∈ LinearMap.range Q₀
      exact LinearMap.mem_range_self Q₀ (f₀ c)
    change matlisPieceRestrict I hA.homogeneous (e - n)
        ⟨inverseSystemMap hA c, hmemc⟩ = E y
    calc
      matlisPieceRestrict I hA.homogeneous (e - n)
          ⟨inverseSystemMap hA c, hmemc⟩ =
          inverseSystemPieceMap hA (e - n) u := by simpa [c] using hleft
      _ = E y := hu
  let Pexact := exactPresentationOfLinearData
    (m₂ := (shiftSum ((e : ℤ) + 3)
      (shiftMultiplicity (fun g => (C.qShift g : ℤ))) (n : ℤ)).toNat)
    (m₁ := (shiftSum ((e : ℤ) + 3)
      (shiftMultiplicity (fun b => (C.pShift b : ℤ))) (n : ℤ)).toNat)
    (m₀ := (2 * Nz (n : ℤ)).toNat)
    (rangeMap f₂ P₂ P₁ hcomm₂)
    (rangeMap f₁ P₁ P₀ hcomm₁)
    (rangeMap f₀ P₀ Q₀ hcomm₀)
    hinj₂ hrange₂ hrange₁ hsurj₀
    (by
      have hnonneg : 0 ≤ shiftSum ((e : ℤ) + 3)
          (shiftMultiplicity (fun g : C.β₂ => (C.qShift g : ℤ))) (n : ℤ) :=
        shiftSum_nonneg ((e : ℤ) + 3)
          (fun b => shiftMultiplicity_nonneg
            (fun g : C.β₂ => (C.qShift g : ℤ)) b) (n : ℤ)
      have hcast : ((shiftSum ((e : ℤ) + 3)
          (shiftMultiplicity (fun g => (C.qShift g : ℤ))) (n : ℤ)).toNat : ℤ) =
          shiftSum ((e : ℤ) + 3)
            (shiftMultiplicity (fun g => (C.qShift g : ℤ))) (n : ℤ) :=
        Int.toNat_of_nonneg hnonneg
      have hz : (finrank k (LinearMap.range P₂) : ℤ) =
          ((shiftSum ((e : ℤ) + 3)
            (shiftMultiplicity (fun g => (C.qShift g : ℤ))) (n : ℤ)).toNat : ℤ) :=
        hfin₂.trans hcast.symm
      simpa using Int.ofNat_inj.mp hz)
    (by
      have hnonneg : 0 ≤ shiftSum ((e : ℤ) + 3)
          (shiftMultiplicity (fun b : C.β₁ => (C.pShift b : ℤ))) (n : ℤ) :=
        shiftSum_nonneg ((e : ℤ) + 3)
          (fun b => shiftMultiplicity_nonneg
            (fun b : C.β₁ => (C.pShift b : ℤ)) b) (n : ℤ)
      have hcast : ((shiftSum ((e : ℤ) + 3)
          (shiftMultiplicity (fun b => (C.pShift b : ℤ))) (n : ℤ)).toNat : ℤ) =
          shiftSum ((e : ℤ) + 3)
            (shiftMultiplicity (fun b => (C.pShift b : ℤ))) (n : ℤ) :=
        Int.toNat_of_nonneg hnonneg
      have hz : (finrank k (LinearMap.range P₁) : ℤ) =
          ((shiftSum ((e : ℤ) + 3)
            (shiftMultiplicity (fun b => (C.pShift b : ℤ))) (n : ℤ)).toNat : ℤ) :=
        hfin₁.trans hcast.symm
      simpa using Int.ofNat_inj.mp hz)
    (by
      have hnonneg : 0 ≤ 2 * Nz (n : ℤ) :=
        mul_nonneg (by norm_num) (Nz_nonneg _)
      have hcast : ((2 * Nz (n : ℤ)).toNat : ℤ) = 2 * Nz (n : ℤ) :=
        Int.toNat_of_nonneg hnonneg
      have hz : (finrank k (LinearMap.range P₀) : ℤ) =
          ((2 * Nz (n : ℤ)).toNat : ℤ) := hfin₀.trans hcast.symm
      exact Int.ofNat_inj.mp hz)
  have Ppost := Pexact.postcompEquiv E
  exact ⟨Ppost⟩

/-! A finite-dimensional exact presentation can be rebuilt from its Euler
characteristic.  This is useful for the resolution bridge because the
projected four-term complex has the third syzygy as an additional summand in
the middle term. -/

noncomputable def finCastLinearEquiv {a b : ℕ} (h : a = b) :
    (Fin a → k) ≃ₗ[k] (Fin b → k) where
  toFun c i := c (Fin.cast h.symm i)
  invFun c i := c (Fin.cast h i)
  left_inv c := by
    funext i
    simp
  right_inv c := by
    funext i
    simp
  map_add' c d := by
    funext i
    simp
  map_smul' r c := by
    funext i
    simp

noncomputable def finSplitLinearEquiv (a b : ℕ) :
    (Fin (a + b) → k) ≃ₗ[k] (Fin a → k) × (Fin b → k) where
  toFun c :=
    (fun i => c (Fin.castAdd b i), fun j => c (Fin.natAdd a j))
  invFun c := Fin.addCases c.1 c.2
  left_inv c := by
    funext i
    refine Fin.addCases (motive := fun i =>
      Fin.addCases (fun j => c (Fin.castAdd b j))
        (fun j => c (Fin.natAdd a j)) i = c i) ?_ ?_ i
    · intro j
      simp
    · intro j
      simp
  right_inv c := by
    apply Prod.ext
    · funext i
      simp
    · funext j
      simp
  map_add' c d := by
    apply Prod.ext <;> funext i <;> simp
  map_smul' r c := by
    apply Prod.ext <;> funext i <;> simp

noncomputable def exactPresentationOfFinrank
    {M : Type*} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M]
    {m₂ m₁ m₀ : ℕ}
    (hm₀ : finrank k M ≤ m₀) (hm₁ : m₂ ≤ m₁)
    (he : finrank k M + m₁ = m₀ + m₂) :
    Nonempty (ExactPresentation k M m₂ m₁ m₀) := by
  classical
  let d := finrank k M
  let r₀ := m₀ - d
  let r₁ := m₁ - m₂
  have hd : d + r₀ = m₀ := by
    dsimp [r₀]
    omega
  have hr : r₀ = r₁ := by
    dsimp [r₀, r₁]
    omega
  have h₁ : r₁ + m₂ = m₁ := by
    dsimp [r₁]
    omega
  let bM : Module.Basis (Fin d) k M := Module.finBasis k M
  let EM : (Fin d → k) ≃ₗ[k] M := bM.equivFun.symm
  let E₀ : (Fin m₀ → k) ≃ₗ[k]
      (Fin d → k) × (Fin r₀ → k) :=
    (finCastLinearEquiv (k := k) hd).symm.trans
      (finSplitLinearEquiv (k := k) d r₀)
  let E₁ : (Fin m₁ → k) ≃ₗ[k]
      (Fin r₁ → k) × (Fin m₂ → k) :=
    (finCastLinearEquiv (k := k) h₁).symm.trans
      (finSplitLinearEquiv (k := k) r₁ m₂)
  let ER : (Fin r₁ → k) ≃ₗ[k] (Fin r₀ → k) :=
    finCastLinearEquiv (k := k) hr.symm
  let L₁ : ((Fin r₁ → k) × (Fin m₂ → k)) →ₗ[k]
      ((Fin d → k) × (Fin r₀ → k)) :=
    { toFun := fun x => (0, ER x.1)
      map_add' := by
        intro x y
        apply Prod.ext <;> simp
      map_smul' := by
        intro c x
        apply Prod.ext <;> simp }
  let L₂ : (Fin m₂ → k) →ₗ[k] ((Fin r₁ → k) × (Fin m₂ → k)) :=
    { toFun := fun x => (0, x)
      map_add' := by
        intro x y
        apply Prod.ext <;> simp
      map_smul' := by
        intro c x
        apply Prod.ext <;> simp }
  let d₀ : (Fin m₀ → k) →ₗ[k] M :=
    EM.toLinearMap.comp ((LinearMap.fst k (Fin d → k) (Fin r₀ → k)).comp
      E₀.toLinearMap)
  let d₁ : (Fin m₁ → k) →ₗ[k] (Fin m₀ → k) :=
    E₀.symm.toLinearMap.comp (L₁.comp E₁.toLinearMap)
  let d₂ : (Fin m₂ → k) →ₗ[k] (Fin m₁ → k) :=
    E₁.symm.toLinearMap.comp L₂
  have hEMinj : Function.Injective EM := EM.injective
  have hd₂ : Function.Injective d₂ := by
    intro x y hxy
    have hE : L₂ x = L₂ y := by
      simpa [d₂, LinearMap.comp_apply] using congrArg E₁ hxy
    change (0, x) = (0, y) at hE
    exact congrArg Prod.snd hE
  have hd₁d₂ : LinearMap.range d₂ = LinearMap.ker d₁ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      apply LinearMap.mem_ker.mpr
      simp [d₁, d₂, LinearMap.comp_apply, L₁, L₂]
    · intro hx
      have hx' : L₁ (E₁ x) = 0 := by
        apply E₀.symm.injective
        simpa [d₁, LinearMap.comp_apply] using hx
      have hfirst : (E₁ x).1 = 0 := by
        have hcoord := congrArg Prod.snd hx'
        have : ER (E₁ x).1 = 0 := by simpa [L₁] using hcoord
        exact ER.injective (by simpa using this)
      let y : Fin m₂ → k := (E₁ x).2
      refine ⟨y, ?_⟩
      have heq : E₁ x = (0, (E₁ x).2) := by
        exact Prod.ext hfirst rfl
      refine E₁.injective ?_
      calc
        E₁ (d₂ y) = L₂ y := by simp [d₂, LinearMap.comp_apply]
        _ = (0, (E₁ x).2) := by simp [L₂, y]
        _ = E₁ x := heq.symm
  have hd₀ : Function.Surjective d₀ := by
    intro y
    let c : Fin m₀ → k :=
      E₀.symm (EM.symm y, 0)
    refine ⟨c, ?_⟩
    simp [d₀, LinearMap.comp_apply, c]
  have hd₁₀ : LinearMap.range d₁ = LinearMap.ker d₀ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      apply LinearMap.mem_ker.mpr
      simp [d₀, d₁, LinearMap.comp_apply, L₁]
    · intro hx
      have hx' : (E₀ x).1 = 0 := by
        have hzero := LinearMap.mem_ker.mp hx
        have hzero' : EM ((E₀ x).1) = 0 := by
          simpa [d₀, LinearMap.comp_apply] using hzero
        exact hEMinj (by simpa using hzero')
      let y : Fin r₁ → k := ER.symm (E₀ x).2
      let z : Fin m₁ → k := E₁.symm (y, 0)
      refine ⟨z, ?_⟩
      have heq : E₀ x = (0, (E₀ x).2) := by
        exact Prod.ext hx' rfl
      refine E₀.injective ?_
      calc
        E₀ (d₁ z) = L₁ (E₁ z) := by simp [d₁, LinearMap.comp_apply]
        _ = (0, ER y) := by simp [L₁, z, E₁]
        _ = (0, (E₀ x).2) := by simp [y]
        _ = E₀ x := heq.symm
  refine ⟨?_⟩
  exact
    { d₂ := d₂
      d₁ := d₁
      d₀ := d₀
      d₂_injective := hd₂
      exact₂₁ := hd₁d₂
      exact₁₀ := hd₁₀
      d₀_surjective := hd₀ }

lemma projected_euler_characteristic
    {A₃ A₂ A₁ A₀ B : Type*}
    [AddCommGroup A₃] [Module k A₃] [FiniteDimensional k A₃]
    [AddCommGroup A₂] [Module k A₂] [FiniteDimensional k A₂]
    [AddCommGroup A₁] [Module k A₁] [FiniteDimensional k A₁]
    [AddCommGroup A₀] [Module k A₀] [FiniteDimensional k A₀]
    [AddCommGroup B] [Module k B] [FiniteDimensional k B]
    (g₃ : A₃ →ₗ[k] A₂) (g₂ : A₂ →ₗ[k] A₁)
    (g₁ : A₁ →ₗ[k] A₀) (g₀ : A₀ →ₗ[k] B)
    (hinj₃ : Function.Injective g₃)
    (hex₃₂ : LinearMap.range g₃ = LinearMap.ker g₂)
    (hex₂₁ : LinearMap.range g₂ = LinearMap.ker g₁)
    (hex₁₀ : LinearMap.range g₁ = LinearMap.ker g₀)
    (hsurj₀ : Function.Surjective g₀) :
    finrank k B + finrank k A₁ + finrank k A₃ =
      finrank k A₀ + finrank k A₂ := by
  have h₃ := LinearMap.finrank_range_add_finrank_ker g₃
  have h₂ := LinearMap.finrank_range_add_finrank_ker g₂
  have h₁ := LinearMap.finrank_range_add_finrank_ker g₁
  have h₀ := LinearMap.finrank_range_add_finrank_ker g₀
  rw [LinearMap.ker_eq_bot.mpr hinj₃, finrank_bot, add_zero] at h₃
  rw [← hex₃₂] at h₂
  rw [← hex₂₁] at h₁
  rw [← hex₁₀, LinearMap.range_eq_top.mpr hsurj₀, finrank_top] at h₀
  omega

lemma shiftMultiplicity_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℤ) (g : B → ℤ) (d : ℤ) :
    shiftMultiplicity (Sum.elim f g) d =
      shiftMultiplicity f d + shiftMultiplicity g d := by
  classical
  unfold shiftMultiplicity
  have hA : ((Finset.univ.filter (fun i : A => f i = d)).card : ℤ) =
      ∑ i : A, if f i = d then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp
  have hB : ((Finset.univ.filter (fun i : B => g i = d)).card : ℤ) =
      ∑ i : B, if g i = d then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp
  have hS : ((Finset.univ.filter
      (fun i : A ⊕ B => Sum.elim f g i = d)).card : ℤ) =
      ∑ i : A ⊕ B, if Sum.elim f g i = d then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp
  rw [hS, hA, hB]
  rw [Fintype.sum_sum_type]
  rfl

lemma degreewise_euler_of_minimal
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    ∀ n : ℕ, n ≤ e →
      (finrank k (gradedDualPiece I e n) : ℤ) +
          shiftSum ((e : ℤ) + 3) C.pMultiplicity (n : ℤ) +
          shiftSum ((e : ℤ) + 3) C.rMultiplicity (n : ℤ) =
        2 * Nz (n : ℤ) +
          shiftSum ((e : ℤ) + 3) C.qMultiplicity (n : ℤ) := by
  classical
  letI : Fintype C.β₁ := C.fintype₁
  letI : Fintype C.β₂ := C.fintype₂
  letI : Fintype C.β₃ := C.fintype₃
  let H := C.firstRelations
  letI : Fintype H.β := H.fintype
  let S := C.secondRelations
  letI : Fintype S.γ := S.fintype
  let T := C.thirdRelations
  letI : Fintype T.δ := T.fintype
  have hHdeg : H.degree = C.pShift := by rfl
  have hSdeg : S.degree = C.qShift := by rfl
  have hTdeg : T.degree = C.rShift := by rfl
  intro n hne
  let P₀ : (Fin 2 → R3 k) →ₗ[k] (Fin 2 → R3 k) :=
    shiftedProjection (fun _ : Fin 2 => 0) n
  let P₁ : (H.β → R3 k) →ₗ[k] (H.β → R3 k) :=
    shiftedProjection H.degree n
  let P₂ : (S.γ → R3 k) →ₗ[k] (S.γ → R3 k) :=
    shiftedProjection S.degree n
  let P₃ : (T.δ → R3 k) →ₗ[k] (T.δ → R3 k) :=
    shiftedProjection T.degree n
  let f₀ : (Fin 2 → R3 k) →ₗ[k] MatlisDual I :=
    (inverseSystemMap hA).restrictScalars k
  let f₁ : (H.β → R3 k) →ₗ[k] (Fin 2 → R3 k) :=
    H.d₁.restrictScalars k
  let f₂ : (S.γ → R3 k) →ₗ[k] (H.β → R3 k) :=
    S.d₂.restrictScalars k
  let f₃ : (T.δ → R3 k) →ₗ[k] (S.γ → R3 k) :=
    T.d₃.restrictScalars k
  let Q₀ : MatlisDual I →ₗ[k] MatlisDual I :=
    matlisComponent I hA.homogeneous (e - n)
  have hP₁def : H.shiftedComponent n = P₁ := by
    apply LinearMap.ext
    intro c
    funext b
    rfl
  have hP₂def : S.shiftedComponent n = P₂ := by
    apply LinearMap.ext
    intro c
    funext b
    rfl
  have hP₃def (c : T.δ → R3 k) :
      HomogeneousFirstRelations.HomogeneousSecondRelations.HomogeneousThirdRelations.shiftedComponent
        T n c = P₃ c := by
    funext a
    rfl
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₀) := by
    exact (shiftedRangeEquiv (k := k) (fun _ : Fin 2 => 0) n).symm.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₁) := by
    exact (shiftedRangeEquiv (k := k) H.degree n).symm.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₂) := by
    exact (shiftedRangeEquiv (k := k) S.degree n).symm.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₃) := by
    exact (shiftedRangeEquiv (k := k) T.degree n).symm.finiteDimensional
  have hP₀ : P₀.comp P₀ = P₀ := by
    exact shiftedProjection_idem (k := k) (fun _ : Fin 2 => 0) n
  have hP₁ : P₁.comp P₁ = P₁ := by
    exact shiftedProjection_idem (k := k) H.degree n
  have hP₂ : P₂.comp P₂ = P₂ := by
    exact shiftedProjection_idem (k := k) S.degree n
  have hP₃ : P₃.comp P₃ = P₃ := by
    exact shiftedProjection_idem (k := k) T.degree n
  have hcomm₀ : f₀.comp P₀ = Q₀.comp f₀ := by
    apply LinearMap.ext
    intro u
    simpa [f₀, P₀, Q₀, vectorProjection_eq_shifted (k := k) n] using
      inverseSystemMap_vectorComponent hA hne u
  have hcomm₁ : f₁.comp P₁ = P₀.comp f₁ := by
    apply LinearMap.ext
    intro c
    simpa [f₁, P₀, P₁, shiftedProjection, vectorProjection_eq_shifted (k := k) n,
      HomogeneousFirstRelations.shiftedComponent] using
      H.d₁_shiftedComponent n c
  have hcomm₂ : f₂.comp P₂ = P₁.comp f₂ := by
    apply LinearMap.ext
    intro c
    have hh := S.d₂_shiftedComponent n c
    rw [hP₂def, hP₁def] at hh
    simpa [f₂] using hh
  have hcomm₃ : f₃.comp P₃ = P₂.comp f₃ := by
    apply LinearMap.ext
    intro c
    have hh := T.d₃_shiftedComponent n c
    rw [hP₃def c, hP₂def] at hh
    simpa [f₃] using hh
  have hrange₁₀ : LinearMap.range f₁ = LinearMap.ker f₀ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun g => g c) H.inverseSystemMap_comp_d₁
      change inverseSystemMap hA (H.d₁ c) = 0
      simpa [LinearMap.comp_apply] using hc
    · intro hx
      have hxR : x ∈ LinearMap.ker (inverseSystemMap hA) := by
        change inverseSystemMap hA x = 0
        exact LinearMap.mem_ker.mp hx
      change x ∈ inverseSystemKernel hA at hxR
      rw [← H.range_d₁_eq_kernel] at hxR
      obtain ⟨c, hc⟩ := hxR
      refine ⟨c, ?_⟩
      exact hc
  have hrange₂₁ : LinearMap.range f₂ = LinearMap.ker f₁ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun g => g c) S.d₁_comp_d₂
      change H.d₁ (S.d₂ c) = 0
      exact hc
    · intro hx
      have hxR : x ∈ LinearMap.ker H.d₁ := by
        exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)
      rw [← S.range_d₂_eq_kernel] at hxR
      obtain ⟨c, hc⟩ := hxR
      refine ⟨c, ?_⟩
      exact hc
  have hrange₃₂ : LinearMap.range f₃ = LinearMap.ker f₂ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun g => g c) T.d₂_comp_d₃
      change S.d₂ (T.d₃ c) = 0
      exact hc
    · intro hx
      have hxR : x ∈ LinearMap.ker S.d₂ := by
        exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)
      rw [← T.range_d₃_eq_kernel] at hxR
      obtain ⟨c, hc⟩ := hxR
      refine ⟨c, ?_⟩
      exact hc
  have hrange₁ : LinearMap.range (rangeMap f₁ P₁ P₀ hcomm₁) =
      LinearMap.ker (rangeMap f₀ P₀ Q₀ hcomm₀) :=
    rangeMap_range_eq_ker f₁ f₀ P₁ P₀ Q₀ hcomm₁ hcomm₀ hP₀ hrange₁₀
  have hrange₂ : LinearMap.range (rangeMap f₂ P₂ P₁ hcomm₂) =
      LinearMap.ker (rangeMap f₁ P₁ P₀ hcomm₁) :=
    rangeMap_range_eq_ker f₂ f₁ P₂ P₁ P₀ hcomm₂ hcomm₁ hP₁ hrange₂₁
  have hrange₃ : LinearMap.range (rangeMap f₃ P₃ P₂ hcomm₃) =
      LinearMap.ker (rangeMap f₂ P₂ P₁ hcomm₂) :=
    rangeMap_range_eq_ker f₃ f₂ P₃ P₂ P₁ hcomm₃ hcomm₂ hP₂ hrange₃₂
  have hinj₃ : Function.Injective (rangeMap f₃ P₃ P₂ hcomm₃) := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : f₃ (x.1 - y.1) = 0 := by
      have h := congrArg Subtype.val hxy
      simpa [rangeMap_apply_val] using sub_eq_zero.mpr h
    have hzero : T.d₃ (x.1 - y.1) = 0 := by
      simpa [f₃] using hxy'
    have htd : T.d₃ = C.d₃ := C.thirdRelations_d₃_eq
    have hzero' : C.d₃ (x.1 - y.1) = 0 := by simpa [htd] using hzero
    apply sub_eq_zero.mp
    apply C.d₃_injective
    simpa using hzero'
  let E : LinearMap.range Q₀ ≃ₗ[k] gradedDualPiece I e n := by
    simpa [Q₀, matlisPiece] using
      (matlisPieceEquiv I hA.homogeneous (e - n))
  letI : FiniteDimensional k (LinearMap.range Q₀) := E.symm.finiteDimensional
  have hsurj₀ : Function.Surjective (rangeMap f₀ P₀ Q₀ hcomm₀) := by
    intro y
    have hne' : e - n ≤ e := Nat.sub_le _ _
    obtain ⟨u, hu⟩ := inverseSystemPieceMap_surjective hA hne' (E y)
    have huHom : ∀ i, MvPolynomial.IsHomogeneous (u i).1 n := by
      intro i
      have huMem : (u i).1 ∈
          MvPolynomial.homogeneousSubmodule (Fin 3) k n := by
        simpa [Nat.sub_sub_self hne] using (u i).2
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp huMem
    let c : Fin 2 → R3 k := fun i => (u i).1
    have hcP : P₀ c = c := by
      funext i
      change MvPolynomial.homogeneousComponent n (u i).1 = (u i).1
      rw [MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (huHom i))]
      simp
    let x : LinearMap.range P₀ := ⟨c, ⟨c, hcP⟩⟩
    refine ⟨x, ?_⟩
    apply E.injective
    have hleft := matlisPieceRestrict_inverseSystemMap hA hne' u
    have hmemc : inverseSystemMap hA c ∈ LinearMap.range Q₀ := by
      have hcQ : Q₀ (f₀ c) = inverseSystemMap hA c := by
        have hh := congrArg (fun g => g c) hcomm₀
        simpa [LinearMap.comp_apply, hcP, f₀] using hh.symm
      rw [← hcQ]
      change Q₀ (f₀ c) ∈ LinearMap.range Q₀
      exact LinearMap.mem_range_self Q₀ (f₀ c)
    change matlisPieceRestrict I hA.homogeneous (e - n)
        ⟨inverseSystemMap hA c, hmemc⟩ = E y
    calc
      matlisPieceRestrict I hA.homogeneous (e - n)
          ⟨inverseSystemMap hA c, hmemc⟩ =
          inverseSystemPieceMap hA (e - n) u := by simpa [c] using hleft
      _ = E y := hu
  have heul := projected_euler_characteristic
    (rangeMap f₃ P₃ P₂ hcomm₃)
    (rangeMap f₂ P₂ P₁ hcomm₂)
    (rangeMap f₁ P₁ P₀ hcomm₁)
    (rangeMap f₀ P₀ Q₀ hcomm₀)
    hinj₃ hrange₃ hrange₂ hrange₁ hsurj₀
  have hfin₃ : (finrank k (LinearMap.range P₃) : ℤ) =
      shiftSum ((e : ℤ) + 3) C.rMultiplicity (n : ℤ) := by
    simpa [P₃, hTdeg, GradedMinimalFreeComplex.rMultiplicity] using
      shiftedRange_finrank_shiftSum_of_nonneg (k := k) T.degree n
        ((e : ℤ) + 3) (fun a => Int.natCast_nonneg _) (by omega)
  have hfin₂ : (finrank k (LinearMap.range P₂) : ℤ) =
      shiftSum ((e : ℤ) + 3) C.qMultiplicity (n : ℤ) := by
    simpa [P₂, hSdeg, GradedMinimalFreeComplex.qMultiplicity] using
      shiftedRange_finrank_shiftSum_of_nonneg (k := k) S.degree n
        ((e : ℤ) + 3) (fun g => Int.natCast_nonneg _) (by omega)
  have hfin₁ : (finrank k (LinearMap.range P₁) : ℤ) =
      shiftSum ((e : ℤ) + 3) C.pMultiplicity (n : ℤ) := by
    simpa [P₁, hHdeg, GradedMinimalFreeComplex.pMultiplicity] using
      shiftedRange_finrank_shiftSum_of_nonneg (k := k) H.degree n
        ((e : ℤ) + 3) (fun b => Int.natCast_nonneg _) (by omega)
  have hfin₀ : (finrank k (LinearMap.range P₀) : ℤ) =
      2 * Nz (n : ℤ) := by
    simpa [P₀, Nz_natCast] using
      (show (finrank k (LinearMap.range
          (shiftedProjection (k := k) (fun _ : Fin 2 => 0) n)) : ℤ) =
        2 * Nz (n : ℤ) by
        rw [shiftedRange_finrank]
        simp [Nz_natCast])
  have hEcast : (finrank k (LinearMap.range Q₀) : ℤ) =
      finrank k (gradedDualPiece I e n) := by
    exact_mod_cast E.finrank_eq
  have heulZ :
      (finrank k (LinearMap.range Q₀) : ℤ) +
          finrank k (LinearMap.range P₁) +
          finrank k (LinearMap.range P₃) =
        finrank k (LinearMap.range P₀) +
          finrank k (LinearMap.range P₂) := by
    exact_mod_cast heul
  rw [hEcast, hfin₁, hfin₃, hfin₀, hfin₂] at heulZ
  simpa [GradedMinimalFreeComplex.pMultiplicity,
    GradedMinimalFreeComplex.qMultiplicity,
    GradedMinimalFreeComplex.rMultiplicity] using heulZ

/-! The same projected complex is exact above the socle degree.  The target
is then zero, so the first differential is surjective on the homogeneous
piece.  We keep the upper cutoff equal to the tested degree; this is the
finite-cardinality form of the usual Euler characteristic and does not use
any regularity bound on the third shifts. -/

lemma degreewise_euler_of_minimal_above
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    ∀ n : ℕ, e < n →
      shiftSum (n : ℤ) C.pMultiplicity (n : ℤ) +
          shiftSum (n : ℤ) C.rMultiplicity (n : ℤ) =
        2 * Nz (n : ℤ) + shiftSum (n : ℤ) C.qMultiplicity (n : ℤ) := by
  classical
  letI : Fintype C.β₁ := C.fintype₁
  letI : Fintype C.β₂ := C.fintype₂
  letI : Fintype C.β₃ := C.fintype₃
  let H := C.firstRelations
  letI : Fintype H.β := H.fintype
  let S := C.secondRelations
  letI : Fintype S.γ := S.fintype
  let T := C.thirdRelations
  letI : Fintype T.δ := T.fintype
  have hHdeg : H.degree = C.pShift := by rfl
  have hSdeg : S.degree = C.qShift := by rfl
  have hTdeg : T.degree = C.rShift := by rfl
  intro n hne
  let P₀ : (Fin 2 → R3 k) →ₗ[k] (Fin 2 → R3 k) :=
    shiftedProjection (fun _ : Fin 2 => 0) n
  let P₁ : (H.β → R3 k) →ₗ[k] (H.β → R3 k) :=
    shiftedProjection H.degree n
  let P₂ : (S.γ → R3 k) →ₗ[k] (S.γ → R3 k) :=
    shiftedProjection S.degree n
  let P₃ : (T.δ → R3 k) →ₗ[k] (T.δ → R3 k) :=
    shiftedProjection T.degree n
  let f₁ : (H.β → R3 k) →ₗ[k] (Fin 2 → R3 k) :=
    H.d₁.restrictScalars k
  let f₂ : (S.γ → R3 k) →ₗ[k] (H.β → R3 k) :=
    S.d₂.restrictScalars k
  let f₃ : (T.δ → R3 k) →ₗ[k] (S.γ → R3 k) :=
    T.d₃.restrictScalars k
  letI : FiniteDimensional k (LinearMap.range P₀) := by
    exact (shiftedRangeEquiv (k := k) (fun _ : Fin 2 => 0) n).symm.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₁) := by
    exact (shiftedRangeEquiv (k := k) H.degree n).symm.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₂) := by
    exact (shiftedRangeEquiv (k := k) S.degree n).symm.finiteDimensional
  letI : FiniteDimensional k (LinearMap.range P₃) := by
    exact (shiftedRangeEquiv (k := k) T.degree n).symm.finiteDimensional
  have hP₀ : P₀.comp P₀ = P₀ := by
    exact shiftedProjection_idem (k := k) (fun _ : Fin 2 => 0) n
  have hP₁ : P₁.comp P₁ = P₁ := by
    exact shiftedProjection_idem (k := k) H.degree n
  have hP₂ : P₂.comp P₂ = P₂ := by
    exact shiftedProjection_idem (k := k) S.degree n
  have hcomm₁ : f₁.comp P₁ = P₀.comp f₁ := by
    apply LinearMap.ext
    intro c
    simpa [f₁, P₀, P₁, shiftedProjection,
      vectorProjection_eq_shifted (k := k) n,
      HomogeneousFirstRelations.shiftedComponent] using
      H.d₁_shiftedComponent n c
  have hcomm₂ : f₂.comp P₂ = P₁.comp f₂ := by
    apply LinearMap.ext
    intro c
    have hh := S.d₂_shiftedComponent n c
    have hP₂def : S.shiftedComponent n = P₂ := by
      apply LinearMap.ext
      intro u
      funext b
      rfl
    have hP₁def : H.shiftedComponent n = P₁ := by
      apply LinearMap.ext
      intro u
      funext b
      rfl
    rw [hP₂def, hP₁def] at hh
    simpa [f₂] using hh
  have hcomm₃ : f₃.comp P₃ = P₂.comp f₃ := by
    apply LinearMap.ext
    intro c
    have hh := T.d₃_shiftedComponent n c
    have hP₃def (u : T.δ → R3 k) : T.shiftedComponent n u = P₃ u := by
      funext a
      rfl
    have hP₂def : S.shiftedComponent n = P₂ := by
      apply LinearMap.ext
      intro u
      funext b
      rfl
    rw [hP₃def c, hP₂def] at hh
    simpa [f₃] using hh
  have hrange₂₁ : LinearMap.range f₂ = LinearMap.ker f₁ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun g => g c) S.d₁_comp_d₂
      change H.d₁ (S.d₂ c) = 0
      exact hc
    · intro hx
      have hxR : x ∈ LinearMap.ker H.d₁ := by
        exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)
      rw [← S.range_d₂_eq_kernel] at hxR
      obtain ⟨c, hc⟩ := hxR
      refine ⟨c, ?_⟩
      exact hc
  have hrange₃₂ : LinearMap.range f₃ = LinearMap.ker f₂ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun g => g c) T.d₂_comp_d₃
      change S.d₂ (T.d₃ c) = 0
      exact hc
    · intro hx
      have hxR : x ∈ LinearMap.ker S.d₂ := by
        exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)
      rw [← T.range_d₃_eq_kernel] at hxR
      obtain ⟨c, hc⟩ := hxR
      refine ⟨c, ?_⟩
      exact hc
  have hrange₃ : LinearMap.range (rangeMap f₃ P₃ P₂ hcomm₃) =
      LinearMap.ker (rangeMap f₂ P₂ P₁ hcomm₂) :=
    rangeMap_range_eq_ker f₃ f₂ P₃ P₂ P₁ hcomm₃ hcomm₂ hP₂ hrange₃₂
  have hrange₂ : LinearMap.range (rangeMap f₂ P₂ P₁ hcomm₂) =
      LinearMap.ker (rangeMap f₁ P₁ P₀ hcomm₁) := by
    exact rangeMap_range_eq_ker f₂ f₁ P₂ P₁ P₀
      hcomm₂ hcomm₁ hP₁ hrange₂₁
  have hinj₃ : Function.Injective (rangeMap f₃ P₃ P₂ hcomm₃) := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : f₃ (x.1 - y.1) = 0 := by
      have h := congrArg Subtype.val hxy
      simpa [rangeMap_apply_val] using sub_eq_zero.mpr h
    have hzero : T.d₃ (x.1 - y.1) = 0 := by
      simpa [f₃] using hxy'
    have htd : T.d₃ = C.d₃ := C.thirdRelations_d₃_eq
    have hzero' : C.d₃ (x.1 - y.1) = 0 := by simpa [htd] using hzero
    apply sub_eq_zero.mp
    apply C.d₃_injective
    simpa using hzero'
  have hsurj₁ : Function.Surjective (rangeMap f₁ P₁ P₀ hcomm₁) := by
    intro y
    have hyfix : P₀ y.1 = y.1 := by
      obtain ⟨u, hu⟩ := y.2
      have hh := congrArg (fun g => g u) hP₀
      simpa [LinearMap.comp_apply, hu] using hh
    have hyhom : inverseSystemMap hA y.1 = 0 := by
      have hhigh := inverseSystemMap_vectorComponent_high hA hne y.1
      have hcomponent : vectorHomogeneousComponent n y.1 = y.1 := by
        simpa [P₀, vectorProjection_eq_shifted (k := k) n] using hyfix
      rw [← hcomponent]
      exact hhigh
    have hyker : y.1 ∈ LinearMap.ker (inverseSystemMap hA) :=
      LinearMap.mem_ker.mpr hyhom
    change y.1 ∈ inverseSystemKernel hA at hyker
    rw [← H.range_d₁_eq_kernel] at hyker
    obtain ⟨c, hc⟩ := hyker
    let x : LinearMap.range P₁ := ⟨P₁ c, ⟨c, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    have hh := congrArg (fun g => g c) hcomm₁
    change f₁ (P₁ c) = y.1
    calc
      f₁ (P₁ c) = P₀ (f₁ c) := by
        simpa [LinearMap.comp_apply] using hh
      _ = P₀ (H.d₁ c) := by rfl
      _ = P₀ y.1 := by rw [hc]
      _ = y.1 := hyfix
  let g₀ : LinearMap.range P₀ →ₗ[k] (Fin 0 → k) := 0
  have hker₀ : LinearMap.ker g₀ = (⊤ : Submodule k (LinearMap.range P₀)) := by
    apply top_unique
    intro x hx
    simp [g₀]
  have hrange₁ : LinearMap.range (rangeMap f₁ P₁ P₀ hcomm₁) =
      LinearMap.ker g₀ := by
    rw [hker₀]
    exact LinearMap.range_eq_top.mpr hsurj₁
  have hsurj₀ : Function.Surjective g₀ := by
    intro y
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  have heul := projected_euler_characteristic
    (rangeMap f₃ P₃ P₂ hcomm₃)
    (rangeMap f₂ P₂ P₁ hcomm₂)
    (rangeMap f₁ P₁ P₀ hcomm₁)
    g₀ hinj₃ hrange₃ hrange₂ hrange₁ hsurj₀
  have hfin₃ : (finrank k (LinearMap.range P₃) : ℤ) =
      shiftSum (n : ℤ) C.rMultiplicity (n : ℤ) := by
    simpa [P₃, hTdeg, GradedMinimalFreeComplex.rMultiplicity] using
      shiftedRange_finrank_shiftSum_of_nonneg (k := k) T.degree n
        (n : ℤ) (fun a => Int.natCast_nonneg _) (by omega)
  have hfin₂ : (finrank k (LinearMap.range P₂) : ℤ) =
      shiftSum (n : ℤ) C.qMultiplicity (n : ℤ) := by
    simpa [P₂, hSdeg, GradedMinimalFreeComplex.qMultiplicity] using
      shiftedRange_finrank_shiftSum_of_nonneg (k := k) S.degree n
        (n : ℤ) (fun g => Int.natCast_nonneg _) (by omega)
  have hfin₁ : (finrank k (LinearMap.range P₁) : ℤ) =
      shiftSum (n : ℤ) C.pMultiplicity (n : ℤ) := by
    simpa [P₁, hHdeg, GradedMinimalFreeComplex.pMultiplicity] using
      shiftedRange_finrank_shiftSum_of_nonneg (k := k) H.degree n
        (n : ℤ) (fun b => Int.natCast_nonneg _) (by omega)
  have hfin₀ : (finrank k (LinearMap.range P₀) : ℤ) =
      2 * Nz (n : ℤ) := by
    simpa [P₀, Nz_natCast] using
      (show (finrank k (LinearMap.range
          (shiftedProjection (k := k) (fun _ : Fin 2 => 0) n)) : ℤ) =
        2 * Nz (n : ℤ) by
        rw [shiftedRange_finrank]
        simp [Nz_natCast])
  have heulZ :
      (finrank k (Fin 0 → k) : ℤ) +
          finrank k (LinearMap.range P₁) +
          finrank k (LinearMap.range P₃) =
        finrank k (LinearMap.range P₀) +
          finrank k (LinearMap.range P₂) := by
    exact_mod_cast heul
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hfin₁,
    hfin₃, hfin₀, hfin₂] at heulZ
  simpa using heulZ

lemma shiftSum_second_diff_above
    (u : ℤ) (f : ℤ → ℤ) (d : ℤ) (hu : 0 ≤ u) (hud : u ≤ d) :
    shiftSum u f d - 2 * shiftSum u f (d - 1) +
        shiftSum u f (d - 2) =
      ∑ b ∈ Finset.Icc (0 : ℤ) u, f b := by
  have hstep : ∀ b ∈ Finset.Icc (0 : ℤ) u,
      f b * Nz (d - b) - 2 * (f b * Nz (d - 1 - b)) +
          f b * Nz (d - 2 - b) = f b := by
    intro b hb
    have h1 : d - 1 - b = d - b - 1 := by ring
    have h2 : d - 2 - b = d - b - 2 := by ring
    rw [h1, h2]
    have h := Nz_second_diff (d - b)
    have hb' := Finset.mem_Icc.mp hb
    rw [if_pos (by omega)] at h
    linear_combination f b * h
  unfold shiftSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl hstep]

lemma minimal_complex_cardinality_euler
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    @Fintype.card C.β₁ C.fintype₁ + @Fintype.card C.β₃ C.fintype₃ =
      @Fintype.card C.β₂ C.fintype₂ + 2 := by
  classical
  let U : ℕ := e + 1 +
    (∑ b : C.β₁, C.pShift b) +
    (∑ g : C.β₂, C.qShift g) +
    (∑ a : C.β₃, C.rShift a)
  have hpU : ∀ b : C.β₁, C.pShift b ≤ U := by
    intro b
    have hs : C.pShift b ≤ ∑ x : C.β₁, C.pShift x := by
      exact Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_univ b)
    dsimp [U]
    omega
  have hqU : ∀ g : C.β₂, C.qShift g ≤ U := by
    intro g
    have hs : C.qShift g ≤ ∑ x : C.β₂, C.qShift x := by
      exact Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_univ g)
    dsimp [U]
    omega
  have hrU : ∀ a : C.β₃, C.rShift a ≤ U := by
    intro a
    have hs : C.rShift a ≤ ∑ x : C.β₃, C.rShift x := by
      exact Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_univ a)
    dsimp [U]
    omega
  have hvan_p : ∀ b : ℤ, (U : ℤ) < b → C.pMultiplicity b = 0 := by
    intro b hb
    unfold GradedMinimalFreeComplex.pMultiplicity shiftMultiplicity
    apply congrArg Int.ofNat
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x _ hx
    have hxU : C.pShift x ≤ U := hpU x
    have hx' : (C.pShift x : ℤ) = b := by simpa using hx
    omega
  have hvan_q : ∀ b : ℤ, (U : ℤ) < b → C.qMultiplicity b = 0 := by
    intro b hb
    unfold GradedMinimalFreeComplex.qMultiplicity shiftMultiplicity
    apply congrArg Int.ofNat
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x _ hx
    have hxU : C.qShift x ≤ U := hqU x
    have hx' : (C.qShift x : ℤ) = b := by simpa using hx
    omega
  have hvan_r : ∀ b : ℤ, (U : ℤ) < b → C.rMultiplicity b = 0 := by
    intro b hb
    unfold GradedMinimalFreeComplex.rMultiplicity shiftMultiplicity
    apply congrArg Int.ofNat
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x _ hx
    have hxU : C.rShift x ≤ U := hrU x
    have hx' : (C.rShift x : ℤ) = b := by simpa using hx
    omega
  have hcut : ∀ (f : ℤ → ℤ),
      (∀ b, (U : ℤ) < b → f b = 0) →
      ∀ t : ℕ, U ≤ t →
        shiftSum (t : ℤ) f (t : ℤ) = shiftSum (U : ℤ) f (t : ℤ) := by
    intro f hf t hUt
    unfold shiftSum
    symm
    have hUt' : (U : ℤ) ≤ (t : ℤ) := by exact_mod_cast hUt
    apply Finset.sum_subset
      (show Finset.Icc (0 : ℤ) (U : ℤ) ⊆ Finset.Icc (0 : ℤ) (t : ℤ) by
        intro b hb
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hb).1,
          (Finset.mem_Icc.mp hb).2.trans hUt'⟩)
    intro b hb hnot
    have hbU : (U : ℤ) < b := by
      have hbt : b ≤ (t : ℤ) := (Finset.mem_Icc.mp hb).2
      have hnot' : ¬ b ≤ (U : ℤ) := by
        intro hle
        apply hnot
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hb).1, hle⟩
      exact lt_of_not_ge hnot'
    rw [hf b hbU, zero_mul]
  have hE0 := degreewise_euler_of_minimal_above hA C U (by dsimp [U]; omega)
  have hE1 := degreewise_euler_of_minimal_above hA C (U + 1) (by dsimp [U]; omega)
  have hE2 := degreewise_euler_of_minimal_above hA C (U + 2) (by dsimp [U]; omega)
  have hE1' :
      shiftSum (U : ℤ) C.pMultiplicity ((U + 1 : ℕ) : ℤ) +
          shiftSum (U : ℤ) C.rMultiplicity ((U + 1 : ℕ) : ℤ) =
        2 * Nz ((U + 1 : ℕ) : ℤ) +
          shiftSum (U : ℤ) C.qMultiplicity ((U + 1 : ℕ) : ℤ) := by
    rw [← hcut C.pMultiplicity hvan_p (U + 1) (by omega),
      ← hcut C.rMultiplicity hvan_r (U + 1) (by omega),
      ← hcut C.qMultiplicity hvan_q (U + 1) (by omega)]
    exact hE1
  have hE2' :
      shiftSum (U : ℤ) C.pMultiplicity ((U + 2 : ℕ) : ℤ) +
          shiftSum (U : ℤ) C.rMultiplicity ((U + 2 : ℕ) : ℤ) =
        2 * Nz ((U + 2 : ℕ) : ℤ) +
          shiftSum (U : ℤ) C.qMultiplicity ((U + 2 : ℕ) : ℤ) := by
    rw [← hcut C.pMultiplicity hvan_p (U + 2) (by omega),
      ← hcut C.rMultiplicity hvan_r (U + 2) (by omega),
      ← hcut C.qMultiplicity hvan_q (U + 2) (by omega)]
    exact hE2
  have hsecond_p := shiftSum_second_diff_above
    (U : ℤ) C.pMultiplicity ((U + 2 : ℕ) : ℤ) (by omega) (by omega)
  have hsecond_q := shiftSum_second_diff_above
    (U : ℤ) C.qMultiplicity ((U + 2 : ℕ) : ℤ) (by omega) (by omega)
  have hsecond_r := shiftSum_second_diff_above
    (U : ℤ) C.rMultiplicity ((U + 2 : ℕ) : ℤ) (by omega) (by omega)
  have hNz := Nz_second_diff ((U + 2 : ℕ) : ℤ)
  rw [if_pos (by omega)] at hNz
  have hcard_p :
      (∑ b ∈ Finset.Icc (0 : ℤ) (U : ℤ), C.pMultiplicity b) =
        (@Fintype.card C.β₁ C.fintype₁ : ℤ) := by
    rw [show C.pMultiplicity =
      @shiftMultiplicity C.β₁ C.fintype₁ (fun b => (C.pShift b : ℤ)) by rfl,
      sum_shiftMultiplicity_Icc]
    norm_cast
    have heq : Finset.univ.filter (fun b : C.β₁ =>
        0 ≤ C.pShift b ∧ C.pShift b ≤ U) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro b hb
      exact ⟨Nat.zero_le _, hpU b⟩
    rw [heq]
    simp
  have hcard_q :
      (∑ b ∈ Finset.Icc (0 : ℤ) (U : ℤ), C.qMultiplicity b) =
        (@Fintype.card C.β₂ C.fintype₂ : ℤ) := by
    rw [show C.qMultiplicity =
      @shiftMultiplicity C.β₂ C.fintype₂ (fun g => (C.qShift g : ℤ)) by rfl,
      sum_shiftMultiplicity_Icc]
    norm_cast
    have heq : Finset.univ.filter (fun g : C.β₂ =>
        0 ≤ C.qShift g ∧ C.qShift g ≤ U) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro g hg
      exact ⟨Nat.zero_le _, hqU g⟩
    rw [heq]
    simp
  have hcard_r :
      (∑ b ∈ Finset.Icc (0 : ℤ) (U : ℤ), C.rMultiplicity b) =
        (@Fintype.card C.β₃ C.fintype₃ : ℤ) := by
    rw [show C.rMultiplicity =
      @shiftMultiplicity C.β₃ C.fintype₃ (fun a => (C.rShift a : ℤ)) by rfl,
      sum_shiftMultiplicity_Icc]
    norm_cast
    have heq : Finset.univ.filter (fun a : C.β₃ =>
        0 ≤ C.rShift a ∧ C.rShift a ≤ U) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro a ha
      exact ⟨Nat.zero_le _, hrU a⟩
    rw [heq]
    simp
  have hsecond_p' :
      shiftSum (U : ℤ) C.pMultiplicity ((U + 2 : ℕ) : ℤ) -
          2 * shiftSum (U : ℤ) C.pMultiplicity ((U + 1 : ℕ) : ℤ) +
          shiftSum (U : ℤ) C.pMultiplicity (U : ℤ) =
        ∑ b ∈ Finset.Icc (0 : ℤ) (U : ℤ), C.pMultiplicity b := by
    have hcast1 : ((U + 2 : ℕ) : ℤ) - 1 = ((U + 1 : ℕ) : ℤ) := by omega
    have hcast0 : ((U + 2 : ℕ) : ℤ) - 2 = (U : ℤ) := by omega
    rw [hcast1, hcast0] at hsecond_p
    exact hsecond_p
  have hsecond_q' :
      shiftSum (U : ℤ) C.qMultiplicity ((U + 2 : ℕ) : ℤ) -
          2 * shiftSum (U : ℤ) C.qMultiplicity ((U + 1 : ℕ) : ℤ) +
          shiftSum (U : ℤ) C.qMultiplicity (U : ℤ) =
        ∑ b ∈ Finset.Icc (0 : ℤ) (U : ℤ), C.qMultiplicity b := by
    have hcast1 : ((U + 2 : ℕ) : ℤ) - 1 = ((U + 1 : ℕ) : ℤ) := by omega
    have hcast0 : ((U + 2 : ℕ) : ℤ) - 2 = (U : ℤ) := by omega
    rw [hcast1, hcast0] at hsecond_q
    exact hsecond_q
  have hsecond_r' :
      shiftSum (U : ℤ) C.rMultiplicity ((U + 2 : ℕ) : ℤ) -
          2 * shiftSum (U : ℤ) C.rMultiplicity ((U + 1 : ℕ) : ℤ) +
          shiftSum (U : ℤ) C.rMultiplicity (U : ℤ) =
        ∑ b ∈ Finset.Icc (0 : ℤ) (U : ℤ), C.rMultiplicity b := by
    have hcast1 : ((U + 2 : ℕ) : ℤ) - 1 = ((U + 1 : ℕ) : ℤ) := by omega
    have hcast0 : ((U + 2 : ℕ) : ℤ) - 2 = (U : ℤ) := by omega
    rw [hcast1, hcast0] at hsecond_r
    exact hsecond_r
  have hNz' :
      Nz ((U + 2 : ℕ) : ℤ) - 2 * Nz ((U + 1 : ℕ) : ℤ) + Nz (U : ℤ) = 1 := by
    have hcast1 : ((U + 2 : ℕ) : ℤ) - 1 = ((U + 1 : ℕ) : ℤ) := by omega
    have hcast0 : ((U + 2 : ℕ) : ℤ) - 2 = (U : ℤ) := by omega
    rw [hcast1, hcast0] at hNz
    exact hNz
  have hlinear :
      (shiftSum (U : ℤ) C.pMultiplicity ((U + 2 : ℕ) : ℤ) -
          2 * shiftSum (U : ℤ) C.pMultiplicity ((U + 1 : ℕ) : ℤ) +
          shiftSum (U : ℤ) C.pMultiplicity (U : ℤ)) +
          (shiftSum (U : ℤ) C.rMultiplicity ((U + 2 : ℕ) : ℤ) -
            2 * shiftSum (U : ℤ) C.rMultiplicity ((U + 1 : ℕ) : ℤ) +
            shiftSum (U : ℤ) C.rMultiplicity (U : ℤ)) =
        2 * (Nz ((U + 2 : ℕ) : ℤ) -
          2 * Nz ((U + 1 : ℕ) : ℤ) + Nz (U : ℤ)) +
          (shiftSum (U : ℤ) C.qMultiplicity ((U + 2 : ℕ) : ℤ) -
            2 * shiftSum (U : ℤ) C.qMultiplicity ((U + 1 : ℕ) : ℤ) +
            shiftSum (U : ℤ) C.qMultiplicity (U : ℤ)) := by
    linear_combination hE2' - 2 * hE1' + hE0
  rw [hsecond_p', hsecond_r', hsecond_q', hNz', hcard_p, hcard_q, hcard_r] at hlinear
  exact_mod_cast (by omega :
    (@Fintype.card C.β₁ C.fintype₁ : ℤ) +
        (@Fintype.card C.β₃ C.fintype₃ : ℤ) =
      (@Fintype.card C.β₂ C.fintype₂ : ℤ) + 2)

noncomputable def paddedPMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : ℤ → ℤ :=
  fun d => C.pMultiplicity d + C.rMultiplicity d

noncomputable def paddedQMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : ℤ → ℤ :=
  fun d => C.qMultiplicity d + if d = (e : ℤ) + 3 then 1 else 0

lemma shiftMultiplicity_fin_one
    {A : Type*} [Fintype A] (a : A) (f : A → ℤ) (d : ℤ) :
    shiftMultiplicity (fun _ : Fin 1 => d) d = 1 := by
  classical
  unfold shiftMultiplicity
  simp

lemma shiftSum_add (u : ℤ) (f g : ℤ → ℤ) (t : ℤ) :
    shiftSum u (fun d => f d + g d) t =
      shiftSum u f t + shiftSum u g t := by
  unfold shiftSum
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

lemma shiftSum_third_diff (u : ℤ) (f : ℤ → ℤ) (d : ℤ)
    (hd : 1 ≤ d) (hdu : d ≤ u) :
    shiftSum u f d - 3 * shiftSum u f (d - 1) +
        3 * shiftSum u f (d - 2) - shiftSum u f (d - 3) = f d := by
  have h₁ := shiftSum_second_diff u f d (by omega) hdu
  have h₂ := shiftSum_second_diff u f (d - 1) (by omega) (by omega)
  have hset : Finset.Icc (0 : ℤ) d =
      insert d (Finset.Icc (0 : ℤ) (d - 1)) := by
    symm
    simpa [sub_eq_add_neg] using
      (Finset.insert_Icc_right_eq_Icc_add_one
        (a := (0 : ℤ)) (b := d - 1) (by omega))
  have hsum :
      (∑ b ∈ Finset.Icc (0 : ℤ) d, f b) =
        f d + ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), f b := by
    have hnot : d ∉ Finset.Icc (0 : ℤ) (d - 1) := by
      simp [show ¬ d ≤ d - 1 by omega]
    rw [hset, Finset.sum_insert hnot]
  rw [hsum] at h₁
  have h₂' :
      shiftSum u f (d - 1) - 2 * shiftSum u f (d - 2) +
          shiftSum u f (d - 3) =
        ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), f b := by
    convert h₂ using 1 <;> ring
  linear_combination h₁ - h₂'

lemma degreewise_exact_padded
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    ∀ n : ℕ, n ≤ e → Nonempty
      (ExactPresentation k (gradedDualPiece I e n)
        (shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ)).toNat
        (shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ)).toNat
        (2 * Nz (n : ℤ)).toNat) := by
  classical
  letI : Fintype C.β₁ := C.fintype₁
  letI : Fintype C.β₂ := C.fintype₂
  letI : Fintype C.β₃ := C.fintype₃
  let pShift' : (C.β₁ ⊕ C.β₃) → ℤ :=
    Sum.elim (fun b => (C.pShift b : ℤ)) (fun a => (C.rShift a : ℤ))
  let qShift' : (C.β₂ ⊕ Fin 1) → ℤ :=
    Sum.elim (fun g => (C.qShift g : ℤ)) (fun _ => (e : ℤ) + 3)
  have hpMult : ∀ d : ℤ,
      shiftMultiplicity pShift' d = paddedPMultiplicity C d := by
    intro d
    rw [show pShift' = Sum.elim (fun b => (C.pShift b : ℤ))
      (fun a => (C.rShift a : ℤ)) by rfl,
      shiftMultiplicity_sum]
    rfl
  have hqMult : ∀ d : ℤ,
      shiftMultiplicity qShift' d = paddedQMultiplicity C d := by
    intro d
    rw [show qShift' = Sum.elim (fun g => (C.qShift g : ℤ))
      (fun _ : Fin 1 => (e : ℤ) + 3) by rfl,
      shiftMultiplicity_sum]
    have hone : shiftMultiplicity (fun _ : Fin 1 => (e : ℤ) + 3) d =
        if d = (e : ℤ) + 3 then 1 else 0 := by
      by_cases h : d = (e : ℤ) + 3
      · subst d
        simpa using
          (shiftMultiplicity_fin_one 0 (fun _ : Fin 1 => (e : ℤ) + 3)
            ((e : ℤ) + 3))
      · unfold shiftMultiplicity
        have h' : ¬(e : ℤ) + 3 = d := by
          intro h'
          exact h h'.symm
        simp [h, h']
    rw [hone]
    rfl
  intro n hne
  have hExtra : shiftSum ((e : ℤ) + 3)
      (fun d : ℤ => if d = (e : ℤ) + 3 then 1 else 0) (n : ℤ) = 0 := by
    apply shiftSum_vanish
    intro d hd0 hdn
    have hne' : d ≠ (e : ℤ) + 3 := by omega
    simp [hne']
  have hpPad : shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ) =
      shiftSum ((e : ℤ) + 3) C.pMultiplicity (n : ℤ) +
        shiftSum ((e : ℤ) + 3) C.rMultiplicity (n : ℤ) := by
    rw [show paddedPMultiplicity C =
      (fun d => C.pMultiplicity d + C.rMultiplicity d) by rfl,
      shiftSum_add]
  have hqPad : shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ) =
      shiftSum ((e : ℤ) + 3) C.qMultiplicity (n : ℤ) := by
    rw [show paddedQMultiplicity C =
      (fun d => C.qMultiplicity d +
      (if d = (e : ℤ) + 3 then 1 else 0)) by rfl,
      shiftSum_add, hExtra, add_zero]
  have hEuler := degreewise_euler_of_minimal hA C n hne
  have hpEq : shiftSum ((e : ℤ) + 3)
      (shiftMultiplicity pShift') (n : ℤ) =
      shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ) := by
    apply congrArg (fun f => shiftSum ((e : ℤ) + 3) f (n : ℤ))
    funext d
    exact hpMult d
  have hqEq : shiftSum ((e : ℤ) + 3)
      (shiftMultiplicity qShift') (n : ℤ) =
      shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ) := by
    apply congrArg (fun f => shiftSum ((e : ℤ) + 3) f (n : ℤ))
    funext d
    exact hqMult d
  have hEuler' :
      (finrank k (gradedDualPiece I e n) : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ) =
        2 * Nz (n : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ) := by
    calc
      (finrank k (gradedDualPiece I e n) : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ) =
          (finrank k (gradedDualPiece I e n) : ℤ) +
            shiftSum ((e : ℤ) + 3) C.pMultiplicity (n : ℤ) +
            shiftSum ((e : ℤ) + 3) C.rMultiplicity (n : ℤ) := by
              rw [hpPad]
              ring
      _ = 2 * Nz (n : ℤ) +
            shiftSum ((e : ℤ) + 3) C.qMultiplicity (n : ℤ) := hEuler
      _ = 2 * Nz (n : ℤ) +
            shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ) := by
              rw [hqPad]
  have hnonnegP' : 0 ≤ shiftSum ((e : ℤ) + 3)
      (shiftMultiplicity pShift') (n : ℤ) :=
    shiftSum_nonneg _ (fun d => shiftMultiplicity_nonneg _ d) _
  have hnonnegQ' : 0 ≤ shiftSum ((e : ℤ) + 3)
      (shiftMultiplicity qShift') (n : ℤ) :=
    shiftSum_nonneg _ (fun d => shiftMultiplicity_nonneg _ d) _
  have hnonnegP : 0 ≤ shiftSum ((e : ℤ) + 3)
      (paddedPMultiplicity C) (n : ℤ) := by
    rw [← hpEq]
    exact hnonnegP'
  have hnonnegQ : 0 ≤ shiftSum ((e : ℤ) + 3)
      (paddedQMultiplicity C) (n : ℤ) := by
    rw [← hqEq]
    exact hnonnegQ'
  have hnonnegM : 0 ≤ 2 * Nz (n : ℤ) :=
    mul_nonneg (by norm_num) (Nz_nonneg _)
  have hMcast : ((finrank k (gradedDualPiece I e n) : ℕ) : ℤ) =
      finrank k (gradedDualPiece I e n) := by rfl
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  have hMle : finrank k (gradedDualPiece I e n) ≤
      (2 * Nz (n : ℤ)).toNat := by
    have hsurj := inverseSystemPieceMap_surjective
      (n := e - n) hA (Nat.sub_le _ _)
    have hdim := LinearMap.finrank_le_finrank_of_surjective
      (f := inverseSystemPieceMap hA (e - n)) hsurj
    have hsource : finrank k (Fin 2 →
        homogeneousSubmodule (Fin 3) k n) =
        2 * finrank k (homogeneousSubmodule (Fin 3) k n) := by
      rw [Module.finrank_pi_fintype]
      simp
    have hN : finrank k (homogeneousSubmodule (Fin 3) k n) =
        (n + 2).choose 2 := finrank_homogeneousSubmodule k _
    have hbound : (finrank k (gradedDualPiece I e n) : ℤ) ≤
        2 * N n := by
      have hdim' : finrank k (gradedDualPiece I e n) ≤
          finrank k (Fin 2 → homogeneousSubmodule (Fin 3) k n) := by
        have hsub : e - (e - n) = n := Nat.sub_sub_self hne
        change finrank k (Module.Dual k (quotPiece I (e - n))) ≤
          finrank k (Fin 2 → homogeneousSubmodule (Fin 3) k n)
        rw [hsub] at hdim
        exact hdim
      rw [hsource, hN] at hdim'
      change (finrank k (gradedDualPiece I e n) : ℤ) ≤
        2 * ((n + 2).choose 2 : ℤ)
      exact_mod_cast hdim'
    have hbound' : (finrank k (gradedDualPiece I e n) : ℤ) ≤
        2 * Nz (n : ℤ) := by
      rw [Nz_natCast n]
      simpa [N] using hbound
    have hcastM : ((2 * Nz (n : ℤ)).toNat : ℤ) =
        2 * Nz (n : ℤ) := Int.toNat_of_nonneg hnonnegM
    have hboundZ : (finrank k (gradedDualPiece I e n) : ℤ) ≤
        ((2 * Nz (n : ℤ)).toNat : ℤ) := by
      rw [hcastM]
      exact hbound'
    exact_mod_cast hboundZ
  have hEulerNat : finrank k (gradedDualPiece I e n) +
      (shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ)).toNat =
    (2 * Nz (n : ℤ)).toNat +
      (shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ)).toNat := by
    have hcastP : ((shiftSum ((e : ℤ) + 3)
        (paddedPMultiplicity C) (n : ℤ)).toNat : ℤ) =
        shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ) :=
      Int.toNat_of_nonneg hnonnegP
    have hcastQ : ((shiftSum ((e : ℤ) + 3)
        (paddedQMultiplicity C) (n : ℤ)).toNat : ℤ) =
        shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ) :=
      Int.toNat_of_nonneg hnonnegQ
    have hcastM' : ((2 * Nz (n : ℤ)).toNat : ℤ) =
        2 * Nz (n : ℤ) := Int.toNat_of_nonneg hnonnegM
    have hEulerZ :
        (finrank k (gradedDualPiece I e n) : ℤ) +
            ((shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C)
              (n : ℤ)).toNat : ℤ) =
          ((2 * Nz (n : ℤ)).toNat : ℤ) +
            ((shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C)
              (n : ℤ)).toNat : ℤ) := by
      rw [hcastP, hcastQ, hcastM']
      exact hEuler'
    exact_mod_cast hEulerZ
  have hm₂m₁ :
      (shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ)).toNat ≤
        (shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ)).toNat := by
    have hMle' : finrank k (gradedDualPiece I e n) ≤
        (2 * Nz (n : ℤ)).toNat := hMle
    omega
  exact exactPresentationOfFinrank hMle hm₂m₁ hEulerNat

/-! ## The first graded regularity bound

The following lemma is the only place where the fact that the irrelevant
ideal is generated by the variables is used in the shift bookkeeping.  It is
proved by taking the homogeneous-submodule power decomposition, rather than
by dividing Euler's identity (which would be invalid in positive
characteristic).
-/

lemma homogeneous_mem_irrelevant_mul_homogeneous
    {n : ℕ} {f : R3 k}
    (hf : MvPolynomial.IsHomogeneous f (n + 1)) :
    f ∈ (MvPolynomial.homogeneousSubmodule (Fin 3) k 1) *
      (MvPolynomial.homogeneousSubmodule (Fin 3) k n) := by
  have hmem : f ∈
      (MvPolynomial.homogeneousSubmodule (Fin 3) k 1) ^ (n + 1) := by
    rw [MvPolynomial.homogeneousSubmodule_one_pow]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hf
  rw [pow_succ] at hmem
  simpa [mul_comm] using hmem

/-! The top socle of the dual module.

The minimal-resolution argument needs the one-dimensional socle on the dual
side, not merely the two-dimensional top piece used to start the
presentation.  We record it directly from the contragredient action.  This
is the elementary graded Matlis calculation: a functional killed by all
variables vanishes on every positive-degree quotient piece, so it is exactly a
functional supported on the degree-zero piece of `R / I`.
-/

noncomputable def matlisDualSocle
    {I : Ideal (R3 k)} (hA : IsTypeTwoLevel I e) :
    Submodule k (MatlisDual I) where
  carrier := {φ | ∀ j : Fin 3, (MvPolynomial.X j : R3 k) • φ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro φ ψ hφ hψ j
    rw [smul_add, hφ j, hψ j, add_zero]
  smul_mem' := by
    intro c φ hφ j
    apply MatlisDual.ext
    apply LinearMap.ext
    intro x
    have hz := congrArg (fun ψ : MatlisDual I => ψ x) (hφ j)
    change (c • φ) (Ideal.Quotient.mk I (MvPolynomial.X j) * x) = 0
    rw [matlisDual_k_smul_apply]
    have hz' : φ (Ideal.Quotient.mk I (MvPolynomial.X j) * x) = 0 := by
      calc
        φ (Ideal.Quotient.mk I (MvPolynomial.X j) * x) =
            ((MvPolynomial.X j : R3 k) • φ) x := rfl
        _ = (0 : MatlisDual I) x := congrArg (fun ψ : MatlisDual I => ψ x)
          (hφ j)
        _ = 0 := rfl
    simp [hz']

lemma matlisDualSocle_mem_iff
    {I : Ideal (R3 k)} (hA : IsTypeTwoLevel I e) (φ : MatlisDual I) :
    φ ∈ matlisDualSocle hA ↔
      ∀ j : Fin 3, (MvPolynomial.X j : R3 k) • φ = 0 := Iff.rfl

lemma matlisDualSocle_eval_homogeneous_zero
    {I : Ideal (R3 k)} (hA : IsTypeTwoLevel I e)
    {φ : MatlisDual I} (hφ : φ ∈ matlisDualSocle hA)
    {n : ℕ} (hn : 0 < n) {f : R3 k}
    (hf : MvPolynomial.IsHomogeneous f n) :
    φ (Ideal.Quotient.mk I f) = 0 := by
  have hmul : f ∈
      (MvPolynomial.homogeneousSubmodule (Fin 3) k 1) *
        (MvPolynomial.homogeneousSubmodule (Fin 3) k (n - 1)) := by
    have hdegree : n = (n - 1) + 1 := by omega
    rw [hdegree] at hf
    exact homogeneous_mem_irrelevant_mul_homogeneous hf
  refine Submodule.mul_induction_on'
    (C := fun z _ => φ (Ideal.Quotient.mk I z) = 0) ?_ ?_ hmul
  · intro a ha b hb
    have ha' : a ∈ Submodule.span k
        (Set.range (MvPolynomial.X : Fin 3 → R3 k)) := by
      rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
      exact ha
    have hspan : φ (Ideal.Quotient.mk I (a * b)) = 0 := by
      refine Submodule.span_induction (p := fun z _ =>
        φ (Ideal.Quotient.mk I (z * b)) = 0) ?_ ?_ ?_ ?_ ha'
      · intro z hz
        obtain ⟨j, rfl⟩ := hz
        have hz' := congrArg (fun ψ : MatlisDual I => ψ
            (Ideal.Quotient.mk I b)) (hφ j)
        have hz'' : φ (Ideal.Quotient.mk I (MvPolynomial.X j) *
            Ideal.Quotient.mk I b) = 0 := by
          calc
            φ (Ideal.Quotient.mk I (MvPolynomial.X j) *
                Ideal.Quotient.mk I b) =
                ((MvPolynomial.X j : R3 k) • φ)
                  (Ideal.Quotient.mk I b) := rfl
            _ = (0 : MatlisDual I) (Ideal.Quotient.mk I b) := hz'
            _ = 0 := rfl
        simpa only [← map_mul] using hz''
      · simp
      · intro z w hz hw hzp hwp
        calc
          φ (Ideal.Quotient.mk I ((z + w) * b)) =
              φ (Ideal.Quotient.mk I (z * b) +
                Ideal.Quotient.mk I (w * b)) := by rw [add_mul, map_add]
          _ = φ (Ideal.Quotient.mk I (z * b)) +
                φ (Ideal.Quotient.mk I (w * b)) := map_add φ.val _ _
          _ = 0 := by rw [hzp, hwp, add_zero]
      · intro c z hz hzp
        rw [Algebra.smul_def]
        calc
          φ (Ideal.Quotient.mk I ((algebraMap k (R3 k) c) * z * b)) =
              φ (Ideal.Quotient.mk I (algebraMap k (R3 k) c) *
                Ideal.Quotient.mk I (z * b)) := by
                simp [← map_mul, mul_assoc]
          _ = c • φ (Ideal.Quotient.mk I (z * b)) := by
            rw [Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def,
              map_smul]
          _ = 0 := by rw [hzp, smul_zero]
    exact hspan
  · intro x hx y hy hxp hyp
    calc
      φ (Ideal.Quotient.mk I (x + y)) =
          φ (Ideal.Quotient.mk I x + Ideal.Quotient.mk I y) := by
            rw [map_add]
      _ = φ (Ideal.Quotient.mk I x) + φ (Ideal.Quotient.mk I y) :=
        map_add φ.val _ _
      _ = 0 := by rw [hxp, hyp, add_zero]

lemma matlisDualSocle_eq_matlisPiece_zero
    {I : Ideal (R3 k)} (hA : IsTypeTwoLevel I e) :
    matlisDualSocle hA = matlisPiece I hA.homogeneous 0 := by
  apply le_antisymm
  · intro φ hφ
    refine ⟨φ, ?_⟩
    apply MatlisDual.ext
    apply LinearMap.ext
    intro x
    have hsum := sum_quotientComponent hA x
    have hzero : ∀ n : ℕ, n ∈ Finset.range (e + 1) → n ≠ 0 →
        φ (quotientComponent I hA.homogeneous n x) = 0 := by
      intro n hn hne
      obtain ⟨f, hf, hmk⟩ :=
        Submodule.mem_map.mp (quotientComponent_mem_quotPiece
          I hA.homogeneous n x)
      have hfzero := matlisDualSocle_eval_homogeneous_zero hA hφ (by omega) hf
      rw [← hmk]
      exact hfzero
    have hsum' := congrArg (fun y : R3 k ⧸ I => φ y) hsum
    rw [matlisComponent_apply]
    calc
      φ (quotientComponent I hA.homogeneous 0 x) =
          φ (∑ n ∈ Finset.range (e + 1),
            quotientComponent I hA.homogeneous n x) := by
        rw [map_sum]
        symm
        apply Finset.sum_eq_single 0
        · intro n hn hne
          exact hzero n hn hne
        · simp
      _ = φ x := hsum'
  · intro φ hφ
    intro j
    have hmem := matlisPiece_smul_eq_zero_of_lt hA.homogeneous
      (MvPolynomial.isHomogeneous_X k j) (by omega) hφ
    exact hmem

lemma matlisDualSocle_finrank
    {I : Ideal (R3 k)} (hA : IsTypeTwoLevel I e) :
    finrank k (matlisDualSocle hA) = 1 := by
  rw [matlisDualSocle_eq_matlisPiece_zero hA,
    finrank_matlisPiece I hA.homogeneous 0]
  have hzero := hilb_zero I hA.proper
  rw [hilb, if_pos le_rfl] at hzero
  exact_mod_cast hzero

/-! The three coordinate variables form a regular sequence in `R3 k`.
This specialized proof uses the monomial description of coordinate ideals:
multiplication by a fresh variable cannot create membership in the ideal
generated by the preceding variables.  It is the input needed by the Rees
Ext-vanishing theorem from FormalDeps. -/

lemma X_isSMulRegular_mod_span
    (S : Set (Fin 3)) (j : Fin 3) (hj : j ∉ S) :
    IsSMulRegular
      ((R3 k) ⧸
        (Ideal.span ((MvPolynomial.X (R := k)) '' S : Set (R3 k)) •
          (⊤ : Submodule (R3 k) (R3 k))))
      (MvPolynomial.X j : R3 k) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro f hf
  have hf' : (MvPolynomial.X j : R3 k) * f ∈
      Ideal.span ((MvPolynomial.X (R := k)) '' S : Set (R3 k)) := by
    simpa only [smul_eq_mul, Ideal.mul_top] using hf
  have hsupport := MvPolynomial.mem_ideal_span_X_image.mp hf'
  have hgoal : f ∈ Ideal.span
      ((MvPolynomial.X (R := k)) '' S : Set (R3 k)) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    let m' := Finsupp.single j 1 + m
    have hm' : m' ∈ ((MvPolynomial.X j : R3 k) * f).support := by
      rw [MvPolynomial.support_X_mul]
      exact Finset.mem_map.mpr ⟨m, hm, rfl⟩
    obtain ⟨i, hiS, hi⟩ := hsupport m' hm'
    refine ⟨i, hiS, ?_⟩
    have hij : i ≠ j := by
      intro hij
      subst i
      exact hj hiS
    simpa [m', Finsupp.single_apply, hij] using hi
  simpa only [smul_eq_mul, Ideal.mul_top] using hgoal

/-- Bridge from the `Set`-indexed span to the `Ideal.ofList` form used by
`RingTheory.Sequence.isWeaklyRegular_iff`. -/
lemma ofList_map_X_eq_span (l : List (Fin 3)) :
    Ideal.ofList (l.map (MvPolynomial.X (R := k)) : List (R3 k)) =
      Ideal.span ((MvPolynomial.X (R := k)) '' {i | i ∈ l} : Set (R3 k)) := by
  unfold Ideal.ofList
  congr 1
  ext f
  simp [Set.mem_image, eq_comm]

lemma X_isSMulRegular_mod_ofList (l : List (Fin 3)) (j : Fin 3) (hj : j ∉ l) :
    IsSMulRegular
      ((R3 k) ⧸
        (Ideal.ofList (l.map (MvPolynomial.X (R := k)) : List (R3 k)) •
          (⊤ : Submodule (R3 k) (R3 k))))
      (MvPolynomial.X j : R3 k) := by
  rw [ofList_map_X_eq_span]
  exact X_isSMulRegular_mod_span _ _ (by simpa using hj)

lemma variables_isWeaklyRegular :
    RingTheory.Sequence.IsWeaklyRegular (R3 k)
      [MvPolynomial.X (R := k) (0 : Fin 3), MvPolynomial.X (R := k) (1 : Fin 3),
        MvPolynomial.X (R := k) (2 : Fin 3)] := by
  rw [RingTheory.Sequence.isWeaklyRegular_iff]
  intro i hi
  have hi3 : i < 3 := by simpa using hi
  interval_cases i
  · exact X_isSMulRegular_mod_ofList (k := k) [] 0 (by simp)
  · exact X_isSMulRegular_mod_ofList (k := k) [0] 1 (by simp)
  · exact X_isSMulRegular_mod_ofList (k := k) [0, 1] 2 (by simp)

lemma variables_isRegular :
    RingTheory.Sequence.IsRegular (R3 k)
      [MvPolynomial.X (R := k) (0 : Fin 3), MvPolynomial.X (R := k) (1 : Fin 3),
        MvPolynomial.X (R := k) (2 : Fin 3)] := by
  refine ⟨variables_isWeaklyRegular (k := k), ?_⟩
  intro htop
  let xs : List (R3 k) :=
      [MvPolynomial.X (R := k) (0 : Fin 3), MvPolynomial.X (R := k) (1 : Fin 3),
        MvPolynomial.X (R := k) (2 : Fin 3)]
  have hlist : Ideal.ofList xs = MvPolynomial.idealOfVars (Fin 3) k := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro f hf
      simp only [Set.mem_setOf_eq, xs] at hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        exact Ideal.subset_span (Set.mem_range_self _)
    · apply Ideal.span_le.mpr
      rintro f ⟨i, rfl⟩
      fin_cases i <;> apply Ideal.subset_span <;> simp [xs]
  have hone : (1 : R3 k) ∈ Ideal.ofList xs := by
    have : (1 : R3 k) ∈
        Ideal.ofList xs • (⊤ : Submodule (R3 k) (R3 k)) := by
      rw [← htop]
      trivial
    simpa only [smul_eq_mul, Ideal.mul_top] using this
  rw [hlist] at hone
  have hc : MvPolynomial.C (1 : k) ∈
      MvPolynomial.idealOfVars (Fin 3) k ^ 1 := by simpa using hone
  have h := (MvPolynomial.C_mem_pow_idealOfVars_iff
    (σ := Fin 3) (R := k) 1 1).mp hc
  simp at h

/-- The contragredient action on the full dual is faithful over `R/I`.
Equivalently, the annihilator of the Matlis dual is the original ideal.
This elementary double-dual fact is the annihilator input in the
last-differential argument; it does not use local duality. -/
lemma matlisDual_annihilator_eq_original
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    Module.annihilator (R3 k) (MatlisDual I) = I := by
  apply le_antisymm
  · intro f hf
    by_contra hfI
    have hmk : Ideal.Quotient.mk I f ≠ 0 := by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hfI
    letI : Module.Free k (R3 k ⧸ I) := Module.Free.of_divisionRing k _
    letI : Module.Projective k (R3 k ⧸ I) := Module.Projective.of_free
    obtain ⟨psi, hpsi⟩ := Projective.exists_dual_ne_zero k hmk
    let phi : MatlisDual I := ⟨psi⟩
    have hzero : f • phi = 0 := Module.mem_annihilator.mp hf phi
    have happ := congrArg (fun φ : MatlisDual I =>
      φ (Ideal.Quotient.mk I 1)) hzero
    change psi (Ideal.Quotient.mk I f * Ideal.Quotient.mk I 1) = 0 at happ
    rw [map_one, mul_one] at happ
    exact hpsi happ
  · intro f hf
    apply Module.mem_annihilator.mpr
    intro phi
    apply MatlisDual.ext
    apply LinearMap.ext
    intro x
    change phi (Ideal.Quotient.mk I f * x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, zero_mul, map_zero]

/-- Finiteness of the Matlis dual over the polynomial ring.  It is finite
dimensional over `k` by `matlisDual_finiteDimensional`, hence finite over
`R3 k`; the level hypothesis only enters through `hA.finiteDimensional`. -/
lemma matlisDual_module_finite
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    Module.Finite (R3 k) (MatlisDual I) := by
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  exact Module.Finite.of_restrictScalars_finite k (R3 k) (MatlisDual I)

/-- The Matlis dual of a proper ideal is nonzero: a nonzero class in `R/I`
is separated by some `k`-functional. -/
lemma matlisDual_nontrivial
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    Nontrivial (MatlisDual I) := by
  have hmk : (Ideal.Quotient.mk I 1 : R3 k ⧸ I) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.eq_top_iff_one]
    exact hA.proper
  letI : Module.Free k (R3 k ⧸ I) := Module.Free.of_divisionRing k _
  letI : Module.Projective k (R3 k ⧸ I) := Module.Projective.of_free
  obtain ⟨psi, hpsi⟩ := Projective.exists_dual_ne_zero k hmk
  refine ⟨⟨psi⟩, 0, ?_⟩
  intro h
  exact hpsi (congrArg (fun φ : MatlisDual I =>
    φ (Ideal.Quotient.mk I 1)) h)

lemma homogeneous_mem_ideal_of_vanish_above
    {I : Ideal (R3 k)} {e n : ℕ} (hA : IsTypeTwoLevel I e)
    (hne : e < n) {f : R3 k} (hf : MvPolynomial.IsHomogeneous f n) :
    f ∈ I := by
  have hpiece : Ideal.Quotient.mk I f ∈ quotPiece I n := by
    apply Submodule.mem_map.mpr
    refine ⟨(⟨f, hf⟩ : homogeneousSubmodule (Fin 3) k n), hf, ?_⟩
    simp [Ideal.Quotient.mkₐ_eq_mk]
  rw [hA.vanish_above n hne] at hpiece
  have hz : Ideal.Quotient.mk I f = 0 := by simpa using hpiece
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

lemma matlisDual_support_subset_irrelevant
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    Module.support (R3 k) (MatlisDual I) ⊆
      PrimeSpectrum.zeroLocus (MvPolynomial.idealOfVars (Fin 3) k) := by
  letI : Module.Finite (R3 k) (MatlisDual I) := matlisDual_module_finite hA
  rw [Module.support_eq_zeroLocus,
    matlisDual_annihilator_eq_original hA]
  intro P hPI
  change MvPolynomial.idealOfVars (Fin 3) k ≤ P.asIdeal
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply P.isPrime.mem_of_pow_mem (e + 1)
  apply hPI
  exact homogeneous_mem_ideal_of_vanish_above hA (by omega)
    (MvPolynomial.isHomogeneous_X_pow j (e + 1))

open CategoryTheory Abelian Limits in
lemma ext_matlisDual_R3_subsingleton_below_three
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    ∀ i < 3, Subsingleton
      (Ext (ModuleCat.of (R3 k) (MatlisDual I))
        (ModuleCat.of (R3 k) (R3 k)) i) := by
  let m := MvPolynomial.idealOfVars (Fin 3) k
  let xs : List (R3 k) :=
    [MvPolynomial.X (R := k) (0 : Fin 3), MvPolynomial.X (R := k) (1 : Fin 3),
      MvPolynomial.X (R := k) (2 : Fin 3)]
  have hlen : xs.length = 3 := by simp [xs]
  have hmem : ∀ r ∈ xs, r ∈ m := by
    intro r hr
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact Ideal.subset_span (Set.mem_range_self _)
  have hreg : RingTheory.Sequence.IsRegular (R3 k) xs := by
    simpa [xs] using variables_isRegular (k := k)
  have hsmul : m • (⊤ : Submodule (R3 k) (R3 k)) < ⊤ := by
    rw [smul_eq_mul, Ideal.mul_top]
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hone : (1 : R3 k) ∈ m := by rw [htop]; trivial
    have hc : MvPolynomial.C (1 : k) ∈ m ^ 1 := by simpa [m] using hone
    have h := (MvPolynomial.C_mem_pow_idealOfVars_iff
      (σ := Fin 3) (R := k) 1 1).mp hc
    simp at h
  have htfae := exist_isRegular_tfae m 3
    (ModuleCat.of (R3 k) (R3 k)) (by infer_instance) (by infer_instance) hsmul
  have hex : ∃ rs : List (R3 k), rs.length = 3 ∧ (∀ r ∈ rs, r ∈ m) ∧
      RingTheory.Sequence.IsRegular (R3 k) rs := ⟨xs, hlen, hmem, hreg⟩
  have hrees : ∀ N : ModuleCat.{u} (R3 k),
      (Nontrivial N ∧ Module.Finite (R3 k) N ∧
        Module.support (R3 k) N ⊆ PrimeSpectrum.zeroLocus m) →
      ∀ i < 3, Subsingleton
        (Ext N (ModuleCat.of (R3 k) (R3 k)) i) :=
    (htfae.out 3 0).mp hex
  letI : Nontrivial (MatlisDual I) := matlisDual_nontrivial hA
  letI : Module.Finite (R3 k) (MatlisDual I) := matlisDual_module_finite hA
  exact hrees (ModuleCat.of (R3 k) (MatlisDual I))
    ⟨by infer_instance, by infer_instance,
      matlisDual_support_subset_irrelevant hA⟩

open CategoryTheory Abelian Limits in
lemma dualMap_surjective_of_ext_one_subsingleton
    {R K F M : Type u} [CommRing R] [Small.{u} R]
    [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] F) (p : F →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    (hExt : Subsingleton
      (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1)) :
    Function.Surjective i.dualMap := by
  let S : ShortComplex (ModuleCat R) :=
    { X₁ := ModuleCat.of R K
      X₂ := ModuleCat.of R F
      X₃ := ModuleCat.of R M
      f := ModuleCat.ofHom i
      g := ModuleCat.ofHom p
      zero := by ext x; simpa using hex.apply_apply_eq_zero x }
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr hex
      mono_f := (ModuleCat.mono_iff_injective S.f).mpr hi
      epi_g := (ModuleCat.epi_iff_surjective S.g).mpr hp }
  have hz : IsZero (AddCommGrpCat.of
      (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1)) :=
    @AddCommGrpCat.isZero_of_subsingleton _ hExt
  have hepi : Epi (AddCommGrpCat.ofHom
      ((Ext.mk₀ S.f).precomp (ModuleCat.of R R) (zero_add 0))) :=
    ShortComplex.Exact.epi_f
      (Ext.contravariant_sequence_exact₁' hS (ModuleCat.of R R) 0 1 rfl)
      (hz.eq_zero_of_tgt _)
  have hsurj := (AddCommGrpCat.epi_iff_surjective _).mp hepi
  intro phi
  obtain ⟨x, hx⟩ := hsurj (Ext.mk₀ (ModuleCat.ofHom phi))
  let psi : Module.Dual R F := (Ext.addEquiv₀ x).hom
  refine ⟨psi, ?_⟩
  have hxm : x = Ext.mk₀ (ModuleCat.ofHom psi) := by
    simp [psi]
  rw [hxm] at hx
  have hmk : Ext.mk₀ (S.f ≫ ModuleCat.ofHom psi) =
      Ext.mk₀ (ModuleCat.ofHom phi) := by
    simpa [Ext.mk₀_comp_mk₀] using hx
  have hx' := congrArg ModuleCat.Hom.hom
    ((Ext.mk₀_bijective _ _).injective hmk)
  apply LinearMap.ext
  intro y
  simpa [psi, S] using DFunLike.congr_fun hx' y

open CategoryTheory Abelian Limits in
lemma ext_one_kernel_subsingleton_of_ext_two_cokernel
    {R K F M : Type u} [CommRing R] [Small.{u} R]
    [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M]
    [CategoryTheory.Projective (ModuleCat.of R F)]
    (i : K →ₗ[R] F) (p : F →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    (hExt₂ : Subsingleton
      (Ext (ModuleCat.of R M) (ModuleCat.of R R) 2)) :
    Subsingleton (Ext (ModuleCat.of R K) (ModuleCat.of R R) 1) := by
  let S : ShortComplex (ModuleCat R) :=
    { X₁ := ModuleCat.of R K
      X₂ := ModuleCat.of R F
      X₃ := ModuleCat.of R M
      f := ModuleCat.ofHom i
      g := ModuleCat.ofHom p
      zero := by ext x; simpa using hex.apply_apply_eq_zero x }
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr hex
      mono_f := (ModuleCat.mono_iff_injective S.f).mpr hi
      epi_g := (ModuleCat.epi_iff_surjective S.g).mpr hp }
  have hzero (x : Ext (ModuleCat.of R K) (ModuleCat.of R R) 1) : x = 0 := by
    have hconn : hS.extClass.comp x (show 1 + 1 = 2 by omega) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS
      (ModuleCat.of R R) x (show 1 + 1 = 2 by omega) hconn
    have hyzero : y = 0 := Ext.eq_zero_of_projective y
    rw [hyzero, Ext.comp_zero] at hy
    exact hy.symm
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

lemma dual_d₁_range_eq_kernel_d₂
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    LinearMap.range C.d₁.dualMap = LinearMap.ker C.d₂.dualMap := by
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, C.d₂_range]
  apply LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective
  apply dualMap_surjective_of_ext_one_subsingleton
    (i := (LinearMap.range C.d₁).subtype)
    (p := inverseSystemMap hA)
  · exact (LinearMap.range C.d₁).injective_subtype
  · exact inverseSystemMap_surjective hA
  · rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact C.d₁_range.symm
  · exact ext_matlisDual_R3_subsingleton_below_three hA 1 (by omega)

open CategoryTheory Abelian Limits in
lemma dual_d₂_range_eq_kernel_d₃
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex.{u, 0, 0, 0} I e hA) :
    LinearMap.range C.d₂.dualMap = LinearMap.ker C.d₃.dualMap := by
  let R := R3 k
  letI : Fintype C.β₁ := C.fintype₁
  letI : Module.Free R (Fin 2 → R) := by infer_instance
  letI : Module.Projective R (Fin 2 → R) := Module.Projective.of_free
  have hExtRange : Subsingleton
      (Ext (ModuleCat.of R (LinearMap.range C.d₁))
        (ModuleCat.of R R) 1) := by
    apply ext_one_kernel_subsingleton_of_ext_two_cokernel
      (i := (LinearMap.range C.d₁).subtype)
      (p := inverseSystemMap hA)
    · exact (LinearMap.range C.d₁).injective_subtype
    · exact inverseSystemMap_surjective hA
    · rw [LinearMap.exact_iff, Submodule.range_subtype]
      exact C.d₁_range.symm
    · exact ext_matlisDual_R3_subsingleton_below_three hA 2 (by omega)
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, C.d₃_range]
  apply LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective
  apply dualMap_surjective_of_ext_one_subsingleton
    (i := (LinearMap.range C.d₂).subtype)
    (p := C.d₁.rangeRestrict)
  · exact (LinearMap.range C.d₂).injective_subtype
  · exact LinearMap.surjective_rangeRestrict C.d₁
  · rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
      Submodule.range_subtype]
    exact C.d₂_range.symm
  · exact hExtRange

/-! The full Matlis dual is torsion, with an explicit common annihilator.  This
is the localization input for the first differential: after inverting the
polynomial ring, the inverse-system presentation becomes a surjection onto
the two-dimensional free target. -/

lemma matlisDual_X_pow_smul_zero
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
  (φ : MatlisDual I) :
    (MvPolynomial.X (0 : Fin 3) ^ (e + 1) : R3 k) • φ = 0 := by
  rw [← sum_matlisComponent hA φ, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro n hn
  have hn' : n < e + 1 := Finset.mem_range.mp hn
  have hpiece : matlisComponent I hA.homogeneous n φ ∈
      matlisPiece I hA.homogeneous n :=
    LinearMap.mem_range_self (matlisComponent I hA.homogeneous n) φ
  exact matlisPiece_smul_eq_zero_of_lt hA.homogeneous
    (MvPolynomial.isHomogeneous_X_pow (0 : Fin 3) (e + 1))
    hn' hpiece

noncomputable def localizedFirstMap
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    (C.β₁ → FractionRing (R3 k)) →ₗ[FractionRing (R3 k)]
      (Fin 2 → FractionRing (R3 k)) := by
  letI := C.fintype₁
  exact Fintype.linearCombination (FractionRing (R3 k))
    (fun i z => algebraMap (R3 k) (FractionRing (R3 k))
      (C.d₁ (Pi.single i 1) z))

@[simp] lemma localizedFirstMap_apply
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    (c : C.β₁ → FractionRing (R3 k)) :
    localizedFirstMap hA C c = ∑ i, c i •
      (fun z => algebraMap (R3 k) (FractionRing (R3 k))
        (C.d₁ (Pi.single i 1) z)) := rfl

lemma localizedFirstMap_surjective
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    Function.Surjective (localizedFirstMap hA C) := by
  classical
  letI := C.fintype₁
  let R := R3 k
  let K := FractionRing R
  let s : R := MvPolynomial.X (0 : Fin 3) ^ (e + 1)
  have hs : s ≠ 0 := by
    dsimp [s]
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := k) (0 : Fin 3))
  have hbasis : ∀ z : Fin 2, ∃ c : C.β₁ → K,
      localizedFirstMap hA C c = Pi.single z 1 := by
    intro z
    let u : Fin 2 → R := Pi.single z s
    have hu : u ∈ inverseSystemKernel hA := by
      rw [LinearMap.mem_ker]
      rw [inverseSystemMap_apply]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hiz : i = z
      · subst i
        simpa [u] using matlisDual_X_pow_smul_zero hA (matlisGenerator hA z)
      · simp [u, Pi.single, hiz]
    obtain ⟨x, hx⟩ := (show u ∈ LinearMap.range C.d₁ by
      rw [C.d₁_range]
      exact hu)
    let xK : C.β₁ → K := fun b =>
      (algebraMap R K s)⁻¹ * algebraMap R K (x b)
    have hdx : C.d₁ x = u := hx
    have hloc : localizedFirstMap hA C
        (fun b => algebraMap R K (x b)) =
        (fun i => algebraMap R K (C.d₁ x i)) := by
      funext i
      simp only [localizedFirstMap, Fintype.linearCombination_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hsum : (∑ b, x b • Pi.single b (1 : R)) = x := by
        funext b
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Fintype.sum_eq_single b]
        · simp
        · intro c hcb
          have hbc : b ≠ c := Ne.symm hcb
          simp [Pi.single, hbc]
      have hdx' : C.d₁ x = ∑ b, x b • C.d₁ (Pi.single b 1) := by
        calc
          C.d₁ x = C.d₁ (∑ b, x b • Pi.single b 1) := by rw [hsum]
          _ = ∑ b, x b • C.d₁ (Pi.single b 1) := by
            rw [map_sum]
            simp only [map_smul]
      have hi := congrFun hdx' i
      calc
        (∑ b, (algebraMap R K) (x b) *
            (algebraMap R K) (C.d₁ (Pi.single b 1) i)) =
            ∑ b, (algebraMap R K)
              (x b • C.d₁ (Pi.single b 1) i) := by
          apply Finset.sum_congr rfl
          intro b hb
          simp [map_smul, smul_eq_mul]
        _ = (algebraMap R K)
              ((∑ b, x b • C.d₁ (Pi.single b 1)) i) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [map_sum]
        _ = (algebraMap R K) (C.d₁ x i) := by rw [hi]
    have hsK : algebraMap R K s ≠ 0 := by
      intro hzero
      apply hs
      apply IsFractionRing.injective R K
      simpa using hzero
    have hlocx : localizedFirstMap hA C xK = Pi.single z 1 := by
      rw [show xK = (algebraMap R K s)⁻¹ •
          (fun b => algebraMap R K (x b)) by
          funext b
          simp [xK, smul_eq_mul]]
      rw [map_smul, hloc]
      funext i
      by_cases hiz : i = z
      · subst i
        have hdxz : C.d₁ x z = s := by
          simpa [u] using congrFun hdx z
        simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
        change (algebraMap R K s)⁻¹ * algebraMap R K (C.d₁ x z) = 1
        rw [hdxz]
        exact inv_mul_cancel₀ hsK
      · have hdxi : C.d₁ x i = 0 := by
          rw [hdx]
          simp [u, Pi.single, hiz]
        simp only [Pi.smul_apply, smul_eq_mul]
        have hzsingle : (Pi.single z (1 : K) : Fin 2 → K) i = 0 :=
          (Pi.single_eq_of_ne' (Ne.symm hiz)) 1
        rw [hdxi, map_zero, mul_zero, hzsingle]
    exact ⟨xK, hlocx⟩
  intro y
  let c : C.β₁ → K := fun b =>
    ∑ z : Fin 2, y z • Classical.choose (hbasis z) b
  refine ⟨c, ?_⟩
  have hc : c = ∑ z : Fin 2, y z • Classical.choose (hbasis z) := by
    funext b
    rfl
  rw [hc, map_sum]
  simp_rw [map_smul, Classical.choose_spec (hbasis _)]
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_smul,
    one_smul, zero_smul]
  rw [Fintype.sum_eq_single z]
  · simp
  · intro w hw
    have hzw : z ≠ w := fun h => hw h.symm
    simp [Pi.single, hzw]

/-! The remaining two differentials are localized by the same finite-basis
construction.  The three compatibility lemmas below are deliberately stated
over algebra-mapped vectors; they are the only calculation needed when a
denominator is cleared in the exactness proof. -/

noncomputable def localizedSecondMap
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    (C.β₂ → FractionRing (R3 k)) →ₗ[FractionRing (R3 k)]
      (C.β₁ → FractionRing (R3 k)) := by
  letI := C.fintype₂
  exact Fintype.linearCombination (FractionRing (R3 k))
    (fun j i => algebraMap (R3 k) (FractionRing (R3 k))
      (C.d₂ (Pi.single j 1) i))

noncomputable def localizedThirdMap
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    (C.β₃ → FractionRing (R3 k)) →ₗ[FractionRing (R3 k)]
      (C.β₂ → FractionRing (R3 k)) := by
  letI := C.fintype₃
  exact Fintype.linearCombination (FractionRing (R3 k))
    (fun a g => algebraMap (R3 k) (FractionRing (R3 k))
      (C.d₃ (Pi.single a 1) g))

@[simp] lemma localizedSecondMap_apply
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA)
    (c : C.β₂ → FractionRing (R3 k)) :
    localizedSecondMap C c = ∑ j, c j •
      (fun i => algebraMap (R3 k) (FractionRing (R3 k))
        (C.d₂ (Pi.single j 1) i)) := rfl

@[simp] lemma localizedThirdMap_apply
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA)
    (c : C.β₃ → FractionRing (R3 k)) :
    localizedThirdMap C c = ∑ a, c a •
      (fun g => algebraMap (R3 k) (FractionRing (R3 k))
        (C.d₃ (Pi.single a 1) g)) := rfl

lemma localizedFirstMap_algebraMap
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA)
    (x : C.β₁ → R3 k) :
    localizedFirstMap hA C (fun b => algebraMap (R3 k)
        (FractionRing (R3 k)) (x b)) =
      (fun z => algebraMap (R3 k) (FractionRing (R3 k)) (C.d₁ x z)) := by
  classical
  letI := C.fintype₁
  funext z
  simp only [localizedFirstMap, Fintype.linearCombination_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ b, x b • Pi.single b (1 : R3 k)) = x := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single b]
    · simp
    · intro c hcb
      have hbc : b ≠ c := Ne.symm hcb
      simp [Pi.single, hbc]
  have hdx : C.d₁ x = ∑ b, x b • C.d₁ (Pi.single b 1) := by
    calc
      C.d₁ x = C.d₁ (∑ b, x b • Pi.single b 1) := by rw [hsum]
      _ = ∑ b, x b • C.d₁ (Pi.single b 1) := by
        rw [map_sum]
        simp only [map_smul]
  have hz := congrFun hdx z
  calc
    (∑ b, algebraMap (R3 k) (FractionRing (R3 k)) (x b) *
        algebraMap (R3 k) (FractionRing (R3 k))
          (C.d₁ (Pi.single b 1) z)) =
        ∑ b, algebraMap (R3 k) (FractionRing (R3 k))
          (x b • C.d₁ (Pi.single b 1) z) := by
      apply Finset.sum_congr rfl
      intro b hb
      simp [map_smul, smul_eq_mul]
    _ = algebraMap (R3 k) (FractionRing (R3 k))
          ((∑ b, x b • C.d₁ (Pi.single b 1)) z) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [map_sum]
    _ = algebraMap (R3 k) (FractionRing (R3 k)) (C.d₁ x z) := by rw [hz]

lemma localizedSecondMap_algebraMap
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA)
    (x : C.β₂ → R3 k) :
    localizedSecondMap C (fun j => algebraMap (R3 k)
        (FractionRing (R3 k)) (x j)) =
      (fun i => algebraMap (R3 k) (FractionRing (R3 k)) (C.d₂ x i)) := by
  classical
  letI := C.fintype₂
  funext i
  simp only [localizedSecondMap, Fintype.linearCombination_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ j, x j • Pi.single j (1 : R3 k)) = x := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro l hlj
      have hz : ((Pi.single l (1 : R3 k) : C.β₂ → R3 k) j) = 0 :=
        (Pi.single_eq_of_ne' hlj) 1
      rw [hz, mul_zero]
  have hdx : C.d₂ x = ∑ j, x j • C.d₂ (Pi.single j 1) := by
    calc
      C.d₂ x = C.d₂ (∑ j, x j • Pi.single j 1) := by rw [hsum]
      _ = ∑ j, x j • C.d₂ (Pi.single j 1) := by
        rw [map_sum]
        simp only [map_smul]
  have hi := congrFun hdx i
  calc
    (∑ j, algebraMap (R3 k) (FractionRing (R3 k)) (x j) *
        algebraMap (R3 k) (FractionRing (R3 k))
          (C.d₂ (Pi.single j 1) i)) =
        ∑ j, algebraMap (R3 k) (FractionRing (R3 k))
          (x j • C.d₂ (Pi.single j 1) i) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [map_smul, smul_eq_mul]
    _ = algebraMap (R3 k) (FractionRing (R3 k))
          ((∑ j, x j • C.d₂ (Pi.single j 1)) i) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [map_sum]
    _ = algebraMap (R3 k) (FractionRing (R3 k)) (C.d₂ x i) := by rw [hi]

lemma localizedThirdMap_algebraMap
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA)
    (x : C.β₃ → R3 k) :
    localizedThirdMap C (fun a => algebraMap (R3 k)
        (FractionRing (R3 k)) (x a)) =
      (fun g => algebraMap (R3 k) (FractionRing (R3 k)) (C.d₃ x g)) := by
  classical
  letI := C.fintype₃
  funext g
  simp only [localizedThirdMap, Fintype.linearCombination_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ a, x a • Pi.single a (1 : R3 k)) = x := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single a]
    · simp
    · intro l hla
      have hz : ((Pi.single l (1 : R3 k) : C.β₃ → R3 k) a) = 0 :=
        (Pi.single_eq_of_ne' hla) 1
      rw [hz, mul_zero]
  have hdx : C.d₃ x = ∑ a, x a • C.d₃ (Pi.single a 1) := by
    calc
      C.d₃ x = C.d₃ (∑ a, x a • Pi.single a 1) := by rw [hsum]
      _ = ∑ a, x a • C.d₃ (Pi.single a 1) := by
        rw [map_sum]
        simp only [map_smul]
  have hg := congrFun hdx g
  calc
    (∑ a, algebraMap (R3 k) (FractionRing (R3 k)) (x a) *
        algebraMap (R3 k) (FractionRing (R3 k))
          (C.d₃ (Pi.single a 1) g)) =
        ∑ a, algebraMap (R3 k) (FractionRing (R3 k))
          (x a • C.d₃ (Pi.single a 1) g) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [map_smul, smul_eq_mul]
    _ = algebraMap (R3 k) (FractionRing (R3 k))
          ((∑ a, x a • C.d₃ (Pi.single a 1)) g) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [map_sum]
    _ = algebraMap (R3 k) (FractionRing (R3 k)) (C.d₃ x g) := by rw [hg]

lemma fraction_common_denominator
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ι : Type*} [Fintype ι] (x : ι → K) :
    ∃ b : R, b ≠ 0 ∧ ∃ y : ι → R, ∀ i,
      algebraMap R K (y i) = algebraMap R K b * x i := by
  classical
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) x
  have hex (i : ι) : ∃ y : R,
      algebraMap R K y = (b : R) • x i := by
    exact RingHom.mem_rangeS.mp (hb i)
  let y : ι → R := fun i => Classical.choose (hex i)
  have hy (i : ι) : algebraMap R K (y i) =
      (b : R) • x i := Classical.choose_spec (hex i)
  refine ⟨b, mem_nonZeroDivisors_iff_ne_zero.mp b.property, y, ?_⟩
  intro i
  simpa [y, Algebra.smul_def] using hy i

lemma localizedSecondMap_range_eq_kernel
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    LinearMap.range (localizedSecondMap C) =
      LinearMap.ker (localizedFirstMap hA C) := by
  classical
  let R := R3 k
  let K := FractionRing R
  let alg : R →+* K := algebraMap R K
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hcol : ∀ j : C.β₂,
        localizedFirstMap hA C
            (fun i => alg (C.d₂ (Pi.single j 1) i)) = 0 := by
      intro j
      apply _root_.funext
      intro z
      have hcomp := congrArg (fun f => f (Pi.single j 1)) C.d₁_d₂
      have hsum : (∑ i, C.d₂ (Pi.single j 1) i •
          Pi.single i (1 : R)) = C.d₂ (Pi.single j 1) := by
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Fintype.sum_eq_single i]
        · simp
        · intro l hli
          have hz : ((Pi.single l (1 : R) : C.β₁ → R) i) = 0 :=
            (Pi.single_eq_of_ne' hli) 1
          rw [hz, mul_zero]
      simp only [LinearMap.comp_apply] at hcomp
      rw [← hsum, map_sum] at hcomp
      simp only [map_smul] at hcomp
      have hzR := congrFun hcomp z
      have hzR' : (∑ x, C.d₂ (Pi.single j 1) x *
          C.d₁ (Pi.single x 1) z) = 0 := by
        simpa [smul_eq_mul] using hzR
      have hzK : (∑ x, alg (C.d₂ (Pi.single j 1) x) *
          alg (C.d₁ (Pi.single x 1) z)) = 0 := by
        have hzK0 := congrArg alg hzR'
        simpa only [map_zero, map_sum, map_mul] using hzK0
      simpa [localizedFirstMap_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] using hzK
    rw [localizedSecondMap_apply, map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_smul, hcol, smul_zero]
  · intro hy
    obtain ⟨b, hb0, yR, hyR⟩ :=
      fraction_common_denominator (R := R) (K := K) y
    have hden : (fun i => alg (yR i)) = (alg b) • y := by
      funext i
      change alg (yR i) = alg b * y i
      exact hyR i
    have hzeroK : localizedFirstMap hA C
        (fun i => alg (yR i)) = 0 := by
      rw [hden, map_smul, hy, smul_zero]
    have hzeroR : C.d₁ yR = 0 := by
      have hmap := localizedFirstMap_algebraMap C yR
      have hzeroK' : (fun z => alg (C.d₁ yR z)) = 0 := by
        rw [← hmap]
        exact hzeroK
      funext z
      exact IsFractionRing.injective R K (by
        change alg (C.d₁ yR z) = alg 0
        simpa using congrFun hzeroK' z)
    have hyker : yR ∈ LinearMap.ker C.d₁ :=
      LinearMap.mem_ker.mpr hzeroR
    rw [← C.d₂_range] at hyker
    obtain ⟨x, hx⟩ := hyker
    refine ⟨(alg b)⁻¹ • (fun i => alg (x i)), ?_⟩
    rw [map_smul, localizedSecondMap_algebraMap, hx]
    funext i
    change (alg b)⁻¹ * alg (yR i) = y i
    rw [hyR i]
    have hbK : alg b ≠ 0 := by
      intro hzero
      exact hb0 (IsFractionRing.injective R K (by
        change alg b = alg 0
        simpa using hzero))
    rw [← mul_assoc, inv_mul_cancel₀ hbK, one_mul]

lemma localizedThirdMap_range_eq_kernel
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    LinearMap.range (localizedThirdMap C) =
      LinearMap.ker (localizedSecondMap C) := by
  classical
  let R := R3 k
  let K := FractionRing R
  let alg : R →+* K := algebraMap R K
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hcol : ∀ a : C.β₃,
        localizedSecondMap C
            (fun j => alg (C.d₃ (Pi.single a 1) j)) = 0 := by
      intro a
      apply _root_.funext
      intro i
      have hcomp := congrArg (fun f => f (Pi.single a 1)) C.d₂_d₃
      have hsum : (∑ j, C.d₃ (Pi.single a 1) j •
          Pi.single j (1 : R)) = C.d₃ (Pi.single a 1) := by
        funext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Fintype.sum_eq_single j]
        · simp
        · intro l hlj
          have hz : ((Pi.single l (1 : R) : C.β₂ → R) j) = 0 :=
            (Pi.single_eq_of_ne' hlj) 1
          rw [hz, mul_zero]
      simp only [LinearMap.comp_apply] at hcomp
      rw [← hsum, map_sum] at hcomp
      simp only [map_smul] at hcomp
      have hiR := congrFun hcomp i
      have hiR' : (∑ x, C.d₃ (Pi.single a 1) x *
          C.d₂ (Pi.single x 1) i) = 0 := by
        simpa [smul_eq_mul] using hiR
      have hiK : (∑ x, alg (C.d₃ (Pi.single a 1) x) *
          alg (C.d₂ (Pi.single x 1) i)) = 0 := by
        have hiK0 := congrArg alg hiR'
        simpa only [map_zero, map_sum, map_mul] using hiK0
      simpa [localizedSecondMap_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] using hiK
    rw [localizedThirdMap_apply, map_sum]
    apply Finset.sum_eq_zero
    intro a ha
    rw [map_smul, hcol, smul_zero]
  · intro hy
    obtain ⟨b, hb0, yR, hyR⟩ :=
      fraction_common_denominator (R := R) (K := K) y
    have hden : (fun j => alg (yR j)) = (alg b) • y := by
      funext j
      change alg (yR j) = alg b * y j
      exact hyR j
    have hzeroK : localizedSecondMap C
        (fun j => alg (yR j)) = 0 := by
      rw [hden, map_smul, hy, smul_zero]
    have hzeroR : C.d₂ yR = 0 := by
      have hmap := localizedSecondMap_algebraMap C yR
      have hzeroK' : (fun i => alg (C.d₂ yR i)) = 0 := by
        rw [← hmap]
        exact hzeroK
      funext i
      exact IsFractionRing.injective R K (by
        change alg (C.d₂ yR i) = alg 0
        simpa using congrFun hzeroK' i)
    have hyker : yR ∈ LinearMap.ker C.d₂ :=
      LinearMap.mem_ker.mpr hzeroR
    rw [← C.d₃_range] at hyker
    obtain ⟨x, hx⟩ := hyker
    refine ⟨(alg b)⁻¹ • (fun j => alg (x j)), ?_⟩
    rw [map_smul, localizedThirdMap_algebraMap, hx]
    funext j
    change (alg b)⁻¹ * alg (yR j) = y j
    rw [hyR j]
    have hbK : alg b ≠ 0 := by
      intro hzero
      exact hb0 (IsFractionRing.injective R K (by
        change alg b = alg 0
        simpa using hzero))
    rw [← mul_assoc, inv_mul_cancel₀ hbK, one_mul]

lemma homogeneous_column_mem_irrelevant_smul_range
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) (i : Fin 2)
    {d : ℕ} {f : R3 k}
    (hf : MvPolynomial.IsHomogeneous f d) (hde : e + 1 < d) :
    f • (Pi.single i 1) ∈
      irrelevantIdeal k • (LinearMap.range C.d₁) := by
  have hmul : f ∈
      (MvPolynomial.homogeneousSubmodule (Fin 3) k 1) *
        (MvPolynomial.homogeneousSubmodule (Fin 3) k (d - 1)) := by
    have hd : d = (d - 1) + 1 := by omega
    rw [hd] at hf
    exact homogeneous_mem_irrelevant_mul_homogeneous hf
  refine Submodule.mul_induction_on'
    (C := fun z _ => z • (Pi.single i 1) ∈
      irrelevantIdeal k • (LinearMap.range C.d₁)) ?_ ?_ hmul
  · intro a ha b hb
    have haHom : MvPolynomial.IsHomogeneous a 1 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp ha
    have hbHom : MvPolynomial.IsHomogeneous b (d - 1) :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp hb
    have haI : a ∈ irrelevantIdeal k := by
      simpa [irrelevantIdeal] using
        (isHomogeneous_mem_pow_idealOfVars haHom (by norm_num : 1 ≤ 1))
    have hvec : inverseSystemMap hA (Pi.single i b) = 0 := by
      rw [inverseSystemMap_apply]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa using matlisPiece_smul_eq_zero_of_lt hA.homogeneous hbHom
          (by omega) (matlisGenerator_mem_top hA i)
      · simp [Pi.single, hji]
    have hvecK : Pi.single i b ∈ inverseSystemKernel hA := by
      rw [LinearMap.mem_ker]
      exact hvec
    have hvecR : Pi.single i b ∈ LinearMap.range C.d₁ := by
      rw [C.d₁_range]
      exact hvecK
    have hterm : (a * b) • (Pi.single i 1) = a • (Pi.single i b) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [smul_eq_mul, mul_assoc]
      · simp [Pi.single, hji]
    rw [hterm]
    exact Submodule.smul_mem_smul haI hvecR
  · intro x hx y hy hpx hpy
    simpa [add_smul] using add_mem hpx hpy

lemma first_shift_le
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    ∀ b, (C.pShift b : ℤ) ≤ (e : ℤ) + 1 := by
  classical
  letI : Fintype C.β₁ := C.fintype₁
  let N := C.firstNakayamaCertificate
  intro b
  by_contra hbad
  have hde : e + 1 < C.pShift b := by omega
  have hcol : ∀ i, C.d₁ (Pi.single b 1) i • Pi.single i 1 ∈
      irrelevantIdeal k • (LinearMap.range C.d₁) := by
    intro i
    apply homogeneous_column_mem_irrelevant_smul_range hA C i
    · exact C.d₁_homogeneous b i
    · exact hde
  have hcolvec : C.d₁ (Pi.single b 1) ∈
      irrelevantIdeal k • (LinearMap.range C.d₁) := by
    have hdecomp : C.d₁ (Pi.single b 1) =
        ∑ i : Fin 2, C.d₁ (Pi.single b 1) i • Pi.single i 1 := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fintype.sum_eq_single i]
      · simp
      · intro j hji
        have hz : ((Pi.single j (1 : R3 k) : Fin 2 → R3 k) i) = 0 :=
          (Pi.single_eq_of_ne' hji) 1
        rw [hz, mul_zero]
    rw [hdecomp]
    apply Submodule.sum_mem
    intro i hi
    exact hcol i
  have hN : N.generatorMap (Pi.single b 1) ∈
      irrelevantIdeal k • (⊤ : Submodule (R3 k)
        (LinearMap.range C.d₁)) := by
    have hsub : ∀ (x : Fin 2 → R3 k), x ∈
        irrelevantIdeal k • (LinearMap.range C.d₁) →
        ∀ hx : x ∈ LinearMap.range C.d₁,
          (⟨x, hx⟩ : LinearMap.range C.d₁) ∈
              irrelevantIdeal k • (⊤ : Submodule (R3 k)
              (LinearMap.range C.d₁)) := by
      have hJrange_le : irrelevantIdeal k • (LinearMap.range C.d₁) ≤
          LinearMap.range C.d₁ := by
        refine Submodule.smul_le.mpr ?_
        intro a ha m hm
        exact (LinearMap.range C.d₁).smul_mem a hm
      intro x hx
      refine Submodule.smul_induction_on' hx (p := fun x _ => ∀ hx :
          x ∈ LinearMap.range C.d₁,
          (⟨x, hx⟩ : LinearMap.range C.d₁) ∈
            irrelevantIdeal k • (⊤ : Submodule (R3 k)
              (LinearMap.range C.d₁)) ) ?_ ?_
      · intro a ha m hm hxrange
        have hm' : (⟨m, hm⟩ : LinearMap.range C.d₁) ∈
            (⊤ : Submodule (R3 k) (LinearMap.range C.d₁)) :=
          Submodule.mem_top
        have hmem := Submodule.smul_mem_smul ha hm'
        simpa using hmem
      · intro x hx y hy hpx hpy hxrange
        have hxr : x ∈ LinearMap.range C.d₁ := hJrange_le hx
        have hyr : y ∈ LinearMap.range C.d₁ := hJrange_le hy
        have hmem : (⟨x + y, hxrange⟩ : LinearMap.range C.d₁) ∈
            irrelevantIdeal k • (⊤ : Submodule (R3 k)
              (LinearMap.range C.d₁)) := by
          have hx' := hpx hxr
          have hy' := hpy hyr
          have hsum : (⟨x, hxr⟩ : LinearMap.range C.d₁) +
              ⟨y, hyr⟩ ∈ irrelevantIdeal k •
                (⊤ : Submodule (R3 k) (LinearMap.range C.d₁)) :=
            add_mem hx' hy'
          simpa using hsum
        simpa using hmem
    have hgen_eq : N.generatorMap (Pi.single b 1) =
        (⟨C.d₁ (Pi.single b 1),
          ⟨Pi.single b 1, rfl⟩⟩ : LinearMap.range C.d₁) := by
      apply Subtype.ext
      rw [GradedNakayamaCertificate.generatorMap_apply]
      have hgen_col : ∀ j, N.generator j =
          (⟨C.d₁ (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩ :
            LinearMap.range C.d₁) := by
        intro j
        rfl
      simp_rw [hgen_col]
      rw [Fintype.sum_eq_single b]
      · simp
      · intro j hji
        simp [Pi.single, hji]
    rw [hgen_eq]
    exact hsub _ hcolvec ⟨Pi.single b 1, rfl⟩
  have hone : (1 : R3 k) ∈ irrelevantIdeal k := by
    have hsum : (∑ j, ((Pi.single b (1 : R3 k) : C.β₁ → R3 k) j) •
        N.generator j) ∈
        N.irrelevant • (⊤ : Submodule (R3 k)
          (LinearMap.range C.d₁)) := by
      change (∑ j, ((Pi.single b (1 : R3 k) : C.β₁ → R3 k) j) •
          N.generator j) ∈
        irrelevantIdeal k • (⊤ : Submodule (R3 k)
          (LinearMap.range C.d₁))
      simpa [GradedNakayamaCertificate.generatorMap] using hN
    have hc := N.residueIndependent (Pi.single b 1) hsum b
    change (1 : R3 k) ∈ N.irrelevant
    simpa using hc
  have hpow : (1 : R3 k) ∈ MvPolynomial.idealOfVars (Fin 3) k ^ 1 := by
    simpa [irrelevantIdeal] using hone
  have hcontra :=
    (MvPolynomial.C_mem_pow_idealOfVars_iff (σ := Fin 3) (R := k) 1 1).mp hpow
  rcases hcontra with hzero | hone
  · exact one_ne_zero hzero
  · exact one_ne_zero hone

/-! ## Homogeneous pieces of the actual first syzygy

The critical branch is a statement about the *homogeneous* kernel of the
inverse-system presentation.  Keeping that kernel as an honest submodule of
the polynomial vector space is useful: it lets the later line-factorization
argument talk to `vJPiece` without passing through a choice of coordinates in
the finite-dimensional degree piece.
-/

noncomputable def inverseSystemKernelPiece
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) (t : ℤ) :
    Submodule k (Fin 2 → R3 k) :=
  if ht : 0 ≤ t then
    LinearMap.range (vectorHomogeneousComponent t.toNat) ⊓
      Submodule.restrictScalars k (inverseSystemKernel hA)
  else ⊥

noncomputable def minimalKernelPiece
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) (t : ℤ) :
    Submodule k (Fin 2 → R3 k) :=
  if ht : 0 ≤ t then
    LinearMap.range (vectorHomogeneousComponent t.toNat) ⊓
      LinearMap.range (C.d₁.restrictScalars k)
  else ⊥

lemma minimalKernelPiece_eq_inverseSystemKernelPiece
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) (t : ℤ) :
    minimalKernelPiece hA C t = inverseSystemKernelPiece hA t := by
  classical
  by_cases ht : 0 ≤ t
  · rw [minimalKernelPiece, dif_pos ht, inverseSystemKernelPiece, dif_pos ht]
    change LinearMap.range (vectorHomogeneousComponent t.toNat) ⊓
      LinearMap.range (C.d₁.restrictScalars k) =
      LinearMap.range (vectorHomogeneousComponent t.toNat) ⊓
        Submodule.restrictScalars k (inverseSystemKernel hA)
    rw [LinearMap.range_restrictScalars, C.d₁_range]
  · rw [minimalKernelPiece, dif_neg ht, inverseSystemKernelPiece, dif_neg ht]

lemma vectorHomogeneousComponent_mem_range_iff
    {d : ℕ} {u : Fin 2 → R3 k} :
    u ∈ LinearMap.range (vectorHomogeneousComponent d) ↔
      ∀ i, MvPolynomial.IsHomogeneous (u i) d := by
  constructor
  · rintro ⟨c, rfl⟩ i
    exact MvPolynomial.homogeneousComponent_isHomogeneous d (c i)
  · intro hu
    refine ⟨u, ?_⟩
    funext i
    have hi : u i ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k d :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hu i)
    simpa [vectorHomogeneousComponent_apply] using
      (MvPolynomial.homogeneousComponent_of_mem (m := d) (n := d) hi)

lemma inverseSystemKernelPiece_mem_iff
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) {t : ℤ}
    (ht : 0 ≤ t) (u : Fin 2 → R3 k) :
    u ∈ inverseSystemKernelPiece hA t ↔
      (∀ i, MvPolynomial.IsHomogeneous (u i) t.toNat) ∧
        inverseSystemMap hA u = 0 := by
  rw [inverseSystemKernelPiece, dif_pos ht, Submodule.mem_inf]
  constructor
  · rintro ⟨hu, hker⟩
    refine ⟨(vectorHomogeneousComponent_mem_range_iff.mp hu), ?_⟩
    exact LinearMap.mem_ker.mp hker
  · rintro ⟨hhom, hker⟩
    refine ⟨vectorHomogeneousComponent_mem_range_iff.mpr hhom, ?_⟩
    exact LinearMap.mem_ker.mpr hker

lemma minimalKernelPiece_mem_iff
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) {t : ℤ} (ht : 0 ≤ t)
    (u : Fin 2 → R3 k) :
    u ∈ minimalKernelPiece hA C t ↔
      (∀ i, MvPolynomial.IsHomogeneous (u i) t.toNat) ∧
        inverseSystemMap hA u = 0 := by
  rw [minimalKernelPiece, dif_pos ht, Submodule.mem_inf]
  constructor
  · rintro ⟨hu, hker⟩
    refine ⟨vectorHomogeneousComponent_mem_range_iff.mp hu, ?_⟩
    have hker' : u ∈ inverseSystemKernel hA := by
      have hker'' : u ∈ Submodule.restrictScalars k (LinearMap.range C.d₁) := by
        simpa only [LinearMap.range_restrictScalars] using hker
      rw [C.d₁_range] at hker''
      exact hker''
    exact LinearMap.mem_ker.mp hker'
  · rintro ⟨hhom, hker⟩
    refine ⟨vectorHomogeneousComponent_mem_range_iff.mpr hhom, ?_⟩
    have hker' : u ∈ Submodule.restrictScalars k (LinearMap.range C.d₁) := by
      rw [C.d₁_range]
      exact LinearMap.mem_ker.mpr hker
    simpa only [LinearMap.range_restrictScalars] using hker'

lemma inverseSystemKernelPiece_zero_of_neg
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) {t : ℤ}
    (ht : t < 0) : inverseSystemKernelPiece hA t = ⊥ := by
  rw [inverseSystemKernelPiece, dif_neg (by omega)]

lemma minimalKernelPiece_zero_of_neg
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) {t : ℤ} (ht : t < 0) :
    minimalKernelPiece hA C t = ⊥ := by
  rw [minimalKernelPiece, dif_neg (by omega)]

/-! A coordinate-free way of turning a surjective map on a finite
finite-dimensional source into the `SurjectivePresentation` used by the
critical certificate.  The kernel is allowed to live in a different ambient
space; the supplied linear equivalence is the only bridge needed. -/

noncomputable def surjectivePresentationOfFinrank
    {V M K : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] [AddCommGroup K] [Module k K]
    [FiniteDimensional k V]
    (f : V →ₗ[k] M) (hf : Function.Surjective f)
    (E : LinearMap.ker f ≃ₗ[k] K) :
    Nonempty (SurjectivePresentation k M K (finrank k V)) := by
  classical
  let b : Basis (Fin (finrank k V)) k V := Module.finBasis k V
  let π : (Fin (finrank k V) → k) →ₗ[k] M :=
    f.comp b.equivFun.symm.toLinearMap
  let e : (Fin (finrank k V) → k) ≃ₗ[k] V := b.equivFun.symm
  let forward : LinearMap.ker π →ₗ[k] LinearMap.ker f :=
    { toFun := fun x =>
        ⟨e x.1, by
          apply LinearMap.mem_ker.mpr
          have hx := LinearMap.mem_ker.mp x.2
          change f (e x.1) = 0 at hx
          exact hx⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact e.map_add x.1 y.1
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact e.map_smul c x.1 }
  let backward : LinearMap.ker f →ₗ[k] LinearMap.ker π :=
    { toFun := fun y =>
        ⟨e.symm y.1, by
          apply LinearMap.mem_ker.mpr
          have hy := LinearMap.mem_ker.mp y.2
          change f (e (e.symm y.1)) = 0
          simpa using hy⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact e.symm.map_add x.1 y.1
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact e.symm.map_smul c x.1 }
  have hforward : Function.Bijective forward := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hxy' := congrArg (fun z => z.1) hxy
      exact e.injective hxy'
    · intro y
      refine ⟨backward y, ?_⟩
      apply Subtype.ext
      change e (e.symm y.1) = y.1
      exact e.apply_symm_apply _
  let kerEquiv : LinearMap.ker π ≃ₗ[k] LinearMap.ker f :=
    LinearEquiv.ofBijective forward hforward
  refine ⟨{ π := π, surjective := ?_, kernelEquiv := kerEquiv.trans E }⟩
  intro y
  obtain ⟨x, hx⟩ := hf y
  refine ⟨b.equivFun x, ?_⟩
  simpa [π, LinearMap.comp_apply] using hx

lemma minimalKernelPiece_surjectivePresentation
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    {t : ℤ} (ht0 : 0 ≤ t) (hte : t ≤ (e : ℤ)) :
    Nonempty (SurjectivePresentation k (gradedDualPiece I e t.toNat)
      (minimalKernelPiece hA C t) (2 * Nz t).toNat) := by
  classical
  let n : ℕ := t.toNat
  have htn : (n : ℤ) = t := Int.toNat_of_nonneg ht0
  have hn : n ≤ e := by
    exact_mod_cast (show (n : ℤ) ≤ (e : ℤ) by omega)
  letI : Fintype C.β₁ := C.fintype₁
  letI : Fintype C.β₂ := C.fintype₂
  letI : Fintype C.β₃ := C.fintype₃
  let H := C.firstRelations
  letI : Fintype H.β := H.fintype
  let P₀ : (Fin 2 → R3 k) →ₗ[k] (Fin 2 → R3 k) :=
    shiftedProjection (fun _ : Fin 2 => 0) n
  let P₁ : (H.β → R3 k) →ₗ[k] (H.β → R3 k) :=
    shiftedProjection H.degree n
  let f₀ : (Fin 2 → R3 k) →ₗ[k] MatlisDual I :=
    (inverseSystemMap hA).restrictScalars k
  let f₁ : (H.β → R3 k) →ₗ[k] (Fin 2 → R3 k) :=
    H.d₁.restrictScalars k
  let Q₀ : MatlisDual I →ₗ[k] MatlisDual I :=
    matlisComponent I hA.homogeneous (e - n)
  have hP₀ : P₀.comp P₀ = P₀ := by
    exact shiftedProjection_idem (k := k) (fun _ : Fin 2 => 0) n
  have hP₁ : P₁.comp P₁ = P₁ := by
    exact shiftedProjection_idem (k := k) H.degree n
  have hP₁def : H.shiftedComponent n = P₁ := by
    apply LinearMap.ext
    intro c
    funext b
    rfl
  have hcomm₀ : f₀.comp P₀ = Q₀.comp f₀ := by
    apply LinearMap.ext
    intro u
    simpa [f₀, P₀, Q₀, vectorProjection_eq_shifted (k := k) n] using
      inverseSystemMap_vectorComponent hA hn u
  have hcomm₁ : f₁.comp P₁ = P₀.comp f₁ := by
    apply LinearMap.ext
    intro c
    simpa [f₁, P₀, P₁, shiftedProjection,
      vectorProjection_eq_shifted (k := k) n,
      HomogeneousFirstRelations.shiftedComponent] using
      H.d₁_shiftedComponent n c
  have hrange₁₀ : LinearMap.range f₁ = LinearMap.ker f₀ := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hc := congrArg (fun g => g c) H.inverseSystemMap_comp_d₁
      change inverseSystemMap hA (H.d₁ c) = 0
      simpa [LinearMap.comp_apply] using hc
    · intro hx
      have hxR : x ∈ inverseSystemKernel hA := by
        change inverseSystemMap hA x = 0
        exact LinearMap.mem_ker.mp hx
      rw [← H.range_d₁_eq_kernel] at hxR
      obtain ⟨c, hc⟩ := hxR
      refine ⟨c, ?_⟩
      exact hc
  let g₀ : LinearMap.range P₀ →ₗ[k] LinearMap.range Q₀ :=
    rangeMap f₀ P₀ Q₀ hcomm₀
  let g₁ : LinearMap.range P₁ →ₗ[k] LinearMap.range P₀ :=
    rangeMap f₁ P₁ P₀ hcomm₁
  have hrange₁ : LinearMap.range g₁ = LinearMap.ker g₀ := by
    exact rangeMap_range_eq_ker f₁ f₀ P₁ P₀ Q₀
      hcomm₁ hcomm₀ hP₀ hrange₁₀
  let E : LinearMap.range Q₀ ≃ₗ[k] gradedDualPiece I e n := by
    simpa [Q₀, matlisPiece] using
      (matlisPieceEquiv I hA.homogeneous (e - n))
  let f : LinearMap.range P₀ →ₗ[k] gradedDualPiece I e n :=
    E.toLinearMap.comp g₀
  have hf : Function.Surjective f := by
    intro y
    have hne' : e - n ≤ e := Nat.sub_le _ _
    obtain ⟨u, hu⟩ := inverseSystemPieceMap_surjective hA hne' y
    have huHom : ∀ i, MvPolynomial.IsHomogeneous (u i).1 n := by
      intro i
      have hi := (MvPolynomial.mem_homogeneousSubmodule _ _).mp (u i).2
      simpa [Nat.sub_sub_self hn] using hi
    let c : Fin 2 → R3 k := fun i => (u i).1
    have hcP : P₀ c = c := by
      funext i
      change MvPolynomial.homogeneousComponent n (u i).1 = (u i).1
      have hi : (u i).1 ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k n :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (huHom i)
      simpa using
        (MvPolynomial.homogeneousComponent_of_mem (m := n) (n := n) hi)
    let x : LinearMap.range P₀ := ⟨c, ⟨c, hcP⟩⟩
    refine ⟨x, ?_⟩
    have hleft := matlisPieceRestrict_inverseSystemMap hA hne' u
    have hmemc : inverseSystemMap hA c ∈ LinearMap.range Q₀ := by
      have hcQ : Q₀ (f₀ c) = inverseSystemMap hA c := by
        have hh := congrArg (fun g => g c) hcomm₀
        simpa [LinearMap.comp_apply, hcP, f₀] using hh.symm
      rw [← hcQ]
      exact LinearMap.mem_range_self Q₀ (f₀ c)
    change E (g₀ x) = y
    change matlisPieceRestrict I hA.homogeneous (e - n)
        ⟨inverseSystemMap hA c, hmemc⟩ = y
    calc
      matlisPieceRestrict I hA.homogeneous (e - n)
          ⟨inverseSystemMap hA c, hmemc⟩ =
          inverseSystemPieceMap hA (e - n) u := by simpa [c] using hleft
      _ = y := hu
  let inc : LinearMap.range P₀ →ₗ[k] (Fin 2 → R3 k) :=
    (LinearMap.range P₀).subtype
  let g₁full : LinearMap.range P₁ →ₗ[k] (Fin 2 → R3 k) :=
    inc.comp g₁
  have hminrange : LinearMap.range g₁full = minimalKernelPiece hA C t := by
    apply Submodule.ext
    intro u
    constructor
    · rintro ⟨x, rfl⟩
      have hxP := (g₁ x).property
      have hxK : (g₁ x : Fin 2 → R3 k) ∈
          LinearMap.range (C.d₁.restrictScalars k) := by
        refine ⟨x.1, ?_⟩
        change C.d₁ x.1 = H.d₁ x.1
        rw [GradedMinimalFreeComplex.firstRelations_d₁_eq C]
      have hxhom : (g₁ x : Fin 2 → R3 k) ∈
          LinearMap.range (vectorHomogeneousComponent t.toNat) := by
        simpa [P₀, vectorProjection_eq_shifted (k := k) n] using hxP
      rw [minimalKernelPiece, dif_pos ht0]
      exact ⟨hxhom, hxK⟩
    · intro hu
      rw [minimalKernelPiece, dif_pos ht0] at hu
      obtain ⟨u', hu'⟩ := hu.1
      have huP : P₀ u = u := by
        have hu'P : P₀ u' = u := by
          simpa [P₀, vectorProjection_eq_shifted (k := k) n] using hu'
        calc
          P₀ u = P₀ (P₀ u') := by rw [hu'P]
          _ = P₀ u' := congrArg (fun z => z u') hP₀
          _ = u := hu'P
      obtain ⟨c, hc⟩ := hu.2
      let x : LinearMap.range P₁ := ⟨P₁ c, ⟨c, rfl⟩⟩
      refine ⟨x, ?_⟩
      have hh := congrArg (fun z => z c) hcomm₁
      have hc' : f₁ c = u := by
        change H.d₁ c = u
        rw [GradedMinimalFreeComplex.firstRelations_d₁_eq C]
        exact hc
      change f₁ (P₁ c) = u
      calc
        f₁ (P₁ c) = P₀ (f₁ c) := by
          simpa [LinearMap.comp_apply] using hh
        _ = P₀ u := by rw [hc']
        _ = u := huP
  -- The preceding range map is only used through its range.  The canonical
  -- map from that range to the ambient polynomial vector space is injective;
  -- obtain its equivalence and transport the kernel equality through it.
  let grange : LinearMap.range g₁ →ₗ[k] (Fin 2 → R3 k) :=
    inc.comp (LinearMap.range g₁).subtype
  have hgrange_inj : Function.Injective grange := by
    intro x y hxy
    apply Subtype.ext
    simpa [grange, inc] using hxy
  have hgrange_range : LinearMap.range grange = minimalKernelPiece hA C t := by
    rw [← hminrange]
    apply Submodule.ext
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := x.property
      refine ⟨y, ?_⟩
      simp [grange, g₁full, inc, hy]
    · rintro ⟨y, rfl⟩
      refine ⟨⟨g₁ y, ⟨y, rfl⟩⟩, ?_⟩
      simp [grange, g₁full, inc]
  let Er : LinearMap.range g₁ ≃ₗ[k] minimalKernelPiece hA C t :=
    (LinearEquiv.ofInjective grange hgrange_inj).trans
      (LinearEquiv.ofEq _ _ hgrange_range)
  have hkerf : LinearMap.ker f = LinearMap.ker g₀ := by
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      apply LinearMap.mem_ker.mpr
      have hx' := LinearMap.mem_ker.mp hx
      exact E.injective (by simpa [f, LinearMap.comp_apply] using hx')
    · intro hx
      apply LinearMap.mem_ker.mpr
      simp [f, LinearMap.comp_apply, LinearMap.mem_ker.mp hx]
  let Ek : LinearMap.ker f ≃ₗ[k] minimalKernelPiece hA C t :=
    (LinearEquiv.ofEq _ _ hkerf).trans
      ((LinearEquiv.ofEq _ _ hrange₁.symm).trans Er)
  have hfin : (finrank k (LinearMap.range P₀) : ℤ) = 2 * Nz t := by
    simpa [P₀, Nz_natCast, htn] using
      (show (finrank k (LinearMap.range
          (shiftedProjection (k := k) (fun _ : Fin 2 => 0) n)) : ℤ) =
        2 * Nz (n : ℤ) by
        rw [shiftedRange_finrank]
        simp [Nz_natCast])
  have hfinNat : finrank k (LinearMap.range P₀) = (2 * Nz t).toNat := by
    have hnonneg : 0 ≤ 2 * Nz t := mul_nonneg (by norm_num) (Nz_nonneg _)
    have hz := Int.toNat_of_nonneg hnonneg
    have hfin' : (finrank k (LinearMap.range P₀) : ℤ) =
        ((2 * Nz t).toNat : ℤ) := hfin.trans (by simpa [htn] using hz.symm)
    exact_mod_cast hfin'
  letI : FiniteDimensional k (LinearMap.range P₀) := by
    exact (shiftedRangeEquiv (k := k) (fun _ : Fin 2 => 0) n).symm.finiteDimensional
  have P := surjectivePresentationOfFinrank f hf Ek
  simpa [hfinNat] using P

/-! A finite homogeneous generating family for `I`.

The resolution package only needs a finite list of homogeneous generators of
the ideal.  We build that list directly from the homogeneous pieces.  The
piece in degree `e+1` already contains every monomial of that degree (the
quotient vanishes above `e`), and therefore generates all higher pieces.  This
keeps the later circuit construction independent of a choice of Gröbner basis.
-/

abbrev IdealPieceIndex {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) :=
  Σ n : Fin (e + 2), Fin (finrank k (idealPiece I n))

noncomputable def idealPieceBasis
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) (n : ℕ) :
    Basis (Fin (finrank k (idealPiece I n))) k (idealPiece I n) :=
  Module.finBasis k (idealPiece I n)

noncomputable def idealPieceGenerator
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    IdealPieceIndex hA → R3 k := fun i =>
  ((idealPieceBasis hA i.1.1) i.2 : R3 k)

lemma idealPieceGenerator_homogeneous
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealPieceIndex hA) :
    MvPolynomial.IsHomogeneous (idealPieceGenerator hA i) i.1.1 := by
  exact (idealPieceBasis hA i.1.1 i.2).property.1

lemma idealPieceGenerator_mem
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealPieceIndex hA) : idealPieceGenerator hA i ∈ I := by
  exact (idealPieceBasis hA i.1.1 i.2).property.2

lemma idealPieceGenerator_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealPieceIndex hA) : idealPieceGenerator hA i ≠ 0 := by
  intro hi
  exact (idealPieceBasis hA i.1.1).ne_zero i.2 (Subtype.ext hi)

lemma mem_idealSpan_of_mem_idealPiece
    {I : Ideal (R3 k)} {e n : ℕ} (hA : IsTypeTwoLevel I e)
    (hn : n < e + 2) {f : R3 k} (hf : f ∈ idealPiece I n) :
    f ∈ Ideal.span (Set.range (idealPieceGenerator hA)) := by
  classical
  let b := idealPieceBasis hA n
  let x : idealPiece I n := ⟨f, hf⟩
  have hrepr := b.sum_repr x
  have hrepr' :
      (∑ i, b.repr x i • (b i : R3 k)) = f := by
    calc
      (∑ i, b.repr x i • (b i : R3 k)) =
          (↑(∑ i, b.repr x i • b i) : R3 k) := by
        symm
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul_of_tower]
      _ = f := congrArg Subtype.val hrepr
  rw [← hrepr']
  apply Submodule.sum_mem
  intro i hi
  let j : IdealPieceIndex hA := ⟨⟨n, hn⟩, i⟩
  have hj : idealPieceGenerator hA j ∈
      Ideal.span (Set.range (idealPieceGenerator hA)) :=
    Ideal.subset_span ⟨j, rfl⟩
  have hj' := Submodule.smul_mem
    (Ideal.span (Set.range (idealPieceGenerator hA)))
    (algebraMap k (R3 k) (b.repr x i)) hj
  simpa [j, idealPieceGenerator, Algebra.smul_def] using hj'

lemma irrelevantPow_le_idealPieceSpan
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    MvPolynomial.idealOfVars (Fin 3) k ^ (e + 1) ≤
      Ideal.span (Set.range (idealPieceGenerator hA)) := by
  rw [MvPolynomial.pow_idealOfVars_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨d, hd, rfl⟩
  have hd' : d.degree = e + 1 := by simpa using hd
  have hhom := MvPolynomial.isHomogeneous_monomial (1 : k) hd'
  have hmem : monomial d 1 ∈ I :=
    homogeneous_mem_ideal_of_vanish_above hA (by omega) hhom
  have hp : monomial d 1 ∈ idealPiece I (e + 1) := ⟨hhom, hmem⟩
  exact mem_idealSpan_of_mem_idealPiece hA (by omega) hp

lemma ideal_eq_span_idealPieceGenerator
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    I = Ideal.span (Set.range (idealPieceGenerator hA)) := by
  apply le_antisymm
  · intro f hf
    rw [← DirectSum.sum_support_decompose
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) f]
    apply Ideal.sum_mem
    intro n hn
    by_cases hlow : n < e + 2
    · have hp : (DirectSum.decompose
          (MvPolynomial.homogeneousSubmodule (Fin 3) k) f n : R3 k) ∈
          idealPiece I n := by
        exact ⟨(DirectSum.decompose
          (MvPolynomial.homogeneousSubmodule (Fin 3) k) f n).property,
          hA.homogeneous n hf⟩
      exact mem_idealSpan_of_mem_idealPiece hA hlow hp
    · have hhom : MvPolynomial.IsHomogeneous
          (DirectSum.decompose
            (MvPolynomial.homogeneousSubmodule (Fin 3) k) f n : R3 k) n :=
        (DirectSum.decompose
          (MvPolynomial.homogeneousSubmodule (Fin 3) k) f n).property
      have hpow : (DirectSum.decompose
          (MvPolynomial.homogeneousSubmodule (Fin 3) k) f n : R3 k) ∈
          MvPolynomial.idealOfVars (Fin 3) k ^ (e + 1) := by
        simpa [irrelevantIdeal] using
          (isHomogeneous_mem_pow_idealOfVars hhom (by omega))
      exact irrelevantPow_le_idealPieceSpan hA hpow
  · apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    exact idealPieceGenerator_mem hA i

/-! The full piece basis is convenient for proving generation, but it is not
the basis of the last differential: most of those vectors are multiples of
earlier ones.  The following finite Nakayama-style thinning is the actual
homogeneous generator set used by the resolution package. -/

noncomputable def idealMinimalFamily
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    MinimalSpanningFamily (I : Submodule (R3 k) (R3 k))
      (idealPieceGenerator hA)
      (ideal_eq_span_idealPieceGenerator hA).symm := by
  exact MinimalSpanningFamily.ofSpan I (idealPieceGenerator hA)
    (ideal_eq_span_idealPieceGenerator hA).symm

noncomputable abbrev IdealMinimalIndex
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :=
  (idealMinimalFamily hA).indices.attach

noncomputable def idealMinimalGenerator
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    IdealMinimalIndex hA → R3 k :=
  fun i => idealPieceGenerator hA i.1.1

lemma idealMinimalGenerator_mem
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealMinimalIndex hA) : idealMinimalGenerator hA i ∈ I := by
  exact idealPieceGenerator_mem hA i.1.1

lemma idealMinimalGenerator_homogeneous
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealMinimalIndex hA) :
    MvPolynomial.IsHomogeneous (idealMinimalGenerator hA i) i.1.1.1 := by
  exact idealPieceGenerator_homogeneous hA i.1.1

lemma idealMinimalGenerator_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealMinimalIndex hA) : idealMinimalGenerator hA i ≠ 0 := by
  exact idealPieceGenerator_ne_zero hA i.1.1

lemma ideal_eq_span_idealMinimalGenerator
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    I = Ideal.span (Set.range (idealMinimalGenerator hA)) := by
  apply le_antisymm
  · intro f hf
    have hle : Ideal.span (Set.range (idealPieceGenerator hA)) ≤
        Ideal.span (Set.range (idealMinimalGenerator hA)) := by
      have himage :
          idealPieceGenerator hA ''
              ((idealMinimalFamily hA).indices : Set (IdealPieceIndex hA)) ⊆
            Set.range (idealMinimalGenerator hA) := by
        rintro g ⟨i, hi, rfl⟩
        exact ⟨⟨⟨i, hi⟩, Finset.mem_attach _ ⟨i, hi⟩⟩, rfl⟩
      calc
        Ideal.span (Set.range (idealPieceGenerator hA)) = I :=
          (ideal_eq_span_idealPieceGenerator hA).symm
        _ = Ideal.span (idealPieceGenerator hA ''
              ((idealMinimalFamily hA).indices : Set (IdealPieceIndex hA))) :=
          (idealMinimalFamily hA).span_eq.symm
        _ ≤ Ideal.span (Set.range (idealMinimalGenerator hA)) :=
          Ideal.span_mono himage
    apply hle
    rw [← ideal_eq_span_idealPieceGenerator hA]
    exact hf
  · apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    exact idealMinimalGenerator_mem hA i

/-! The finite signed part of the Hilbert numerator.  The actual minimal
complex supplies a nonnegative presentation of each coefficient; splitting
the difference of the two degree multiplicities into positive and negative
parts gives finite index types without making a choice of a minimal
resolution at the level of the final package. -/

noncomputable def signedMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA)
    (d : ℤ) : ℤ := paddedQMultiplicity C d - paddedPMultiplicity C d

abbrev LowPositiveIndex
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :=
  Σ b : Fin (e + 1), Fin ((signedMultiplicity C (b : ℤ)).toNat)

abbrev LowNegativeIndex
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :=
  Σ b : Fin (e + 1), Fin ((-signedMultiplicity C (b : ℤ)).toNat)

lemma int_toNat_split (a : ℤ) :
    ((a.toNat : ℤ) - ((-a).toNat : ℤ)) = a := by
  by_cases h : 0 ≤ a
  · rw [Int.toNat_of_nonneg h, Int.toNat_of_nonpos (by omega)]
    simp
  · have ha : a ≤ 0 := by omega
    rw [Int.toNat_of_nonpos ha, Int.toNat_of_nonneg (by omega)]
    simp

lemma shiftMultiplicity_sigma_fin
    {A : Type*} [Fintype A] (m : A → ℕ) (f : A → ℤ) (d : ℤ) :
    shiftMultiplicity (fun x : Σ a, Fin (m a) => f x.1) d =
      ∑ a : A, if f a = d then (m a : ℤ) else 0 := by
  classical
  unfold shiftMultiplicity
  norm_cast
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : f a = d
  · simp [h]
  · simp [h]

lemma shiftMultiplicity_lowPositive
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ) :
    shiftMultiplicity (fun x : LowPositiveIndex C => (x.1 : ℤ)) d =
    if 0 ≤ d ∧ d ≤ (e : ℤ) then
        (signedMultiplicity C d).toNat else 0 := by
  classical
  change shiftMultiplicity
      (fun x : Σ b : Fin (e + 1),
        Fin ((signedMultiplicity C (b : ℤ)).toNat) => (x.1 : ℤ)) d = _
  rw [shiftMultiplicity_sigma_fin
    (m := fun b : Fin (e + 1) =>
      (signedMultiplicity C (b : ℤ)).toNat)
    (f := fun b : Fin (e + 1) => (b : ℤ)) d]
  by_cases hd0 : 0 ≤ d
  · by_cases hde : d ≤ (e : ℤ)
    · let b : Fin (e + 1) := ⟨d.toNat, by omega⟩
      have hb : (b : ℤ) = d := by
        simp [b, Int.toNat_of_nonneg hd0]
      have hsum :
          (∑ a : Fin (e + 1),
            if (a : ℤ) = d then
              ((signedMultiplicity C (a : ℤ)).toNat : ℤ) else 0) =
            ((signedMultiplicity C d).toNat : ℤ) := by
        rw [← hb]
        have hsum0 :
            (∑ a : Fin (e + 1),
              if (a : ℤ) = (b : ℤ) then
                ((signedMultiplicity C (a : ℤ)).toNat : ℤ) else 0) =
              (if (b : ℤ) = (b : ℤ) then
                ((signedMultiplicity C (b : ℤ)).toNat : ℤ) else 0) := by
          apply Fintype.sum_eq_single b
          intro a ha
          by_cases had : (a : ℤ) = (b : ℤ)
          · exfalso
            apply ha
            apply Fin.ext
            exact_mod_cast had
          · simp [had]
        simpa using hsum0
      rw [hsum]
      simp [hd0, hde]
    · have hzero : ∀ a : Fin (e + 1), (a : ℤ) ≠ d := by
        intro a ha
        have hae_nat : a.1 ≤ e := by omega
        have hae : (a : ℤ) ≤ (e : ℤ) := by exact_mod_cast hae_nat
        omega
      simp [hzero, hd0, hde]
  · have hzero : ∀ a : Fin (e + 1), (a : ℤ) ≠ d := by
      intro a ha
      have ha0 : 0 ≤ (a : ℤ) := Int.natCast_nonneg _
      omega
    simp [hzero, hd0]

lemma shiftMultiplicity_lowNegative
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ) :
    shiftMultiplicity (fun x : LowNegativeIndex C => (x.1 : ℤ)) d =
    if 0 ≤ d ∧ d ≤ (e : ℤ) then
        (-signedMultiplicity C d).toNat else 0 := by
  classical
  change shiftMultiplicity
      (fun x : Σ b : Fin (e + 1),
        Fin ((-signedMultiplicity C (b : ℤ)).toNat) => (x.1 : ℤ)) d = _
  rw [shiftMultiplicity_sigma_fin
    (m := fun b : Fin (e + 1) =>
      (-signedMultiplicity C (b : ℤ)).toNat)
    (f := fun b : Fin (e + 1) => (b : ℤ)) d]
  by_cases hd0 : 0 ≤ d
  · by_cases hde : d ≤ (e : ℤ)
    · let b : Fin (e + 1) := ⟨d.toNat, by omega⟩
      have hb : (b : ℤ) = d := by
        simp [b, Int.toNat_of_nonneg hd0]
      have hsum :
          (∑ a : Fin (e + 1),
            if (a : ℤ) = d then
              ((-signedMultiplicity C (a : ℤ)).toNat : ℤ) else 0) =
            ((-signedMultiplicity C d).toNat : ℤ) := by
        rw [← hb]
        have hsum0 :
            (∑ a : Fin (e + 1),
              if (a : ℤ) = (b : ℤ) then
                ((-signedMultiplicity C (a : ℤ)).toNat : ℤ) else 0) =
              (if (b : ℤ) = (b : ℤ) then
                ((-signedMultiplicity C (b : ℤ)).toNat : ℤ) else 0) := by
          apply Fintype.sum_eq_single b
          intro a ha
          by_cases had : (a : ℤ) = (b : ℤ)
          · exfalso
            apply ha
            apply Fin.ext
            exact_mod_cast had
          · simp [had]
        simpa using hsum0
      rw [hsum]
      simp [hd0, hde]
    · have hzero : ∀ a : Fin (e + 1), (a : ℤ) ≠ d := by
        intro a ha
        have hae_nat : a.1 ≤ e := by omega
        have hae : (a : ℤ) ≤ (e : ℤ) := by exact_mod_cast hae_nat
        omega
      simp [hzero, hd0, hde]
  · have hzero : ∀ a : Fin (e + 1), (a : ℤ) ≠ d := by
      intro a ha
      have ha0 : 0 ≤ (a : ℤ) := Int.natCast_nonneg _
      omega
    simp [hzero, hd0]

lemma idealPiece_bot_of_le
    {I : Ideal (R3 k)} {n d : ℕ} (hbot : idealPiece I d = ⊥)
    (hnd : n ≤ d) : idealPiece I n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hhom : MvPolynomial.IsHomogeneous f n := hf.1
  have hmem : f ∈ I := hf.2
  let z : R3 k := MvPolynomial.X (0 : Fin 3) ^ (d - n)
  have hzhom : MvPolynomial.IsHomogeneous z (d - n) := by
    exact MvPolynomial.isHomogeneous_X_pow _ _
  have hprod : f * z ∈ idealPiece I d := by
    refine ⟨?_, ?_⟩
    · have hm := hhom.mul hzhom
      simpa [z, Nat.add_sub_of_le hnd] using hm
    · simpa [mul_comm] using I.mul_mem_left z hmem
  have hzero : f * z = 0 := by
    have hzbot : f * z ∈ (⊥ : Submodule k (R3 k)) := by
      rw [← hbot]
      exact hprod
    simpa using hzbot
  have hz : z ≠ 0 := by
    dsimp [z]
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := k) (0 : Fin 3))
  exact (mul_eq_zero.mp hzero).resolve_right hz

lemma hilb_eq_N_of_idealPiece_bot
    {I : Ideal (R3 k)} {n : ℕ} (hbot : idealPiece I n = ⊥) :
    hilb I (n : ℤ) = N n := by
  have h := idealHilb_add_hilb I (n : ℤ)
  rw [idealHilb, if_pos (Int.natCast_nonneg n), Int.toNat_natCast, hbot,
    finrank_bot] at h
  rw [Nz_natCast] at h
  norm_num at h
  exact h

lemma padded_signed_shiftSum
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (n : ℕ) (hn : n ≤ e) :
    shiftSum ((e : ℤ) + 3)
        (shiftMultiplicity (fun x : LowPositiveIndex C => (x.1 : ℤ)))
        (n : ℤ) -
      shiftSum ((e : ℤ) + 3)
        (shiftMultiplicity (fun x : LowNegativeIndex C => (x.1 : ℤ)))
        (n : ℤ) =
      shiftSum ((e : ℤ) + 3) (signedMultiplicity C) (n : ℤ) := by
  classical
  unfold shiftSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdI := Finset.mem_Icc.mp hd
  by_cases hr : 0 ≤ d ∧ d ≤ (e : ℤ)
  · rw [shiftMultiplicity_lowPositive, shiftMultiplicity_lowNegative, if_pos hr,
      if_pos hr]
    have hs := int_toNat_split (signedMultiplicity C d)
    rw [← sub_mul, hs]
  · have hp :
        shiftMultiplicity (fun x : LowPositiveIndex C => (x.1 : ℤ)) d = 0 := by
      rw [shiftMultiplicity_lowPositive, if_neg hr]
      norm_num
    have hq :
        shiftMultiplicity (fun x : LowNegativeIndex C => (x.1 : ℤ)) d = 0 := by
      rw [shiftMultiplicity_lowNegative, if_neg hr]
      norm_num
    rw [hp, hq]
    by_cases hde : (e : ℤ) < d
    · rw [Nz_neg (n - d) (by omega)]
      simp
    · have hdneg : d < 0 := by omega
      have hq0 : paddedQMultiplicity C d = 0 := by
        change
          ((Finset.univ.filter
            (fun x : C.β₂ => (C.qShift x : ℤ) = d)).card : ℤ) +
              (if d = (e : ℤ) + 3 then 1 else 0) = 0
        have hempty : Finset.univ.filter
            (fun x : C.β₂ => (C.qShift x : ℤ) = d) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          have hx' : (0 : ℤ) ≤ (C.qShift x : ℤ) := Int.natCast_nonneg _
          omega
        rw [hempty]
        simp [show d ≠ (e : ℤ) + 3 by omega]
      have hp0 : paddedPMultiplicity C d = 0 := by
        change
          ((Finset.univ.filter
            (fun x : C.β₁ => (C.pShift x : ℤ) = d)).card : ℤ) +
              (Finset.univ.filter
                (fun x : C.β₃ => (C.rShift x : ℤ) = d)).card = 0
        have hpempty : Finset.univ.filter
            (fun x : C.β₁ => (C.pShift x : ℤ) = d) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          have hx' : (0 : ℤ) ≤ (C.pShift x : ℤ) := Int.natCast_nonneg _
          omega
        have hrempty : Finset.univ.filter
            (fun x : C.β₃ => (C.rShift x : ℤ) = d) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          have hx' : (0 : ℤ) ≤ (C.rShift x : ℤ) := Int.natCast_nonneg _
          omega
        rw [hpempty, hrempty]
        simp
      have hsigned : signedMultiplicity C d = 0 := by
        simp [signedMultiplicity, hq0, hp0]
      rw [hsigned]
      simp

lemma signed_shiftSum_eq_finrank_of_le
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (n : ℕ) (hn : n ≤ e) :
    shiftSum ((e : ℤ) + 3) (signedMultiplicity C) (n : ℤ) =
      (finrank k (gradedDualPiece I e n) : ℤ) - 2 * Nz (n : ℤ) := by
  have hEuler := degreewise_euler_of_minimal hA C n hn
  have hExtra : shiftSum ((e : ℤ) + 3)
      (fun d : ℤ => if d = (e : ℤ) + 3 then 1 else 0) (n : ℤ) = 0 := by
    apply shiftSum_vanish
    intro d hd0 hdn
    have hne : d ≠ (e : ℤ) + 3 := by omega
    simp [hne]
  have hpPad : shiftSum ((e : ℤ) + 3)
      (paddedPMultiplicity C) (n : ℤ) =
        shiftSum ((e : ℤ) + 3) C.pMultiplicity (n : ℤ) +
          shiftSum ((e : ℤ) + 3) C.rMultiplicity (n : ℤ) := by
    rw [show paddedPMultiplicity C =
      (fun d => C.pMultiplicity d + C.rMultiplicity d) by rfl,
      shiftSum_add]
  have hqPad : shiftSum ((e : ℤ) + 3)
      (paddedQMultiplicity C) (n : ℤ) =
        shiftSum ((e : ℤ) + 3) C.qMultiplicity (n : ℤ) := by
    rw [show paddedQMultiplicity C =
      (fun d => C.qMultiplicity d +
        (if d = (e : ℤ) + 3 then 1 else 0)) by rfl,
      shiftSum_add, hExtra, add_zero]
  have hEuler' :
      (finrank k (gradedDualPiece I e n) : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ) =
        2 * Nz (n : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ) := by
    calc
      (finrank k (gradedDualPiece I e n) : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ) =
          (finrank k (gradedDualPiece I e n) : ℤ) +
            shiftSum ((e : ℤ) + 3) C.pMultiplicity (n : ℤ) +
            shiftSum ((e : ℤ) + 3) C.rMultiplicity (n : ℤ) := by
              rw [hpPad]
              ring
      _ = 2 * Nz (n : ℤ) +
            shiftSum ((e : ℤ) + 3) C.qMultiplicity (n : ℤ) := hEuler
      _ = 2 * Nz (n : ℤ) +
            shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ) := by
              rw [hqPad]
  have hsplit :
      shiftSum ((e : ℤ) + 3) (signedMultiplicity C) (n : ℤ) =
        shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (n : ℤ) -
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (n : ℤ) := by
    unfold signedMultiplicity shiftSum
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  linarith [hEuler']

lemma signedMultiplicity_zero
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : signedMultiplicity C 0 = 0 := by
  have hsum := signed_shiftSum_eq_finrank_of_le C 0 (by omega)
  have hsingle : shiftSum ((e : ℤ) + 3) (signedMultiplicity C) 0 =
      signedMultiplicity C 0 := by
    apply shiftSum_single
    · omega
    · omega
    · intro d hd0 hdl
      omega
  have hfin : (finrank k (gradedDualPiece I e 0) : ℤ) = 2 := by
    have h := finrank_gradedDualPiece I e 0 (by omega)
    simpa [reversedHilb, hA.hilb_top] using h
  have hsum' : shiftSum ((e : ℤ) + 3) (signedMultiplicity C) 0 =
      (finrank k (gradedDualPiece I e 0) : ℤ) - 2 * Nz (0 : ℤ) := by
    simpa using hsum
  rw [hsingle, hfin, Nz_zero] at hsum'
  linarith

lemma signedMultiplicity_one_nonpos
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : signedMultiplicity C 1 ≤ 0 := by
  have hsum := signed_shiftSum_eq_finrank_of_le C 1 (by
    have he := hA.two_le_socleDegree
    omega)
  have hzero := signedMultiplicity_zero C
  have hsingle : shiftSum ((e : ℤ) + 3) (signedMultiplicity C) 1 =
      signedMultiplicity C 1 := by
    apply shiftSum_single
    · omega
    · omega
    · intro d hd0 hdl
      have : d = 0 := by omega
      simpa [this, hzero]
  have hfinle : (finrank k (gradedDualPiece I e 1) : ℤ) ≤ 6 := by
    letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
    have hsurj := inverseSystemPieceMap_surjective
      (n := e - 1) hA (Nat.sub_le _ _)
    have hdim := LinearMap.finrank_le_finrank_of_surjective
      (f := inverseSystemPieceMap hA (e - 1)) hsurj
    have hsource : finrank k (Fin 2 →
        homogeneousSubmodule (Fin 3) k 1) = 6 := by
      rw [Module.finrank_pi_fintype]
      simp [finrank_homogeneousSubmodule]
    have he := hA.two_le_socleDegree
    rw [show e - (e - 1) = 1 by omega] at hdim
    rw [hsource] at hdim
    exact_mod_cast hdim
  have hsum' : shiftSum ((e : ℤ) + 3) (signedMultiplicity C) 1 =
      (finrank k (gradedDualPiece I e 1) : ℤ) - 2 * Nz (1 : ℤ) := by
    simpa using hsum
  rw [hsingle] at hsum'
  have hNz1 : Nz (1 : ℤ) = 3 := by norm_num [Nz, N]
  rw [hNz1] at hsum'
  linarith

lemma signed_shiftSum_eq_hilb_of_idealPiece_bot
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (m d : ℕ)
    (hm : m ≤ e) (hmd : e - m ≤ d)
    (hbot : idealPiece I d = ⊥) :
    shiftSum ((e : ℤ) + 3) (signedMultiplicity C) (m : ℤ) =
      hilb I ((e - m : ℕ) : ℤ) - 2 * Nz (m : ℤ) := by
  have hlow : idealPiece I (e - m) = ⊥ :=
    idealPiece_bot_of_le hbot hmd
  have hhilb : hilb I ((e - m : ℕ) : ℤ) = N (e - m) :=
    hilb_eq_N_of_idealPiece_bot hlow
  have hfin : (finrank k (gradedDualPiece I e m) : ℤ) =
      hilb I ((e - m : ℕ) : ℤ) := by
    have h := finrank_gradedDualPiece I e m hm
    simpa [reversedHilb, Nat.cast_sub hm] using h
  have heuler := degreewise_euler_of_minimal hA C m hm
  have hsplit :
      shiftSum ((e : ℤ) + 3) (signedMultiplicity C) (m : ℤ) =
        shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (m : ℤ) -
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (m : ℤ) := by
    unfold signedMultiplicity shiftSum
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  have hExtra : shiftSum ((e : ℤ) + 3)
      (fun d : ℤ => if d = (e : ℤ) + 3 then 1 else 0) (m : ℤ) = 0 := by
    apply shiftSum_vanish
    intro b hb0 hbm
    have hne : b ≠ (e : ℤ) + 3 := by omega
    simp [hne]
  have hpPad : shiftSum ((e : ℤ) + 3)
      (paddedPMultiplicity C) (m : ℤ) =
        shiftSum ((e : ℤ) + 3) C.pMultiplicity (m : ℤ) +
          shiftSum ((e : ℤ) + 3) C.rMultiplicity (m : ℤ) := by
    rw [show paddedPMultiplicity C =
      (fun b => C.pMultiplicity b + C.rMultiplicity b) by rfl,
      shiftSum_add]
  have hqPad : shiftSum ((e : ℤ) + 3)
      (paddedQMultiplicity C) (m : ℤ) =
        shiftSum ((e : ℤ) + 3) C.qMultiplicity (m : ℤ) := by
    rw [show paddedQMultiplicity C =
      (fun b => C.qMultiplicity b +
        (if b = (e : ℤ) + 3 then 1 else 0)) by rfl,
      shiftSum_add, hExtra, add_zero]
  have heuler' :
      (finrank k (gradedDualPiece I e m) : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (m : ℤ) =
        2 * Nz (m : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (m : ℤ) := by
    calc
      (finrank k (gradedDualPiece I e m) : ℤ) +
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (m : ℤ) =
          (finrank k (gradedDualPiece I e m) : ℤ) +
            shiftSum ((e : ℤ) + 3) C.pMultiplicity (m : ℤ) +
            shiftSum ((e : ℤ) + 3) C.rMultiplicity (m : ℤ) := by
              rw [hpPad]
              ring
      _ = 2 * Nz (m : ℤ) +
            shiftSum ((e : ℤ) + 3) C.qMultiplicity (m : ℤ) := heuler
      _ = 2 * Nz (m : ℤ) +
            shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (m : ℤ) := by
              rw [hqPad]
  have hqp :
      shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (m : ℤ) -
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (m : ℤ) =
        (finrank k (gradedDualPiece I e m) : ℤ) - 2 * Nz (m : ℤ) := by
    linarith [heuler']
  calc
    shiftSum ((e : ℤ) + 3) (signedMultiplicity C) (m : ℤ) =
        shiftSum ((e : ℤ) + 3) (paddedQMultiplicity C) (m : ℤ) -
          shiftSum ((e : ℤ) + 3) (paddedPMultiplicity C) (m : ℤ) := hsplit
    _ = (finrank k (gradedDualPiece I e m) : ℤ) - 2 * Nz (m : ℤ) := hqp
    _ = hilb I ((e - m : ℕ) : ℤ) - 2 * Nz (m : ℤ) := by rw [hfin]

lemma third_difference_Nz_zero {t : ℤ} (ht : 2 ≤ t) :
    Nz t - 3 * Nz (t - 1) + 3 * Nz (t - 2) - Nz (t - 3) = 0 := by
  have h₀ := Nz_second_diff t
  have h₁ := Nz_second_diff (t - 1)
  rw [if_pos (by omega : (0 : ℤ) ≤ t)] at h₀
  rw [if_pos (by omega : (0 : ℤ) ≤ t - 1)] at h₁
  have h₁' : Nz (t - 1) - 2 * Nz (t - 2) + Nz (t - 3) = 1 := by
    convert h₁ using 1 <;> ring
  linarith

lemma idealPiece_ne_bot_of_signed_pos
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (b : Fin (e + 1))
    (hb : 0 < signedMultiplicity C (b : ℤ)) :
    idealPiece I (e + 3 - b.1) ≠ ⊥ := by
  intro hbot
  let d : ℕ := e + 3 - b.1
  have hddef : d = e + 3 - b.1 := rfl
  by_cases hsmall : b.1 < 3
  · have hde : e < d := by dsimp [d]; omega
    let f : R3 k := MvPolynomial.X (0 : Fin 3) ^ d
    have hfhom : MvPolynomial.IsHomogeneous f d := by
      exact MvPolynomial.isHomogeneous_X_pow _ _
    have hfmem : f ∈ I := by
      exact homogeneous_mem_ideal_of_vanish_above hA hde hfhom
    have hfpiece : f ∈ idealPiece I d := ⟨hfhom, hfmem⟩
    have hfzero : f = 0 := by
      rw [hbot] at hfpiece
      simpa using hfpiece
    exact (pow_ne_zero _
      (MvPolynomial.X_ne_zero (R := k) (0 : Fin 3))) hfzero
  · have hb3 : 3 ≤ b.1 := by omega
    have hdm0 : e - b.1 ≤ d := by dsimp [d]; omega
    have hdm1 : e - (b.1 - 1) ≤ d := by dsimp [d]; omega
    have hdm2 : e - (b.1 - 2) ≤ d := by dsimp [d]; omega
    have hdm3 : e - (b.1 - 3) ≤ d := by dsimp [d]; omega
    have hpiece0 : idealPiece I (e - b.1) = ⊥ :=
      idealPiece_bot_of_le hbot hdm0
    have hpiece1 : idealPiece I (e - (b.1 - 1)) = ⊥ :=
      idealPiece_bot_of_le hbot hdm1
    have hpiece2 : idealPiece I (e - (b.1 - 2)) = ⊥ :=
      idealPiece_bot_of_le hbot hdm2
    have hpiece3 : idealPiece I (e - (b.1 - 3)) = ⊥ :=
      idealPiece_bot_of_le hbot hdm3
    have h0 := signed_shiftSum_eq_hilb_of_idealPiece_bot C b.1 d
      (by omega) hdm0 hbot
    have h1 := signed_shiftSum_eq_hilb_of_idealPiece_bot C (b.1 - 1) d
      (by omega) hdm1 hbot
    have h2 := signed_shiftSum_eq_hilb_of_idealPiece_bot C (b.1 - 2) d
      (by omega) hdm2 hbot
    have h3 := signed_shiftSum_eq_hilb_of_idealPiece_bot C (b.1 - 3) d
      (by omega) hdm3 hbot
    rw [hilb_eq_N_of_idealPiece_bot hpiece0, Nz_natCast] at h0
    rw [hilb_eq_N_of_idealPiece_bot hpiece1, Nz_natCast] at h1
    rw [hilb_eq_N_of_idealPiece_bot hpiece2, Nz_natCast] at h2
    rw [hilb_eq_N_of_idealPiece_bot hpiece3, Nz_natCast] at h3
    have hdb0 : e - b.1 = d - 3 := by dsimp [d]; omega
    have hdb1 : e - (b.1 - 1) = d - 2 := by dsimp [d]; omega
    have hdb2 : e - (b.1 - 2) = d - 1 := by dsimp [d]; omega
    have hdb3 : e - (b.1 - 3) = d := by dsimp [d]; omega
    rw [hdb0] at h0
    rw [hdb1] at h1
    rw [hdb2] at h2
    rw [hdb3] at h3
    have hcast1 : ((b.1 - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
    have hcast2 : ((b.1 - 2 : ℕ) : ℤ) = (b : ℤ) - 2 := by omega
    have hcast3 : ((b.1 - 3 : ℕ) : ℤ) = (b : ℤ) - 3 := by omega
    rw [hcast1] at h1
    rw [hcast2] at h2
    rw [hcast3] at h3
    have hthird := shiftSum_third_diff ((e : ℤ) + 3)
      (signedMultiplicity C) (b : ℤ) (by omega) (by omega)
    rw [h0, h1, h2, h3] at hthird
    have hdN := third_difference_Nz_zero (t := (d : ℤ)) (by omega)
    have hbN := third_difference_Nz_zero (t := (b.1 : ℤ)) (by omega)
    have hdN' : N d - 3 * N (d - 1) + 3 * N (d - 2) - N (d - 3) = 0 := by
      have h1 : Nz ((d : ℤ) - 1) = N (d - 1) := by
        rw [show (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) by omega, Nz_natCast]
      have h2 : Nz ((d : ℤ) - 2) = N (d - 2) := by
        rw [show (d : ℤ) - 2 = ((d - 2 : ℕ) : ℤ) by omega, Nz_natCast]
      have h3 : Nz ((d : ℤ) - 3) = N (d - 3) := by
        rw [show (d : ℤ) - 3 = ((d - 3 : ℕ) : ℤ) by omega, Nz_natCast]
      rw [Nz_natCast, h1, h2, h3] at hdN
      exact hdN
    have hbN' : N b.1 - 3 * N (b.1 - 1) +
        3 * N (b.1 - 2) - N (b.1 - 3) = 0 := by
      have h1 : Nz ((b.1 : ℤ) - 1) = N (b.1 - 1) := by
        rw [show (b.1 : ℤ) - 1 = ((b.1 - 1 : ℕ) : ℤ) by omega, Nz_natCast]
      have h2 : Nz ((b.1 : ℤ) - 2) = N (b.1 - 2) := by
        rw [show (b.1 : ℤ) - 2 = ((b.1 - 2 : ℕ) : ℤ) by omega, Nz_natCast]
      have h3 : Nz ((b.1 : ℤ) - 3) = N (b.1 - 3) := by
        rw [show (b.1 : ℤ) - 3 = ((b.1 - 3 : ℕ) : ℤ) by omega, Nz_natCast]
      rw [Nz_natCast, h1, h2, h3] at hbN
      exact hbN
    have : signedMultiplicity C (b : ℤ) = 0 := by
      linarith [hdN', hbN']
    omega

noncomputable def idealPieceWitness
    {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (n : ℕ) (hn : idealPiece I n ≠ ⊥) : R3 k :=
  (Submodule.exists_mem_ne_zero_of_ne_bot hn).choose

lemma idealPieceWitness_mem
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (n : ℕ) (hn : idealPiece I n ≠ ⊥) :
    idealPieceWitness hA n hn ∈ idealPiece I n := by
  exact (Submodule.exists_mem_ne_zero_of_ne_bot hn).choose_spec.1

lemma idealPieceWitness_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (n : ℕ) (hn : idealPiece I n ≠ ⊥) : idealPieceWitness hA n hn ≠ 0 := by
  exact (Submodule.exists_mem_ne_zero_of_ne_bot hn).choose_spec.2

lemma idealPieceWitness_homogeneous
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (n : ℕ) (hn : idealPiece I n ≠ ⊥) :
    MvPolynomial.IsHomogeneous (idealPieceWitness hA n hn) n := by
  exact (idealPieceWitness_mem (hA := hA) n hn).1

lemma idealPieceWitness_mem_ideal
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (n : ℕ) (hn : idealPiece I n ≠ ⊥) : idealPieceWitness hA n hn ∈ I := by
  exact (idealPieceWitness_mem (hA := hA) n hn).2

lemma signedMultiplicity_pos_of_lowPositive
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (x : LowPositiveIndex C) :
    0 < signedMultiplicity C (x.1 : ℤ) := by
  by_contra h
  have hs : signedMultiplicity C (x.1 : ℤ) ≤ 0 := by omega
  have hz : (signedMultiplicity C (x.1 : ℤ)).toNat = 0 :=
    Int.toNat_of_nonpos hs
  have hx := x.2.isLt
  omega

noncomputable def idealPieceShift
    {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (i : IdealPieceIndex hA) : ℤ :=
  (e : ℤ) + 3 - (i.1.1 : ℤ)

lemma idealPieceShift_nonneg
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealPieceIndex hA) : 0 ≤ idealPieceShift hA i := by
  dsimp [idealPieceShift]
  have hi : i.1.1 ≤ e + 1 := by omega
  omega

lemma idealPieceShift_generator_degree
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealPieceIndex hA) :
    (((e : ℤ) + 3 - idealPieceShift hA i).toNat) = i.1.1 := by
  have hi : i.1.1 ≤ e + 1 := by omega
  have hcast : ((i.1.1 : ℕ) : ℤ) = (i.1.1 : ℤ) := rfl
  simp [idealPieceShift]

abbrev CanonicalPIndex
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :=
  IdealPieceIndex hA ⊕ LowNegativeIndex C

abbrev CanonicalQIndex
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :=
  IdealPieceIndex hA ⊕ LowPositiveIndex C

noncomputable def canonicalPShift
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : CanonicalPIndex C → ℤ :=
  Sum.elim (idealPieceShift hA) (fun x => (x.1 : ℤ))

noncomputable def canonicalQShift
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : CanonicalQIndex C → ℤ :=
  Sum.elim (idealPieceShift hA) (fun x => (x.1 : ℤ))

lemma canonicalPShift_nonneg
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (i : CanonicalPIndex C) :
    0 ≤ canonicalPShift C i := by
  cases i with
  | inl i => exact idealPieceShift_nonneg hA i
  | inr i => exact Int.natCast_nonneg _

lemma canonicalQShift_nonneg
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (i : CanonicalQIndex C) :
    0 ≤ canonicalQShift C i := by
  cases i with
  | inl i => exact idealPieceShift_nonneg hA i
  | inr i => exact Int.natCast_nonneg _

noncomputable def canonicalIdealGenerator
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : CanonicalQIndex C → R3 k :=
  Sum.elim (idealPieceGenerator hA) (fun x =>
    idealPieceWitness hA (e + 3 - x.1.1)
      (idealPiece_ne_bot_of_signed_pos C x.1
        (signedMultiplicity_pos_of_lowPositive C x)))

lemma canonicalIdealGenerator_mem
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (j : CanonicalQIndex C) :
    canonicalIdealGenerator C j ∈ I := by
  cases j with
  | inl j => exact idealPieceGenerator_mem hA j
  | inr j =>
      exact idealPieceWitness_mem_ideal (hA := hA) (e + 3 - j.1.1)
        (idealPiece_ne_bot_of_signed_pos C j.1
          (signedMultiplicity_pos_of_lowPositive C j))

lemma canonicalIdealGenerator_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (j : CanonicalQIndex C) :
    canonicalIdealGenerator C j ≠ 0 := by
  cases j with
  | inl j => exact idealPieceGenerator_ne_zero hA j
  | inr j =>
      exact idealPieceWitness_ne_zero (hA := hA) (e + 3 - j.1.1)
        (idealPiece_ne_bot_of_signed_pos C j.1
          (signedMultiplicity_pos_of_lowPositive C j))

lemma canonicalIdealGenerator_homogeneous
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (j : CanonicalQIndex C) :
    MvPolynomial.IsHomogeneous (canonicalIdealGenerator C j)
      (((e : ℤ) + 3 - canonicalQShift C j).toNat) := by
  cases j with
  | inl j =>
      rw [show canonicalQShift C (Sum.inl j) = idealPieceShift hA j by rfl,
        idealPieceShift_generator_degree hA j]
      exact idealPieceGenerator_homogeneous hA j
  | inr j =>
      let d : ℕ := e + 3 - j.1.1
      have hd : d = e + 3 - j.1.1 := rfl
      have hdeg : (((e : ℤ) + 3 - canonicalQShift C (Sum.inr j)).toNat) = d := by
        dsimp [canonicalQShift, d]
        have hj : j.1.1 ≤ e := by omega
        simp
        omega
      rw [hdeg]
      exact idealPieceWitness_homogeneous (hA := hA) d
        (idealPiece_ne_bot_of_signed_pos C j.1
          (signedMultiplicity_pos_of_lowPositive C j))

lemma canonicalIdealGenerator_span
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    I = Ideal.span (Set.range (canonicalIdealGenerator C)) := by
  apply le_antisymm
  · intro f hf
    have hle : Ideal.span (Set.range (idealPieceGenerator hA)) ≤
        Ideal.span (Set.range (canonicalIdealGenerator C)) := by
      apply Ideal.span_le.mpr
      rintro g ⟨i, rfl⟩
      exact Ideal.subset_span ⟨Sum.inl i, rfl⟩
    apply hle
    rw [← ideal_eq_span_idealPieceGenerator hA]
    exact hf
  · apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨j, rfl⟩ := hf
    exact canonicalIdealGenerator_mem C j

lemma canonicalP_shiftMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ) :
    shiftMultiplicity (canonicalPShift C) d =
      shiftMultiplicity (idealPieceShift hA) d +
        shiftMultiplicity (fun x : LowNegativeIndex C => (x.1 : ℤ)) d := by
  rw [show canonicalPShift C =
      Sum.elim (idealPieceShift hA)
        (fun x : LowNegativeIndex C => (x.1 : ℤ)) by rfl,
    shiftMultiplicity_sum]

lemma canonicalQ_shiftMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ) :
    shiftMultiplicity (canonicalQShift C) d =
      shiftMultiplicity (idealPieceShift hA) d +
        shiftMultiplicity (fun x : LowPositiveIndex C => (x.1 : ℤ)) d := by
  rw [show canonicalQShift C =
      Sum.elim (idealPieceShift hA)
        (fun x : LowPositiveIndex C => (x.1 : ℤ)) by rfl,
    shiftMultiplicity_sum]

lemma canonical_shiftSum_difference
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (n : ℕ) :
    shiftSum ((e : ℤ) + 3) (shiftMultiplicity (canonicalQShift C)) (n : ℤ) -
        shiftSum ((e : ℤ) + 3) (shiftMultiplicity (canonicalPShift C)) (n : ℤ) =
      shiftSum ((e : ℤ) + 3)
          (shiftMultiplicity (fun x : LowPositiveIndex C => (x.1 : ℤ))) (n : ℤ) -
        shiftSum ((e : ℤ) + 3)
          (shiftMultiplicity (fun x : LowNegativeIndex C => (x.1 : ℤ))) (n : ℤ) := by
  have hq : shiftMultiplicity (canonicalQShift C) =
      (fun d => shiftMultiplicity (idealPieceShift hA) d +
        shiftMultiplicity (fun x : LowPositiveIndex C => (x.1 : ℤ)) d) := by
    funext d
    exact canonicalQ_shiftMultiplicity C d
  have hp : shiftMultiplicity (canonicalPShift C) =
      (fun d => shiftMultiplicity (idealPieceShift hA) d +
        shiftMultiplicity (fun x : LowNegativeIndex C => (x.1 : ℤ)) d) := by
    funext d
    exact canonicalP_shiftMultiplicity C d
  rw [hq, hp, shiftSum_add, shiftSum_add]
  ring

lemma canonical_shiftSum_difference_eq_finrank
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (n : ℕ) (hn : n ≤ e) :
    shiftSum ((e : ℤ) + 3) (shiftMultiplicity (canonicalQShift C)) (n : ℤ) -
        shiftSum ((e : ℤ) + 3) (shiftMultiplicity (canonicalPShift C)) (n : ℤ) =
      (finrank k (gradedDualPiece I e n) : ℤ) - 2 * Nz (n : ℤ) := by
  rw [canonical_shiftSum_difference]
  rw [padded_signed_shiftSum C n hn]
  exact signed_shiftSum_eq_finrank_of_le C n hn

lemma finrank_gradedDualPiece_le_twoNz
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (n : ℕ) (hn : n ≤ e) :
    finrank k (gradedDualPiece I e n) ≤ (2 * Nz (n : ℤ)).toNat := by
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  have hsurj := inverseSystemPieceMap_surjective
    (n := e - n) hA (Nat.sub_le _ _)
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (f := inverseSystemPieceMap hA (e - n)) hsurj
  have hsource : finrank k (Fin 2 →
      homogeneousSubmodule (Fin 3) k n) =
      2 * finrank k (homogeneousSubmodule (Fin 3) k n) := by
    rw [Module.finrank_pi_fintype]
    simp
  have hN : finrank k (homogeneousSubmodule (Fin 3) k n) =
      (n + 2).choose 2 := finrank_homogeneousSubmodule k _
  have hdim' : finrank k (gradedDualPiece I e n) ≤
      finrank k (Fin 2 → homogeneousSubmodule (Fin 3) k n) := by
    have hsub : e - (e - n) = n := Nat.sub_sub_self hn
    rw [hsub] at hdim
    exact hdim
  rw [hsource, hN] at hdim'
  have hbound : (finrank k (gradedDualPiece I e n) : ℤ) ≤
      2 * Nz (n : ℤ) := by
    change (finrank k (gradedDualPiece I e n) : ℤ) ≤
      2 * ((n + 2).choose 2 : ℤ)
    exact_mod_cast hdim'
  have hnonneg : 0 ≤ 2 * Nz (n : ℤ) :=
    mul_nonneg (by norm_num) (Nz_nonneg _)
  have hcast : ((2 * Nz (n : ℤ)).toNat : ℤ) = 2 * Nz (n : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  have hbound' : (finrank k (gradedDualPiece I e n) : ℤ) ≤
      ((2 * Nz (n : ℤ)).toNat : ℤ) := by
    rw [hcast]
    exact hbound
  exact_mod_cast hbound'

lemma canonical_degreewise_exact
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    ∀ n : ℕ, n ≤ e → Nonempty
      (ExactPresentation k (gradedDualPiece I e n)
        (shiftSum ((e : ℤ) + 3) (shiftMultiplicity (canonicalQShift C)) (n : ℤ)).toNat
        (shiftSum ((e : ℤ) + 3) (shiftMultiplicity (canonicalPShift C)) (n : ℤ)).toNat
        (2 * Nz (n : ℤ)).toNat) := by
  classical
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  intro n hn
  let qn := shiftSum ((e : ℤ) + 3)
    (shiftMultiplicity (canonicalQShift C)) (n : ℤ)
  let pn := shiftSum ((e : ℤ) + 3)
    (shiftMultiplicity (canonicalPShift C)) (n : ℤ)
  let mn := 2 * Nz (n : ℤ)
  have hqn : 0 ≤ qn := by
    dsimp [qn]
    exact shiftSum_nonneg _ (fun d => shiftMultiplicity_nonneg _ _) _
  have hpn : 0 ≤ pn := by
    dsimp [pn]
    exact shiftSum_nonneg _ (fun d => shiftMultiplicity_nonneg _ _) _
  have hmn : 0 ≤ mn := by
    dsimp [mn]
    exact mul_nonneg (by norm_num) (Nz_nonneg _)
  have hdiff : qn - pn =
      (finrank k (gradedDualPiece I e n) : ℤ) - mn := by
    dsimp [qn, pn, mn]
    exact canonical_shiftSum_difference_eq_finrank C n hn
  have hqcast : (qn.toNat : ℤ) = qn := Int.toNat_of_nonneg hqn
  have hpcast : (pn.toNat : ℤ) = pn := Int.toNat_of_nonneg hpn
  have hmcast : (mn.toNat : ℤ) = mn := Int.toNat_of_nonneg hmn
  have heZ :
      (finrank k (gradedDualPiece I e n) : ℤ) + (pn.toNat : ℤ) =
        (mn.toNat : ℤ) + (qn.toNat : ℤ) := by
    rw [hpcast, hmcast, hqcast]
    linarith
  have he : finrank k (gradedDualPiece I e n) + pn.toNat =
      mn.toNat + qn.toNat := by exact_mod_cast heZ
  have hmle : finrank k (gradedDualPiece I e n) ≤ mn.toNat :=
    finrank_gradedDualPiece_le_twoNz hA n hn
  have hqle : qn.toNat ≤ pn.toNat := by omega
  exact exactPresentationOfFinrank hmle hqle he

/-! The minimal ideal family is inserted into the signed numerator with the
unique complementary padding.  At a shift `b`, the two residual fibres have
cardinalities `(a_b-g_b)⁺` and `(g_b-a_b)⁺`, so their difference is exactly
the signed coefficient `a_b`.  This keeps the degreewise Euler identity,
while removing the redundant high-degree piece basis from the last
differential. -/

noncomputable def minimalIdealShift
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    IdealMinimalIndex hA → ℤ := fun i =>
  (e : ℤ) + 3 - (i.1.1.1 : ℤ)

lemma minimalIdealShift_nonneg
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealMinimalIndex hA) : 0 ≤ minimalIdealShift hA i := by
  dsimp [minimalIdealShift]
  have hi : i.1.1.1 ≤ e + 1 := by omega
  omega

lemma minimalIdealShift_generator_degree
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (i : IdealMinimalIndex hA) :
    (((e : ℤ) + 3 - minimalIdealShift hA i).toNat) = i.1.1.1 := by
  have hi : i.1.1.1 ≤ e + 1 := by omega
  simp [minimalIdealShift]

abbrev MinimalResidualQIndex
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :=
  LowPositiveIndex C

abbrev MinimalResidualPIndex
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :=
  LowNegativeIndex C

noncomputable instance minimalResidualQIndex_fintype
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    Fintype (MinimalResidualQIndex C) := by
  dsimp [MinimalResidualQIndex]
  infer_instance

noncomputable instance minimalResidualPIndex_fintype
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    Fintype (MinimalResidualPIndex C) := by
  dsimp [MinimalResidualPIndex]
  infer_instance

abbrev MinimalPIndex
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :=
  IdealMinimalIndex hA ⊕ MinimalResidualPIndex C

abbrev MinimalQIndex
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :=
  IdealMinimalIndex hA ⊕ MinimalResidualQIndex C

noncomputable def minimalPShift
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : MinimalPIndex C → ℤ :=
  Sum.elim (minimalIdealShift hA)
    (fun x => (x.1 : ℤ))

noncomputable def minimalQShift
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : MinimalQIndex C → ℤ :=
  Sum.elim (minimalIdealShift hA)
    (fun x => (x.1 : ℤ))

lemma minimalPShift_nonneg
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (i : MinimalPIndex C) :
    0 ≤ minimalPShift C i := by
  cases i with
  | inl i => exact minimalIdealShift_nonneg hA i
  | inr i => exact Int.natCast_nonneg _

lemma minimalQShift_nonneg
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (i : MinimalQIndex C) :
    0 ≤ minimalQShift C i := by
  cases i with
  | inl i => exact minimalIdealShift_nonneg hA i
  | inr i => exact Int.natCast_nonneg _

noncomputable def minimalIdealGenerator
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) : MinimalQIndex C → R3 k :=
  Sum.elim (idealMinimalGenerator hA) (fun x =>
    idealPieceWitness hA (e + 3 - x.1.1)
      (idealPiece_ne_bot_of_signed_pos C x.1
        (signedMultiplicity_pos_of_lowPositive C x)))

lemma minimalIdealGenerator_mem
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (j : MinimalQIndex C) :
    minimalIdealGenerator C j ∈ I := by
  cases j with
  | inl j => exact idealMinimalGenerator_mem hA j
  | inr j =>
      exact idealPieceWitness_mem_ideal (hA := hA) (e + 3 - j.1.1)
        (idealPiece_ne_bot_of_signed_pos C j.1
          (signedMultiplicity_pos_of_lowPositive C j))

lemma minimalIdealGenerator_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (j : MinimalQIndex C) :
    minimalIdealGenerator C j ≠ 0 := by
  cases j with
  | inl j => exact idealMinimalGenerator_ne_zero hA j
  | inr j =>
      exact idealPieceWitness_ne_zero (hA := hA) (e + 3 - j.1.1)
        (idealPiece_ne_bot_of_signed_pos C j.1
          (signedMultiplicity_pos_of_lowPositive C j))

lemma minimalIdealGenerator_homogeneous
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (j : MinimalQIndex C) :
    MvPolynomial.IsHomogeneous (minimalIdealGenerator C j)
      (((e : ℤ) + 3 - minimalQShift C j).toNat) := by
  cases j with
  | inl j =>
      rw [show minimalQShift C (Sum.inl j) = minimalIdealShift hA j by rfl,
        minimalIdealShift_generator_degree hA j]
      exact idealMinimalGenerator_homogeneous hA j
  | inr j =>
      let d : ℕ := e + 3 - j.1.1
      have hdeg : (((e : ℤ) + 3 - minimalQShift C (Sum.inr j)).toNat) = d := by
        dsimp [minimalQShift, d]
        have hj : j.1.1 ≤ e := by omega
        simp
        omega
      rw [hdeg]
      exact idealPieceWitness_homogeneous (hA := hA) (e + 3 - j.1.1)
        (idealPiece_ne_bot_of_signed_pos C j.1
          (signedMultiplicity_pos_of_lowPositive C j))

lemma minimalIdealGenerator_span
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    I = Ideal.span (Set.range (minimalIdealGenerator C)) := by
  apply le_antisymm
  · intro f hf
    have hle : Ideal.span (Set.range (idealMinimalGenerator hA)) ≤
        Ideal.span (Set.range (minimalIdealGenerator C)) := by
      apply Ideal.span_le.mpr
      rintro g ⟨i, rfl⟩
      exact Ideal.subset_span ⟨Sum.inl i, rfl⟩
    apply hle
    rw [← ideal_eq_span_idealMinimalGenerator hA]
    exact hf
  · apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨j, rfl⟩ := hf
    exact minimalIdealGenerator_mem C j

lemma minimalQ_shiftMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ) :
    shiftMultiplicity (minimalQShift C) d =
      shiftMultiplicity (minimalIdealShift hA) d +
        shiftMultiplicity (fun x : MinimalResidualQIndex C => (x.1 : ℤ)) d := by
  rw [show minimalQShift C =
      Sum.elim (minimalIdealShift hA)
        (fun x : MinimalResidualQIndex C => (x.1 : ℤ)) by rfl,
    shiftMultiplicity_sum]

lemma minimalP_shiftMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ) :
    shiftMultiplicity (minimalPShift C) d =
      shiftMultiplicity (minimalIdealShift hA) d +
        shiftMultiplicity (fun x : MinimalResidualPIndex C => (x.1 : ℤ)) d := by
  rw [show minimalPShift C =
      Sum.elim (minimalIdealShift hA)
        (fun x : MinimalResidualPIndex C => (x.1 : ℤ)) by rfl,
    shiftMultiplicity_sum]

lemma minimalResidualQ_shiftMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ)
    (hd : 0 ≤ d ∧ d ≤ (e : ℤ)) :
      shiftMultiplicity (fun x : MinimalResidualQIndex C => (x.1 : ℤ)) d =
      (signedMultiplicity C d).toNat := by
  change shiftMultiplicity (fun x : LowPositiveIndex C => (x.1 : ℤ)) d = _
  have h := shiftMultiplicity_lowPositive C d
  rw [if_pos hd] at h
  exact h

lemma minimalResidualP_shiftMultiplicity
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ)
    (hd : 0 ≤ d ∧ d ≤ (e : ℤ)) :
      shiftMultiplicity (fun x : MinimalResidualPIndex C => (x.1 : ℤ)) d =
      (-signedMultiplicity C d).toNat := by
  change shiftMultiplicity (fun x : LowNegativeIndex C => (x.1 : ℤ)) d = _
  have h := shiftMultiplicity_lowNegative C d
  rw [if_pos hd] at h
  exact h

lemma minimal_shiftSum_difference_eq_signed
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (n : ℕ) (hn : n ≤ e) :
    shiftSum ((e : ℤ) + 3) (shiftMultiplicity (minimalQShift C)) (n : ℤ) -
        shiftSum ((e : ℤ) + 3) (shiftMultiplicity (minimalPShift C)) (n : ℤ) =
      shiftSum ((e : ℤ) + 3) (signedMultiplicity C) (n : ℤ) := by
  have hq : shiftMultiplicity (minimalQShift C) =
      (fun d => shiftMultiplicity (minimalIdealShift hA) d +
        shiftMultiplicity (fun x : MinimalResidualQIndex C => (x.1 : ℤ)) d) := by
    funext d; exact minimalQ_shiftMultiplicity C d
  have hp : shiftMultiplicity (minimalPShift C) =
      (fun d => shiftMultiplicity (minimalIdealShift hA) d +
        shiftMultiplicity (fun x : MinimalResidualPIndex C => (x.1 : ℤ)) d) := by
    funext d; exact minimalP_shiftMultiplicity C d
  rw [hq, hp, shiftSum_add, shiftSum_add]
  unfold shiftSum
  ring_nf
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdi := Finset.mem_Icc.mp hd
  by_cases hdt : d ≤ (n : ℤ)
  · have hr : 0 ≤ d ∧ d ≤ (e : ℤ) := by
      exact ⟨hdi.1, by omega⟩
    rw [minimalResidualQ_shiftMultiplicity C d hr,
      minimalResidualP_shiftMultiplicity C d hr]
    have hsplit :
        ((signedMultiplicity C d).toNat : ℤ) -
            ((-signedMultiplicity C d).toNat : ℤ) =
          signedMultiplicity C d := by
      exact int_toNat_split (signedMultiplicity C d)
    rw [← sub_mul, hsplit]
  · rw [Nz_neg (n - d) (by omega)]
    simp

lemma minimal_shiftSum_difference_eq_finrank
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (n : ℕ) (hn : n ≤ e) :
    shiftSum ((e : ℤ) + 3) (shiftMultiplicity (minimalQShift C)) (n : ℤ) -
        shiftSum ((e : ℤ) + 3) (shiftMultiplicity (minimalPShift C)) (n : ℤ) =
      (finrank k (gradedDualPiece I e n) : ℤ) - 2 * Nz (n : ℤ) := by
  rw [minimal_shiftSum_difference_eq_signed C n hn]
  exact signed_shiftSum_eq_finrank_of_le C n hn

lemma minimal_degreewise_exact
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) :
    ∀ n : ℕ, n ≤ e → Nonempty
      (ExactPresentation k (gradedDualPiece I e n)
        (shiftSum ((e : ℤ) + 3) (shiftMultiplicity (minimalQShift C)) (n : ℤ)).toNat
        (shiftSum ((e : ℤ) + 3) (shiftMultiplicity (minimalPShift C)) (n : ℤ)).toNat
        (2 * Nz (n : ℤ)).toNat) := by
  classical
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  intro n hn
  let qn := shiftSum ((e : ℤ) + 3)
    (shiftMultiplicity (minimalQShift C)) (n : ℤ)
  let pn := shiftSum ((e : ℤ) + 3)
    (shiftMultiplicity (minimalPShift C)) (n : ℤ)
  let mn := 2 * Nz (n : ℤ)
  have hqn : 0 ≤ qn := by
    dsimp [qn]
    exact shiftSum_nonneg _ (fun d => shiftMultiplicity_nonneg _ _) _
  have hpn : 0 ≤ pn := by
    dsimp [pn]
    exact shiftSum_nonneg _ (fun d => shiftMultiplicity_nonneg _ _) _
  have hmn : 0 ≤ mn := by
    dsimp [mn]
    exact mul_nonneg (by norm_num) (Nz_nonneg _)
  have hdiff : qn - pn =
      (finrank k (gradedDualPiece I e n) : ℤ) - mn := by
    dsimp [qn, pn, mn]
    exact minimal_shiftSum_difference_eq_finrank C n hn
  have hqcast : (qn.toNat : ℤ) = qn := Int.toNat_of_nonneg hqn
  have hpcast : (pn.toNat : ℤ) = pn := Int.toNat_of_nonneg hpn
  have hmcast : (mn.toNat : ℤ) = mn := Int.toNat_of_nonneg hmn
  have heZ :
      (finrank k (gradedDualPiece I e n) : ℤ) + (pn.toNat : ℤ) =
        (mn.toNat : ℤ) + (qn.toNat : ℤ) := by
    rw [hpcast, hmcast, hqcast]
    linarith
  have he : finrank k (gradedDualPiece I e n) + pn.toNat =
      mn.toNat + qn.toNat := by exact_mod_cast heZ
  have hmle : finrank k (gradedDualPiece I e n) ≤ mn.toNat :=
    finrank_gradedDualPiece_le_twoNz hA n hn
  have hqle : qn.toNat ≤ pn.toNat := by omega
  exact exactPresentationOfFinrank hmle hqle he

/-! The remaining input to the dual package is the last differential.  The
following record is deliberately stated over the actual minimal complex: it
contains the rank-one localized kernel, the homogeneous coefficient vector,
and the fact that those coefficients generate the original ideal.  The next
bridge theorem consumes precisely this data, so no matrix or degree claim is
hidden in the construction of the package itself. -/

structure LastDifferentialCertificate
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) where
  shift_ge : ∀ a, (e : ℤ) + 3 ≤ (C.rShift a : ℤ)
  circuit : C.β₂ → R3 k
  first_column_ne_zero : ∀ i, C.d₁ (Pi.single i 1) ≠ 0
  circuit_full : ∀ j, circuit j ≠ 0
  circuit_ne_zero : circuit ≠ 0
  circuit_homogeneous : ∀ j,
    MvPolynomial.IsHomogeneous (circuit j)
      (((e : ℤ) + 3 - (C.qShift j : ℤ)).toNat)
  ideal_eq_span : I = Ideal.span (Set.range circuit)
  circuit_dependency : ∑ j, circuit j • C.d₂ (Pi.single j 1) = 0
  kernel_line : ∀ c : C.β₂ → FractionRing (R3 k),
    (∑ j, c j •
      (fun i => algebraMap (R3 k) (FractionRing (R3 k))
        (C.d₂ (Pi.single j 1) i))) = 0 →
      ∃ a : FractionRing (R3 k),
        c = a • (fun j => algebraMap (R3 k)
          (FractionRing (R3 k)) (circuit j))

/-! The genuinely canonical-module part of the last differential is much
smaller than `LastDifferentialCertificate`: the third free module has one
homogeneous basis vector of shift `e+3`, all coordinates of its image are
nonzero, and those coordinates generate `I`.  Exactness of the localized
minimal complex then supplies the dependency and the one-dimensional kernel
automatically. -/

structure CanonicalLastDifferentialData
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) where
  a0 : C.β₃
  unique_a : ∀ a : C.β₃, a = a0
  shift_eq : C.rShift a0 = e + 3
  β₂_nonempty : Nonempty C.β₂
  coordinate_ne_zero : ∀ j, C.d₃ (Pi.single a0 1) j ≠ 0
  ideal_eq_span : I = Ideal.span (Set.range (C.d₃ (Pi.single a0 1)))

namespace CanonicalLastDifferentialData

variable {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}

lemma localized_kernel_line
    (C : GradedMinimalFreeComplex I e hA)
    (L : CanonicalLastDifferentialData C)
    (c : C.β₂ → FractionRing (R3 k))
    (hc : localizedSecondMap C c = 0) :
    ∃ a : FractionRing (R3 k),
      c = a • (fun j => algebraMap (R3 k) (FractionRing (R3 k))
        (C.d₃ (Pi.single L.a0 1) j)) := by
  classical
  have hmem : c ∈ LinearMap.ker (localizedSecondMap C) :=
    LinearMap.mem_ker.mpr hc
  rw [← localizedThirdMap_range_eq_kernel C] at hmem
  obtain ⟨x, hx⟩ := hmem
  let a : FractionRing (R3 k) := x L.a0
  have hx_single : x = a • Pi.single L.a0 1 := by
    funext b
    rw [L.unique_a b]
    simp [a]
  refine ⟨a, ?_⟩
  rw [← hx, hx_single, map_smul]
  have hmap := localizedThirdMap_algebraMap C
    (Pi.single L.a0 (1 : R3 k))
  simpa using hmap

lemma circuit_dependency
    (C : GradedMinimalFreeComplex I e hA)
    (L : CanonicalLastDifferentialData C) :
    ∑ j, C.d₃ (Pi.single L.a0 1) j • C.d₂ (Pi.single j 1) = 0 := by
  classical
  have hsum :
      (∑ j, C.d₃ (Pi.single L.a0 1) j •
        Pi.single j (1 : R3 k)) = C.d₃ (Pi.single L.a0 1) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro l hlj
      have hz :
          (Pi.single l (1 : R3 k) : C.β₂ → R3 k) j = 0 :=
        (Pi.single_eq_of_ne' hlj) 1
      rw [hz, mul_zero]
  have hcomp := congrArg (fun f => f (Pi.single L.a0 1)) C.d₂_d₃
  simp only [LinearMap.comp_apply] at hcomp
  rw [← hsum, map_sum] at hcomp
  simpa only [map_smul, LinearMap.zero_apply] using hcomp

/-- Any element annihilating the resolved module belongs to the order ideal
of a rank-one last syzygy.  The proof constructs the standard chain
null-homotopy of scalar multiplication, using projectivity of the free
modules at each stage.  For the Matlis dual its annihilator is `I`, so this
gives the inclusion `I ⊆ (entries d₃)` without local duality. -/
lemma originalIdeal_le_coordinateIdeal
    (C : GradedMinimalFreeComplex I e hA)
    (a0 : C.β₃) :
    I ≤ Ideal.span (Set.range (C.d₃ (Pi.single a0 1))) := by
  classical
  letI : Fintype C.β₁ := C.fintype₁
  letI : Fintype C.β₂ := C.fintype₂
  letI : Fintype C.β₃ := C.fintype₃
  letI : Module.Free (R3 k) (Fin 2 → R3 k) := by infer_instance
  letI : Module.Free (R3 k) (C.β₁ → R3 k) := by infer_instance
  letI : Module.Free (R3 k) (C.β₂ → R3 k) := by infer_instance
  letI : Module.Projective (R3 k) (Fin 2 → R3 k) := Module.Projective.of_free
  letI : Module.Projective (R3 k) (C.β₁ → R3 k) := Module.Projective.of_free
  letI : Module.Projective (R3 k) (C.β₂ → R3 k) := Module.Projective.of_free
  intro f hfI
  let K₀ := LinearMap.ker (inverseSystemMap hA)
  let K₁ := LinearMap.ker C.d₁
  let K₂ := LinearMap.ker C.d₂
  let d₁K : (C.β₁ → R3 k) →ₗ[R3 k] K₀ :=
    C.d₁.codRestrict K₀ (by
      intro x
      have hx : C.d₁ x ∈ LinearMap.range C.d₁ :=
        LinearMap.mem_range_self C.d₁ x
      rw [C.d₁_range] at hx
      exact hx)
  let d₂K : (C.β₂ → R3 k) →ₗ[R3 k] K₁ :=
    C.d₂.codRestrict K₁ (by
      intro x
      have hx : C.d₂ x ∈ LinearMap.range C.d₂ :=
        LinearMap.mem_range_self C.d₂ x
      rw [C.d₂_range] at hx
      exact hx)
  let d₃K : (C.β₃ → R3 k) →ₗ[R3 k] K₂ :=
    C.d₃.codRestrict K₂ (by
      intro x
      have hx : C.d₃ x ∈ LinearMap.range C.d₃ :=
        LinearMap.mem_range_self C.d₃ x
      rw [C.d₃_range] at hx
      exact hx)
  have hd₁K : Function.Surjective d₁K := by
    intro y
    have hy : (y : Fin 2 → R3 k) ∈ LinearMap.range C.d₁ := by
      rw [C.d₁_range]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  have hd₂K : Function.Surjective d₂K := by
    intro y
    have hy : (y : C.β₁ → R3 k) ∈ LinearMap.range C.d₂ := by
      rw [C.d₂_range]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  have hd₃K : Function.Surjective d₃K := by
    intro y
    have hy : (y : C.β₂ → R3 k) ∈ LinearMap.range C.d₃ := by
      rw [C.d₃_range]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  have hfAnn : f ∈ Module.annihilator (R3 k) (MatlisDual I) := by
    rw [matlisDual_annihilator_eq_original hA]
    exact hfI
  let g₀ : (Fin 2 → R3 k) →ₗ[R3 k] K₀ :=
    (f • LinearMap.id).codRestrict K₀ (by
      intro x
      rw [LinearMap.mem_ker]
      change inverseSystemMap hA (f • x) = 0
      rw [map_smul]
      exact Module.mem_annihilator.mp hfAnn (inverseSystemMap hA x))
  obtain ⟨h₀, hh₀⟩ := Module.projective_lifting_property d₁K g₀ hd₁K
  have hh₀_apply (x : Fin 2 → R3 k) : C.d₁ (h₀ x) = f • x := by
    have hx := DFunLike.congr_fun hh₀ x
    exact congrArg Subtype.val hx
  let z₁ : (C.β₁ → R3 k) →ₗ[R3 k] (C.β₁ → R3 k) :=
    f • LinearMap.id - h₀.comp C.d₁
  let g₁ : (C.β₁ → R3 k) →ₗ[R3 k] K₁ :=
    z₁.codRestrict K₁ (by
      intro x
      rw [LinearMap.mem_ker]
      simp only [z₁, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.comp_apply, map_sub, map_smul,
        hh₀_apply, sub_self])
  obtain ⟨h₁, hh₁⟩ := Module.projective_lifting_property d₂K g₁ hd₂K
  have hh₁_apply (x : C.β₁ → R3 k) :
      C.d₂ (h₁ x) = f • x - h₀ (C.d₁ x) := by
    have hx := congrArg Subtype.val (DFunLike.congr_fun hh₁ x)
    simpa [d₂K, g₁, z₁] using hx
  let z₂ : (C.β₂ → R3 k) →ₗ[R3 k] (C.β₂ → R3 k) :=
    f • LinearMap.id - h₁.comp C.d₂
  let g₂ : (C.β₂ → R3 k) →ₗ[R3 k] K₂ :=
    z₂.codRestrict K₂ (by
      intro x
      rw [LinearMap.mem_ker]
      have hcomp := congrArg (fun q => q x) C.d₁_d₂
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hcomp
      simp only [z₂, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.comp_apply, map_sub, map_smul,
        hh₁_apply, hcomp, map_zero, sub_zero, sub_self])
  obtain ⟨h₂, hh₂⟩ := Module.projective_lifting_property d₃K g₂ hd₃K
  have hh₂_apply (x : C.β₂ → R3 k) :
      C.d₃ (h₂ x) = f • x - h₁ (C.d₂ x) := by
    have hx := congrArg Subtype.val (DFunLike.congr_fun hh₂ x)
    simpa [d₃K, g₂, z₂] using hx
  have htop (x : C.β₃ → R3 k) : f • x = h₂ (C.d₃ x) := by
    apply C.d₃_injective
    have hcomp := congrArg (fun q => q x) C.d₂_d₃
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hcomp
    rw [map_smul, hh₂_apply, hcomp, map_zero, sub_zero]
  let v : C.β₂ → R3 k := C.d₃ (Pi.single a0 1)
  have hvsum : (∑ j, v j • Pi.single j (1 : R3 k)) =
      C.d₃ (Pi.single a0 1) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp [v]
    · intro l hlj
      have hz : (Pi.single l (1 : R3 k) : C.β₂ → R3 k) j = 0 :=
        (Pi.single_eq_of_ne' hlj) 1
      rw [hz, mul_zero]
  have hf_eq : f = ∑ j, (h₂ (Pi.single j 1) a0) * v j := by
    have ht := congrFun (htop (Pi.single a0 1)) a0
    rw [← hvsum, map_sum] at ht
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at ht
    simpa [Pi.single, mul_comm] using ht
  rw [hf_eq]
  apply Ideal.sum_mem
  intro j hj
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))

noncomputable def toLastDifferentialCertificate
    (C : GradedMinimalFreeComplex I e hA)
    (L : CanonicalLastDifferentialData C) :
    LastDifferentialCertificate C := by
  classical
  let circuit : C.β₂ → R3 k := C.d₃ (Pi.single L.a0 1)
  refine
    { shift_ge := ?_
      circuit := circuit
      first_column_ne_zero := C.first_column_ne_zero
      circuit_full := ?_
      circuit_ne_zero := ?_
      circuit_homogeneous := ?_
      ideal_eq_span := ?_
      circuit_dependency := ?_
      kernel_line := ?_ }
  · intro a
    rw [L.unique_a a, L.shift_eq]
    omega
  · intro j
    exact L.coordinate_ne_zero j
  · intro hzero
    obtain ⟨j⟩ := L.β₂_nonempty
    exact L.coordinate_ne_zero j (congrFun hzero j)
  · intro j
    have hle : C.qShift j ≤ C.rShift L.a0 := by
      by_contra hnot
      have hh := C.d₃_homogeneous L.a0 j
      rw [if_neg hnot] at hh
      exact L.coordinate_ne_zero j hh
    have hh := C.d₃_homogeneous L.a0 j
    rw [if_pos hle] at hh
    have hq : C.qShift j ≤ e + 3 := by
      rw [L.shift_eq] at hle
      exact hle
    have hz :
        (e : ℤ) + 3 - (C.qShift j : ℤ) =
          ((e + 3 - C.qShift j : ℕ) : ℤ) := by
      rw [Nat.cast_sub hq]
      push_cast
      ring
    have hdegree :
        C.rShift L.a0 - C.qShift j =
          (((e : ℤ) + 3 - (C.qShift j : ℤ)).toNat) := by
      rw [L.shift_eq, hz, Int.toNat_natCast]
    simpa [circuit, hdegree] using hh
  · simpa [circuit] using L.ideal_eq_span
  · simpa [circuit] using circuit_dependency C L
  · intro c hc
    exact localized_kernel_line C L c (by simpa [localizedSecondMap_apply] using hc)

end CanonicalLastDifferentialData

/-- Expand a vector of the finite free module in its standard basis. -/
lemma single_expansion {β : Type} [Fintype β] (v : β → R3 k) :
    (∑ b, v b • (Pi.single b 1 : β → R3 k)) = v := by
  classical
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro l hlj
    have hz : (Pi.single l (1 : R3 k) : β → R3 k) j = 0 :=
      (Pi.single_eq_of_ne' hlj) 1
    rw [hz, mul_zero]

/-- An `R`-functional sends a vector whose entries lie in the irrelevant ideal
into the irrelevant ideal. -/
lemma dual_apply_mem_irrelevant {β : Type} [Fintype β]
    (ψ : Module.Dual (R3 k) (β → R3 k)) {v : β → R3 k}
    (hv : ∀ b, v b ∈ irrelevantIdeal k) :
    ψ v ∈ irrelevantIdeal k := by
  classical
  rw [← single_expansion v, map_sum]
  refine Ideal.sum_mem _ ?_
  intro b _
  rw [map_smul]
  exact Ideal.mul_mem_right _ _ (hv b)

/-- A nonempty `β₃` forces a nonempty `β₂`: otherwise the third free module
maps injectively into the zero module. -/
lemma beta₂_nonempty_of_beta₃
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (a0 : C.β₃) : Nonempty C.β₂ := by
  by_contra hempty
  have hE : IsEmpty C.β₂ := not_nonempty_iff.mp hempty
  have h0 : (Pi.single a0 (1 : R3 k) : C.β₃ → R3 k) = 0 := by
    apply C.d₃_injective
    have hz : C.d₃ (Pi.single a0 1) = 0 := funext fun g => hE.elim g
    rw [hz, map_zero]
  have h1 := congrFun h0 a0
  simp at h1

/-- With a one-element `β₃`, no coordinate of the last differential vanishes.
A vanishing `j`-th coordinate makes the `j`-th coordinate functional annihilate
the image of `d₃`; exactness of the dualized complex writes it as `ψ ∘ d₂`, and
minimality of `d₂` then places `1` in the irrelevant ideal. -/
lemma lastDifferential_coordinate_ne_zero
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex.{u, 0, 0, 0} I e hA)
    (a0 : C.β₃) (hunique : ∀ a : C.β₃, a = a0) (j : C.β₂) :
    C.d₃ (Pi.single a0 1) j ≠ 0 := by
  classical
  intro hz
  set φ : Module.Dual (R3 k) (C.β₂ → R3 k) := LinearMap.proj j with hφ
  have hφker : φ ∈ LinearMap.ker C.d₃.dualMap := by
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro x
    have hx : x = x a0 • (Pi.single a0 1 : C.β₃ → R3 k) := by
      funext b
      rw [hunique b]
      simp
    have : C.d₃.dualMap φ x = φ (C.d₃ x) := rfl
    rw [this, hx, map_smul, map_smul]
    simp [hφ, hz]
  rw [← dual_d₂_range_eq_kernel_d₃ hA C] at hφker
  obtain ⟨ψ, hψ⟩ := hφker
  have h2 : φ (Pi.single j 1) = ψ (C.d₂ (Pi.single j 1)) := by
    rw [← hψ]; rfl
  have hmem : ψ (C.d₂ (Pi.single j 1)) ∈ irrelevantIdeal k :=
    dual_apply_mem_irrelevant ψ (fun b => C.d₂_minimal j b)
  rw [← h2] at hmem
  have h1 : φ (Pi.single j (1 : R3 k)) = 1 := by simp [hφ]
  rw [h1] at hmem
  exact GradedMinimalFreeComplex.one_not_mem_irrelevantIdeal hmem

/-- Enlarging the cutoff of a `shiftSum` past the evaluation point changes
nothing: the extra terms carry `Nz` of a negative argument. -/
lemma shiftSum_cutoff_mono (f : ℤ → ℤ) {t u u' : ℤ}
    (htu : t ≤ u) (huu' : u ≤ u') :
    shiftSum u' f t = shiftSum u f t := by
  unfold shiftSum
  symm
  apply Finset.sum_subset
  · intro b hb
    rw [Finset.mem_Icc] at hb ⊢
    exact ⟨hb.1, hb.2.trans huu'⟩
  · intro b hb hnot
    have hb' := Finset.mem_Icc.mp hb
    have hbt : t < b := by
      by_contra hle
      exact hnot (Finset.mem_Icc.mpr ⟨hb'.1, by omega⟩)
    rw [Nz_neg _ (by omega), mul_zero]

/-- The third free module carries the shift `e + 3`.  Taking the third
difference of the degreewise Euler identity at `e + 3` isolates the
coefficient of `t ^ (e+3)` in the numerator of the Hilbert series: the
first shifts are all at most `e + 1`, the socle contributes `h₀ = 1`, and
what is left forces some `rShift` to equal `e + 3`. -/
lemma lastShift_eq_of_unique
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    (a0 : C.β₃) (hunique : ∀ a : C.β₃, a = a0) :
    C.rShift a0 = e + 3 := by
  classical
  have hcut : ∀ (f : ℤ → ℤ) (n : ℕ), (n : ℤ) ≤ (e : ℤ) + 3 →
      shiftSum (n : ℤ) f (n : ℤ) = shiftSum ((e : ℤ) + 3) f (n : ℤ) :=
    fun f n hn => (shiftSum_cutoff_mono f (le_refl (n : ℤ)) hn).symm
  have E : ∀ n : ℕ, e < n → (n : ℤ) ≤ (e : ℤ) + 3 →
      shiftSum ((e : ℤ) + 3) C.pMultiplicity (n : ℤ) +
          shiftSum ((e : ℤ) + 3) C.rMultiplicity (n : ℤ) =
        2 * Nz (n : ℤ) + shiftSum ((e : ℤ) + 3) C.qMultiplicity (n : ℤ) := by
    intro n hn hnU
    have h := degreewise_euler_of_minimal_above hA C n hn
    rwa [hcut _ n hnU, hcut _ n hnU, hcut _ n hnU] at h
  have E1 := E (e + 1) (by omega) (by push_cast; omega)
  have E2 := E (e + 2) (by omega) (by push_cast; omega)
  have E3 := E (e + 3) (by omega) (by push_cast; omega)
  have E0 := degreewise_euler_of_minimal hA C e (le_refl e)
  push_cast at E1 E2 E3
  have hfin : (finrank k (gradedDualPiece I e e) : ℤ) = 1 := by
    rw [finrank_gradedDualPiece I e e (le_refl e), reversedHilb, sub_self]
    exact hilb_zero I hA.proper
  rw [hfin] at E0
  -- third differences at `e + 3`
  have hd1 : (e : ℤ) + 3 - 1 = (e : ℤ) + 2 := by ring
  have hd2 : (e : ℤ) + 3 - 2 = (e : ℤ) + 1 := by ring
  have hd3 : (e : ℤ) + 3 - 3 = (e : ℤ) := by ring
  have hp3 := shiftSum_third_diff ((e : ℤ) + 3) C.pMultiplicity ((e : ℤ) + 3)
    (by omega) (le_refl _)
  have hq3 := shiftSum_third_diff ((e : ℤ) + 3) C.qMultiplicity ((e : ℤ) + 3)
    (by omega) (le_refl _)
  have hr3 := shiftSum_third_diff ((e : ℤ) + 3) C.rMultiplicity ((e : ℤ) + 3)
    (by omega) (le_refl _)
  have hNz3 : Nz ((e : ℤ) + 3) - 3 * Nz ((e : ℤ) + 2) +
      3 * Nz ((e : ℤ) + 1) - Nz (e : ℤ) = 0 := by
    have h1 := Nz_second_diff ((e : ℤ) + 3)
    have h2 := Nz_second_diff ((e : ℤ) + 2)
    rw [if_pos (by omega)] at h1
    rw [if_pos (by omega)] at h2
    have e1 : (e : ℤ) + 3 - 1 = (e : ℤ) + 2 := by ring
    have e2 : (e : ℤ) + 3 - 2 = (e : ℤ) + 1 := by ring
    have e3 : (e : ℤ) + 2 - 1 = (e : ℤ) + 1 := by ring
    have e4 : (e : ℤ) + 2 - 2 = (e : ℤ) := by ring
    rw [e1, e2] at h1
    rw [e3, e4] at h2
    linarith
  rw [hd1, hd2, hd3] at hp3 hq3 hr3
  -- the coefficient identity at degree `e + 3`
  have hkey : C.rMultiplicity ((e : ℤ) + 3) =
      C.qMultiplicity ((e : ℤ) + 3) + 1 - C.pMultiplicity ((e : ℤ) + 3) := by
    rw [← hp3, ← hq3, ← hr3]
    linarith [E0, E1, E2, E3, hNz3]
  have hp0 : C.pMultiplicity ((e : ℤ) + 3) = 0 := by
    letI := C.fintype₁
    have : (Finset.univ.filter fun b => (C.pShift b : ℤ) = (e : ℤ) + 3) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro b _ hb
      have := first_shift_le hA C b
      omega
    simp [GradedMinimalFreeComplex.pMultiplicity, shiftMultiplicity, this]
  have hqnn : 0 ≤ C.qMultiplicity ((e : ℤ) + 3) :=
    C.qMultiplicity_nonneg _
  have hrpos : 0 < C.rMultiplicity ((e : ℤ) + 3) := by
    rw [hkey, hp0]; omega
  -- a positive multiplicity produces an index with that shift
  letI := C.fintype₃
  have hne : (Finset.univ.filter
      fun a => (C.rShift a : ℤ) = (e : ℤ) + 3).Nonempty := by
    rw [← Finset.card_pos]
    have h := hrpos
    simp only [GradedMinimalFreeComplex.rMultiplicity, shiftMultiplicity] at h
    exact_mod_cast h
  obtain ⟨a, ha⟩ := hne
  have ha' : (C.rShift a : ℤ) = (e : ℤ) + 3 :=
    (Finset.mem_filter.mp ha).2
  rw [hunique a] at ha'
  omega

/-- A nonzero element of the ideal: any variable power past the socle degree
lies in `I`. -/
lemma exists_ne_zero_mem
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    ∃ a : R3 k, a ≠ 0 ∧ a ∈ I := by
  refine ⟨(MvPolynomial.X (0 : Fin 3) : R3 k) ^ (e + 1), ?_, ?_⟩
  · exact pow_ne_zero _ (MvPolynomial.X_ne_zero _)
  · exact homogeneous_mem_ideal_of_vanish_above hA (n := e + 1) (by omega)
      (MvPolynomial.isHomogeneous_X_pow (0 : Fin 3) (e + 1))

/-- The dual of the first differential is injective: a functional killing
`range d₁` kills every vector, because the Matlis dual is torsion and the
polynomial ring is a domain. -/
lemma dual_d₁_injective
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA) :
    Function.Injective C.d₁.dualMap := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro c hc
  have hc' : ∀ w, c (C.d₁ w) = 0 := by
    intro w
    have := LinearMap.mem_ker.mp hc
    exact congrFun (congrArg DFunLike.coe this) w
  obtain ⟨a, ha0, haI⟩ := exists_ne_zero_mem hA
  apply LinearMap.ext
  intro u
  have hmem : a • u ∈ LinearMap.range C.d₁ := by
    rw [C.d₁_range, LinearMap.mem_ker, map_smul]
    have := (matlisDual_annihilator_eq_original hA) ▸ haI
    exact Module.mem_annihilator.mp this (inverseSystemMap hA u)
  obtain ⟨w, hw⟩ := hmem
  have hcu : a * c u = 0 := by
    have : c (a • u) = 0 := by rw [← hw]; exact hc' w
    simpa [smul_eq_mul] using this
  have := mul_eq_zero.mp hcu
  simpa [ha0] using this

/-- The entries of the last differential annihilate the Matlis dual, hence lie
in `I`.  The projective null-homotopy of multiplication by an entry is built on
the *dualized* complex — which is exact by `dual_d₁_range_eq_kernel_d₂` and
`dual_d₂_range_eq_kernel_d₃` — and then dualized back, where reflexivity of the
finite free modules turns it into a factorization through `d₁`. -/
lemma coordinateIdeal_le_originalIdeal
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex.{u, 0, 0, 0} I e hA)
    (a0 : C.β₃) (hunique : ∀ a : C.β₃, a = a0) :
    Ideal.span (Set.range (C.d₃ (Pi.single a0 1))) ≤ I := by
  classical
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  set f : R3 k := C.d₃ (Pi.single a0 1) j with hf
  -- projectivity of the duals
  letI : Module.Projective (R3 k) (Module.Dual (R3 k) (C.β₂ → R3 k)) :=
    Module.Projective.of_free
  letI : Module.Projective (R3 k) (Module.Dual (R3 k) (C.β₁ → R3 k)) :=
    Module.Projective.of_free
  letI : Module.Projective (R3 k) (Module.Dual (R3 k) (Fin 2 → R3 k)) :=
    Module.Projective.of_free
  set td1 := C.d₃.dualMap with htd1
  set td2 := C.d₂.dualMap with htd2
  set td3 := C.d₁.dualMap with htd3
  have hex12 : LinearMap.range td2 = LinearMap.ker td1 := by
    rw [htd2, htd1]; exact dual_d₂_range_eq_kernel_d₃ hA C
  have hex23 : LinearMap.range td3 = LinearMap.ker td2 := by
    rw [htd3, htd2]; exact dual_d₁_range_eq_kernel_d₂ hA C
  -- every vector of the third free module is a multiple of the basis vector
  have hev : ∀ (χ : Module.Dual (R3 k) (C.β₃ → R3 k)) (y : C.β₃ → R3 k),
      χ y = y a0 * χ (Pi.single a0 1) := by
    intro χ y
    have hy : y = y a0 • (Pi.single a0 1 : C.β₃ → R3 k) := by
      funext b
      rw [hunique b]
      simp
    conv_lhs => rw [hy]
    rw [map_smul, smul_eq_mul]
  have hd3v : ∀ y : C.β₃ → R3 k,
      C.d₃ y = y a0 • C.d₃ (Pi.single a0 1) := by
    intro y
    have hy : y = y a0 • (Pi.single a0 1 : C.β₃ → R3 k) := by
      funext b
      rw [hunique b]
      simp
    conv_lhs => rw [hy]
    rw [map_smul]
  -- `f` times any functional on the third free module is in the image of `td1`
  set φ : Module.Dual (R3 k) (C.β₂ → R3 k) := LinearMap.proj j with hφ
  have hstart : ∀ ψ : Module.Dual (R3 k) (C.β₃ → R3 k),
      f • ψ = td1 (ψ (Pi.single a0 1) • φ) := by
    intro ψ
    apply LinearMap.ext
    intro x
    have hl : (f • ψ) x = f * (x a0 * ψ (Pi.single a0 1)) := by
      simp only [LinearMap.smul_apply, smul_eq_mul, hev ψ x]
    have hr : td1 (ψ (Pi.single a0 1) • φ) x =
        ψ (Pi.single a0 1) * (x a0 * f) := by
      have hstep : td1 (ψ (Pi.single a0 1) • φ) x =
          (ψ (Pi.single a0 1) • φ) (C.d₃ x) := by rw [htd1]; rfl
      rw [hstep, hd3v x]
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, hφ,
        LinearMap.proj_apply]
      rw [hf]; ring
    rw [hl, hr]; ring
  -- the three lifting steps
  set K₀ : Submodule (R3 k) (Module.Dual (R3 k) (C.β₃ → R3 k)) :=
    LinearMap.range td1 with hK₀
  set K₁ : Submodule (R3 k) (Module.Dual (R3 k) (C.β₂ → R3 k)) :=
    LinearMap.ker td1 with hK₁
  set K₂ : Submodule (R3 k) (Module.Dual (R3 k) (C.β₁ → R3 k)) :=
    LinearMap.ker td2 with hK₂
  let td1K := td1.codRestrict K₀ (fun x => LinearMap.mem_range_self _ x)
  let td2K := td2.codRestrict K₁ (fun x => by
    rw [← hex12]; exact LinearMap.mem_range_self _ x)
  let td3K := td3.codRestrict K₂ (fun x => by
    rw [← hex23]; exact LinearMap.mem_range_self _ x)
  have hs₁ : Function.Surjective td1K := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hs₂ : Function.Surjective td2K := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ LinearMap.range td2 := by rw [hex12]; exact hy
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, Subtype.ext hx⟩
  have hs₃ : Function.Surjective td3K := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ LinearMap.range td3 := by rw [hex23]; exact hy
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, Subtype.ext hx⟩
  let g₀ : Module.Dual (R3 k) (C.β₃ → R3 k) →ₗ[R3 k] K₀ :=
    (f • LinearMap.id).codRestrict K₀ (by
      intro ψ
      rw [hK₀]
      exact ⟨ψ (Pi.single a0 1) • φ, (hstart ψ).symm⟩)
  obtain ⟨h₀, hh₀⟩ := Module.projective_lifting_property td1K g₀ hs₁
  have hh₀' : ∀ ψ, td1 (h₀ ψ) = f • ψ := by
    intro ψ
    exact congrArg Subtype.val (DFunLike.congr_fun hh₀ ψ)
  let z₁ := f • (LinearMap.id : Module.Dual (R3 k) (C.β₂ → R3 k) →ₗ[R3 k] _) -
    h₀.comp td1
  let g₁ : Module.Dual (R3 k) (C.β₂ → R3 k) →ₗ[R3 k] K₁ :=
    z₁.codRestrict K₁ (by
      intro x
      rw [hK₁, LinearMap.mem_ker]
      simp only [z₁, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.comp_apply, map_sub, map_smul,
        hh₀', sub_self])
  obtain ⟨h₁, hh₁⟩ := Module.projective_lifting_property td2K g₁ hs₂
  have hh₁' : ∀ x, td2 (h₁ x) = f • x - h₀ (td1 x) := by
    intro x
    have hx := congrArg Subtype.val (DFunLike.congr_fun hh₁ x)
    simpa [td2K, g₁, z₁] using hx
  let z₂ := f • (LinearMap.id : Module.Dual (R3 k) (C.β₁ → R3 k) →ₗ[R3 k] _) -
    h₁.comp td2
  have htd12 : td1.comp td2 = 0 := by
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro x
    have hz := congrArg (fun q => q x) C.d₂_d₃
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    show c (C.d₂ (C.d₃ x)) = 0
    rw [hz, map_zero]
  have htd12' : ∀ x, td1 (td2 x) = 0 := by
    intro x
    have := congrArg (fun q => q x) htd12
    simpa using this
  have htd23 : td2.comp td3 = 0 := by
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro x
    have hz := congrArg (fun q => q x) C.d₁_d₂
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    show c (C.d₁ (C.d₂ x)) = 0
    rw [hz, map_zero]
  let g₂ : Module.Dual (R3 k) (C.β₁ → R3 k) →ₗ[R3 k] K₂ :=
    z₂.codRestrict K₂ (by
      intro x
      rw [hK₂, LinearMap.mem_ker]
      simp only [z₂, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.comp_apply, map_sub, map_smul,
        hh₁', htd12', map_zero, sub_zero, sub_self])
  obtain ⟨h₂, hh₂⟩ := Module.projective_lifting_property td3K g₂ hs₃
  have hh₂' : ∀ x, td3 (h₂ x) = f • x - h₁ (td2 x) := by
    intro x
    have hx := congrArg Subtype.val (DFunLike.congr_fun hh₂ x)
    simpa [td3K, g₂, z₂] using hx
  -- the top relation, using injectivity of `td3`
  have htop : ∀ x, f • x = h₂ (td3 x) := by
    intro x
    apply dual_d₁_injective hA C
    have hcomp : td2 (td3 x) = 0 := by
      have := congrArg (fun q => q x) htd23
      simpa using this
    show td3 (f • x) = td3 (h₂ (td3 x))
    rw [map_smul, hh₂', hcomp, map_zero, sub_zero]
  -- dualize back
  rw [← matlisDual_annihilator_eq_original hA]
  apply Module.mem_annihilator.mpr
  intro Φ
  obtain ⟨u, rfl⟩ := inverseSystemMap_surjective hA Φ
  rw [← map_smul]
  have hmem : f • u ∈ LinearMap.range C.d₁ := by
    -- apply `dualMap` to `f • id = h₂ ∘ td3` and evaluate on `eval u`
    have hdual : (f • (LinearMap.id :
        Module.Dual (R3 k) (Fin 2 → R3 k) →ₗ[R3 k] _)) = h₂.comp td3 := by
      apply LinearMap.ext
      intro x
      simpa using htop x
    have hstep := congrArg
      (fun q : Module.Dual (R3 k) (Fin 2 → R3 k) →ₗ[R3 k]
          Module.Dual (R3 k) (Fin 2 → R3 k) => q.dualMap) hdual
    rw [← LinearMap.dualMap_comp_dualMap] at hstep
    have hL : (f • (LinearMap.id : Module.Dual (R3 k) (Fin 2 → R3 k) →ₗ[R3 k] _)
        ).dualMap (Module.Dual.eval (R3 k) (Fin 2 → R3 k) u) =
        Module.Dual.eval (R3 k) (Fin 2 → R3 k) (f • u) := by
      apply LinearMap.ext
      intro c
      simp only [LinearMap.dualMap_apply, Module.Dual.eval_apply,
        LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_eq_mul]
    have hR := congrArg (fun q => q (Module.Dual.eval (R3 k) (Fin 2 → R3 k) u))
      hstep
    simp only [LinearMap.comp_apply] at hR
    have hR' : Module.Dual.eval (R3 k) (Fin 2 → R3 k) (f • u) =
        C.d₁.dualMap.dualMap (h₂.dualMap
          (Module.Dual.eval (R3 k) (Fin 2 → R3 k) u)) := by
      rw [← hL, hR, htd3]
    obtain ⟨w, hw⟩ := (Module.bijective_dual_eval (R3 k)
      (C.β₁ → R3 k)).surjective (h₂.dualMap
        (Module.Dual.eval (R3 k) (Fin 2 → R3 k) u))
    refine ⟨w, ?_⟩
    apply (Module.bijective_dual_eval (R3 k) (Fin 2 → R3 k)).injective
    have hnat : C.d₁.dualMap.dualMap
        (Module.Dual.eval (R3 k) (C.β₁ → R3 k) w) =
        Module.Dual.eval (R3 k) (Fin 2 → R3 k) (C.d₁ w) := rfl
    rw [← hnat, hw, ← hR']
  obtain ⟨w, hw⟩ := hmem
  rw [← hw]
  have hmem' : C.d₁ w ∈ LinearMap.range C.d₁ := LinearMap.mem_range_self _ w
  rw [C.d₁_range, LinearMap.mem_ker] at hmem'
  exact hmem'

/-! ## The last-differential record from the last Betti number alone

Everything in `CanonicalLastDifferentialData` except the rank of the third
free module is now derived.  The remaining input is the single homological
statement `Fintype.card C.β₃ = 1`, i.e. that the Matlis dual has last Betti
number one. -/

noncomputable def CanonicalLastDifferentialData.ofCardBeta₃
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex.{u, 0, 0, 0} I e hA)
    (hcard : Fintype.card C.β₃ = 1) :
    CanonicalLastDifferentialData C := by
  classical
  -- `Exists` cannot be destructured into data, so pick the unique index
  let a0 : C.β₃ := (Fintype.card_eq_one_iff.mp hcard).choose
  have hunique : ∀ a : C.β₃, a = a0 :=
    (Fintype.card_eq_one_iff.mp hcard).choose_spec
  refine
    { a0 := a0
      unique_a := hunique
      shift_eq := lastShift_eq_of_unique hA C a0 hunique
      β₂_nonempty := beta₂_nonempty_of_beta₃ C a0
      coordinate_ne_zero :=
        lastDifferential_coordinate_ne_zero hA C a0 hunique
      ideal_eq_span := ?_ }
  apply le_antisymm
  · exact originalIdeal_le_coordinateIdeal C a0
  · exact coordinateIdeal_le_originalIdeal hA C a0 hunique

lemma d₂_entry_zero_of_shift_le
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    (j : C.β₂) (i : C.β₁)
    (hji : (C.qShift j : ℤ) ≤ (C.pShift i : ℤ)) :
    C.d₂ (Pi.single j 1) i = 0 := by
  by_cases hle : C.pShift i ≤ C.qShift j
  · have heq : C.pShift i = C.qShift j := by omega
    have hh := C.d₂_homogeneous j i
    rw [if_pos hle, heq] at hh
    have hmem := C.d₂_minimal j i
    apply isHomogeneous_eq_zero_of_mem_succ_pow_idealOfVars hh
    simpa [irrelevantIdeal, pow_one] using hmem
  · have hh := C.d₂_homogeneous j i
    rw [if_neg hle] at hh
    exact hh

noncomputable def GradedResolutionDuality.ofMinimalLast
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    (L : LastDifferentialCertificate C) :
    GradedResolutionDuality I e C.β₁ C.β₂ := by
  classical
  let pShift : C.β₁ → ℤ := fun i => C.pShift i
  let qShift : C.β₂ → ℤ := fun j => C.qShift j
  let δ₁ : C.β₁ → Fin 2 → R3 k := fun i => C.d₁ (Pi.single i 1)
  let δ₂K : C.β₂ → C.β₁ → FractionRing (R3 k) := fun j i =>
    algebraMap (R3 k) (FractionRing (R3 k))
      (C.d₂ (Pi.single j 1) i)
  let circuit : C.β₂ → FractionRing (R3 k) := fun j =>
    algebraMap (R3 k) (FractionRing (R3 k)) (L.circuit j)
  refine
    { pShift := pShift
      qShift := qShift
      pShift_nonneg := ?_
      qShift_nonneg := ?_
      degreewise_exact := ?_
      δ₁ := δ₁
      δ₁_ne_zero := ?_
      δ₁_homogeneous := ?_
      δ₂K := δ₂K
      δ₂_graded_zero := ?_
      δ₁δ₂ := ?_
      circuit := circuit
      circuit_full := ?_
      circuit_ne_zero := ?_
      circuit_dependency := ?_
      kernel_line := ?_
      idealGenerator := L.circuit
      idealGenerator_homogeneous := ?_
      ideal_eq_span_generators := L.ideal_eq_span
      circuit_eq_generator := ?_ }
  · intro i
    exact Int.natCast_nonneg _
  · intro j
    exact Int.natCast_nonneg _
  · intro n hn
    simpa [pShift, qShift, GradedMinimalFreeComplex.pMultiplicity,
      GradedMinimalFreeComplex.qMultiplicity] using
      degreewise_exact_of_minimal hA C L.shift_ge n hn
  · intro i hzero
    apply L.first_column_ne_zero i
    simpa [δ₁] using hzero
  · intro i z
    have hh := C.d₁_homogeneous i z
    simpa [δ₁, pShift] using hh
  · intro j i hji
    simpa [δ₂K] using d₂_entry_zero_of_shift_le hA C j i hji
  · intro j
    apply _root_.funext
    intro z
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    have hcomp := congrArg
      (fun f => algebraMap (R3 k) (FractionRing (R3 k))
        ((f (Pi.single j 1)) z)) C.d₁_d₂
    have hsum :
        (∑ i, C.d₂ (Pi.single j 1) i • Pi.single i 1) =
          C.d₂ (Pi.single j 1) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fintype.sum_eq_single i]
      · simp
      · intro l hli
        simp [hli]
    simp only [LinearMap.comp_apply] at hcomp
    rw [← hsum, map_sum] at hcomp
    simp only [map_smul] at hcomp
    simpa [δ₁, δ₂K, LinearMap.comp_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hcomp
  · intro j
    intro hzero
    apply L.circuit_full j
    apply IsFractionRing.injective (R3 k) (FractionRing (R3 k))
    simpa [circuit] using hzero
  · intro hzero
    apply L.circuit_ne_zero
    apply _root_.funext
    intro j
    apply IsFractionRing.injective (R3 k) (FractionRing (R3 k))
    have hj := congrFun hzero j
    simpa [circuit] using hj
  · apply _root_.funext
    intro i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    have h := congrFun L.circuit_dependency i
    have hmap := congrArg
      (fun f => algebraMap (R3 k) (FractionRing (R3 k)) f) h
    simpa [δ₂K, circuit, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply] using hmap
  · intro c hc
    exact L.kernel_line c (by simpa [δ₂K] using hc)
  · intro j
    have hh := L.circuit_homogeneous j
    simpa [qShift] using hh
  · intro j
    rfl

/-- The duality package constructed from the irreducible canonical-module
input.  All localized exactness and kernel-line bookkeeping is discharged by
`CanonicalLastDifferentialData.toLastDifferentialCertificate`. -/
noncomputable def GradedResolutionDuality.ofCanonicalLast
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    (L : CanonicalLastDifferentialData C) :
    GradedResolutionDuality I e C.β₁ C.β₂ :=
  GradedResolutionDuality.ofMinimalLast hA C
    (L.toLastDifferentialCertificate C)

/-! Once the primitive homogeneous line and its coefficient/annihilator
ideals have been identified, the remaining fields of
`CriticalBranchCertificate` are formal consequences of the actual graded
kernel pieces.  In particular, callers do not need to manufacture a second
set of degreewise presentations: `minimalKernelPiece_surjectivePresentation`
already supplies them from the minimal complex. -/

/-- Every nonzero polynomial pair admits a common-factor times primitive-pair
factorization.  Mathlib proves that multivariate polynomial rings over a
field are UFDs; choosing the induced gcd structure turns the paper's
"divide a column by the gcd of its entries" step into an actual construction.

The separate assertion that the chosen primitive pair can be taken
homogeneous is intentionally not folded into this lemma: that is the graded
factor theorem still needed when this construction is applied to a
homogeneous low-shift column. -/
lemma r3_primitive_pair_factorization (f : Fin 2 → R3 k) (hf : f ≠ 0) :
    ∃ (c : R3 k) (v : Fin 2 → R3 k),
      (∀ i, f i = c * v i) ∧ IsRelPrime (v 0) (v 1) := by
  classical
  letI : GCDMonoid (R3 k) :=
    UniqueFactorizationMonoid.toGCDMonoid (R3 k)
  let c := gcd (f 0) (f 1)
  obtain ⟨v0, hv0⟩ :=
    exists_eq_mul_left_of_dvd (gcd_dvd_left (f 0) (f 1))
  obtain ⟨v1, hv1⟩ :=
    exists_eq_mul_left_of_dvd (gcd_dvd_right (f 0) (f 1))
  let v : Fin 2 → R3 k := ![v0, v1]
  have hc : c ≠ 0 := by
    intro hc
    change gcd (f 0) (f 1) = 0 at hc
    have h0 : f 0 = 0 := by rw [hv0, hc, mul_zero]
    have h1 : f 1 = 0 := by rw [hv1, hc, mul_zero]
    apply hf
    funext i
    fin_cases i <;> assumption
  refine ⟨c, v, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [c, v, mul_comm] using hv0
    · simpa [c, v, mul_comm] using hv1
  · intro z hz0 hz1
    obtain ⟨w0, hw0⟩ := hz0
    obtain ⟨w1, hw1⟩ := hz1
    have hzf0 : z * c ∣ f 0 := by
      refine ⟨w0, ?_⟩
      rw [hv0]
      simp [v] at hw0
      rw [hw0]
      ring
    have hzf1 : z * c ∣ f 1 := by
      refine ⟨w1, ?_⟩
      rw [hv1]
      simp [v] at hw1
      rw [hw1]
      ring
    obtain ⟨u, hu⟩ := dvd_gcd hzf0 hzf1
    have hu' : c = z * c * u := hu
    have hzu : z * u = 1 := by
      apply mul_right_cancel₀ hc
      calc
        z * u * c = z * c * u := by ring
        _ = c := hu'.symm
        _ = 1 * c := by rw [one_mul]
    exact isUnit_iff_exists_inv.mpr ⟨u, hzu⟩

/-! A grading parameter detects homogeneous factors.

`degreeScaleHom p` is the substitution `p(x) ↦ p(Tx)`, with coefficients
still living in `R3 k`.  Its coefficient of `T^n` is the homogeneous
degree-`n` component of `p`.  If a product is homogeneous, its image is a
single monomial in `T`; additivity of both leading and trailing degrees then
forces the two factors themselves to be monomials in `T`.  This supplies the
homogeneous-gcd fact absent from Mathlib's API. -/

noncomputable def degreeScaleHom : R3 k →+* Polynomial (R3 k) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp (MvPolynomial.C : k →+* R3 k))
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)

lemma degreeScaleHom_monomial (d : Fin 3 →₀ ℕ) (r : k) :
    degreeScaleHom (MvPolynomial.monomial d r) =
      Polynomial.C (MvPolynomial.monomial d r) * Polynomial.X ^ d.degree := by
  rw [degreeScaleHom, MvPolynomial.eval₂Hom_monomial]
  simp only [RingHom.coe_comp, Function.comp_apply, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib]
  have hC : (∏ x ∈ d.support,
      Polynomial.C (MvPolynomial.X x : R3 k) ^ d x) =
      Polynomial.C (∏ x ∈ d.support, (MvPolynomial.X x : R3 k) ^ d x) := by
    simp only [← map_pow, ← map_prod]
  have hmon : MvPolynomial.C r *
      (∏ x ∈ d.support, (MvPolynomial.X x : R3 k) ^ d x) =
      MvPolynomial.monomial d r := by
    simpa only [Finsupp.prod] using
      (MvPolynomial.monomial_eq (s := d) (a := r)).symm
  have hX : (∏ x ∈ d.support, (Polynomial.X : Polynomial (R3 k)) ^ d x) =
      Polynomial.X ^ d.degree := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hC, ← mul_assoc, ← Polynomial.C_mul, hmon, hX]

lemma coeff_degreeScaleHom (p : R3 k) (n : ℕ) :
    (degreeScaleHom p).coeff n = MvPolynomial.homogeneousComponent n p := by
  calc
    (degreeScaleHom p).coeff n =
        (degreeScaleHom (∑ d ∈ p.support,
          MvPolynomial.monomial d (MvPolynomial.coeff d p))).coeff n := by
            apply congrArg (fun q : Polynomial (R3 k) => q.coeff n)
            exact congrArg degreeScaleHom (MvPolynomial.as_sum p)
    _ = ∑ d ∈ p.support, if d.degree = n then
          MvPolynomial.monomial d (MvPolynomial.coeff d p) else 0 := by
      rw [map_sum degreeScaleHom]
      have hcoeff (s : Finset (Fin 3 →₀ ℕ))
          (q : (Fin 3 →₀ ℕ) → Polynomial (R3 k)) :
          (∑ d ∈ s, q d).coeff n = ∑ d ∈ s, (q d).coeff n := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert d s hd ih => simp [hd, ih, Polynomial.coeff_add]
      rw [hcoeff]
      apply Finset.sum_congr rfl
      intro d hd
      rw [degreeScaleHom_monomial,
        Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
    _ = MvPolynomial.homogeneousComponent n p := by
      rw [MvPolynomial.homogeneousComponent_apply, Finset.sum_filter]

lemma eval_one_degreeScaleHom (p : R3 k) :
    Polynomial.eval 1 (degreeScaleHom p) = p := by
  let F : R3 k →+* R3 k :=
    (Polynomial.evalRingHom (1 : R3 k)).comp degreeScaleHom
  have hF : F = RingHom.id (R3 k) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [F, degreeScaleHom]
    · intro i
      simp [F, degreeScaleHom]
  exact congrArg (fun g : R3 k →+* R3 k => g p) hF

lemma degreeScaleHom_injective : Function.Injective (degreeScaleHom (k := k)) := by
  intro p q hpq
  have h := congrArg (Polynomial.eval (1 : R3 k)) hpq
  simpa [eval_one_degreeScaleHom] using h

lemma degreeScaleHom_eq_C_mul_X_pow_iff (p : R3 k) (n : ℕ) :
    degreeScaleHom p = Polynomial.C p * Polynomial.X ^ n ↔
      MvPolynomial.IsHomogeneous p n := by
  constructor
  · intro h
    have hn := congrArg (fun q : Polynomial (R3 k) => q.coeff n) h
    rw [coeff_degreeScaleHom,
      Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, if_pos rfl] at hn
    rw [← hn]
    exact MvPolynomial.homogeneousComponent_isHomogeneous n p
  · intro hp
    ext m
    rw [coeff_degreeScaleHom, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.coeff_monomial]
    have hm := MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.mem_homogeneousSubmodule n p).mpr hp) (m := m)
    rw [hm]
    by_cases hmn : m = n
    · subst m
      simp
    · have hnm : n ≠ m := Ne.symm hmn
      simp [hmn, hnm]

lemma polynomial_eq_C_mul_X_pow_of_trailing_eq_degree
    {R : Type*} [CommRing R] {p : Polynomial R} (_hp : p ≠ 0)
    (h : p.natTrailingDegree = p.natDegree) :
    p = Polynomial.C (p.coeff p.natDegree) * Polynomial.X ^ p.natDegree := by
  ext n
  rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  by_cases hn : p.natDegree = n
  · simp [hn]
  · rw [if_neg hn]
    by_cases hlt : n < p.natDegree
    · apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      simpa [h] using hlt
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega

lemma homogeneous_factors_of_mul_eq
    {c v f : R3 k} {n : ℕ} (hc : c ≠ 0) (hv : v ≠ 0)
    (hmul : c * v = f) (hf : MvPolynomial.IsHomogeneous f n) :
    ∃ a b : ℕ, a + b = n ∧
      MvPolynomial.IsHomogeneous c a ∧ MvPolynomial.IsHomogeneous v b := by
  let Cc := degreeScaleHom c
  let Cv := degreeScaleHom v
  have hCc : Cc ≠ 0 := by
    intro hzero
    exact hc (degreeScaleHom_injective (by simpa [Cc] using hzero))
  have hCv : Cv ≠ 0 := by
    intro hzero
    exact hv (degreeScaleHom_injective (by simpa [Cv] using hzero))
  have hfscale : degreeScaleHom f =
      Polynomial.C f * Polynomial.X ^ n :=
    (degreeScaleHom_eq_C_mul_X_pow_iff f n).mpr hf
  have hprod : Cc * Cv = Polynomial.C f * Polynomial.X ^ n := by
    calc
      Cc * Cv = degreeScaleHom (c * v) := by simp [Cc, Cv]
      _ = degreeScaleHom f := by rw [hmul]
      _ = Polynomial.C f * Polynomial.X ^ n := hfscale
  have hf0 : f ≠ 0 := by
    rw [← hmul]
    exact mul_ne_zero hc hv
  have hdeg : Cc.natDegree + Cv.natDegree = n := by
    rw [← Polynomial.natDegree_mul hCc hCv, hprod,
      Polynomial.natDegree_C_mul_X_pow n f hf0]
  have htrail_rhs :
      (Polynomial.C f * Polynomial.X ^ n).natTrailingDegree = n := by
    rw [Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.natTrailingDegree_monomial hf0]
  have htrail : Cc.natTrailingDegree + Cv.natTrailingDegree = n := by
    rw [← Polynomial.natTrailingDegree_mul hCc hCv, hprod, htrail_rhs]
  have hCcEq : Cc.natTrailingDegree = Cc.natDegree := by
    have hcLe := Polynomial.natTrailingDegree_le_natDegree Cc
    have hvLe := Polynomial.natTrailingDegree_le_natDegree Cv
    omega
  have hCvEq : Cv.natTrailingDegree = Cv.natDegree := by
    have hcLe := Polynomial.natTrailingDegree_le_natDegree Cc
    have hvLe := Polynomial.natTrailingDegree_le_natDegree Cv
    omega
  have hCcMono := polynomial_eq_C_mul_X_pow_of_trailing_eq_degree hCc hCcEq
  have hCvMono := polynomial_eq_C_mul_X_pow_of_trailing_eq_degree hCv hCvEq
  have hCcCoeff : Cc.coeff Cc.natDegree = c := by
    have heval := congrArg (Polynomial.eval (1 : R3 k)) hCcMono
    simpa [Cc, eval_one_degreeScaleHom] using heval.symm
  have hCvCoeff : Cv.coeff Cv.natDegree = v := by
    have heval := congrArg (Polynomial.eval (1 : R3 k)) hCvMono
    simpa [Cv, eval_one_degreeScaleHom] using heval.symm
  refine ⟨Cc.natDegree, Cv.natDegree, hdeg, ?_, ?_⟩
  · apply (degreeScaleHom_eq_C_mul_X_pow_iff c Cc.natDegree).mp
    simpa [Cc, hCcCoeff] using hCcMono
  · apply (degreeScaleHom_eq_C_mul_X_pow_iff v Cv.natDegree).mp
    simpa [Cv, hCvCoeff] using hCvMono

lemma homogeneous_primitive_pair_factorization
    (f : Fin 2 → R3 k) (n : ℕ) (hf : f ≠ 0)
    (hhom : ∀ z, MvPolynomial.IsHomogeneous (f z) n) :
    ∃ (a : ℕ) (c : R3 k) (v : Fin 2 → R3 k),
      a ≤ n ∧ (∀ z, f z = c * v z) ∧ IsRelPrime (v 0) (v 1) ∧
      MvPolynomial.IsHomogeneous c (n - a) ∧
      ∀ z, MvPolynomial.IsHomogeneous (v z) a := by
  obtain ⟨c, v, hfactor, hprim⟩ := r3_primitive_pair_factorization f hf
  have hc : c ≠ 0 := by
    intro hc
    apply hf
    apply _root_.funext
    intro z
    change f z = (0 : R3 k)
    rw [hfactor z, hc, zero_mul]
  obtain ⟨z, hfz⟩ : ∃ z, f z ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  have hvz : v z ≠ 0 := by
    intro hvz
    exact hfz (by rw [hfactor z, hvz, mul_zero])
  obtain ⟨b, a, hba, hcb, hva⟩ :=
    homogeneous_factors_of_mul_eq hc hvz (hfactor z).symm (hhom z)
  have han : a ≤ n := by omega
  have hbn : n - a = b := by omega
  refine ⟨a, c, v, han, hfactor, hprim, ?_, ?_⟩
  · simpa [hbn] using hcb
  · intro w
    by_cases hvw : v w = 0
    · rw [hvw]
      exact MvPolynomial.isHomogeneous_zero (Fin 3) k a
    · obtain ⟨b', a', hba', hcb', hva'⟩ :=
        homogeneous_factors_of_mul_eq hc hvw (hfactor w).symm (hhom w)
      have hbb : b = b' := hcb.inj_right hcb' hc
      have haa : a = a' := by omega
      simpa [haa] using hva'

/-- In the rank-one branch, all polynomial columns of shift below `d` lie
on one primitive `R3 k`-line.  The rank hypothesis first puts the localized
columns on a one-dimensional line over the fraction field.  Dividing one
nonzero column by the gcd of its entries and applying
`primitive_line_saturated_fraction` then descends every coefficient from the
fraction field back to the polynomial ring. -/
lemma rank_one_low_columns_primitive_line
    {I : Ideal (R3 k)} {e : ℕ}
    {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ)
    (hr : D.resolutionRank d = 1) :
    ∃ (a : ℕ) (v : Fin 2 → R3 k),
      (a : ℤ) < d ∧ IsRelPrime (v 0) (v 1) ∧
      (∀ z, MvPolynomial.IsHomogeneous (v z) a) ∧
      ∀ i : D.LowP d, ∃ r : R3 k, D.δ₁ i.1 = r • v := by
  classical
  have hrNat : finrank (FractionRing (R3 k))
      (LinearMap.range (D.lowδ₁ d)) = 1 := by
    unfold GradedResolutionDuality.resolutionRank at hr
    exact_mod_cast hr
  have hcard : 0 < Fintype.card (D.LowP d) := by
    have hle := LinearMap.finrank_range_le (D.lowδ₁ d)
    rw [Module.finrank_fintype_fun_eq_card] at hle
    omega
  let i0 : D.LowP d := Classical.choice (Fintype.card_pos_iff.mp hcard)
  let f : Fin 2 → R3 k := D.δ₁ i0.1
  have hf : f ≠ 0 := D.δ₁_ne_zero i0.1
  let n : ℕ := (D.pShift i0.1).toNat
  obtain ⟨a, c, v, han, hfactor, hprim, hchom, hvhom⟩ :=
    homogeneous_primitive_pair_factorization f n hf (D.δ₁_homogeneous i0.1)
  have hncast : (n : ℤ) = D.pShift i0.1 :=
    Int.toNat_of_nonneg (D.pShift_nonneg i0.1)
  have had : (a : ℤ) < d := by
    have haZ : (a : ℤ) ≤ D.pShift i0.1 := by
      rw [← hncast]
      exact_mod_cast han
    exact haZ.trans_lt i0.2
  refine ⟨a, v, had, hprim, hvhom, ?_⟩
  letI : GCDMonoid (R3 k) :=
    UniqueFactorizationMonoid.toGCDMonoid (R3 k)
  let fK : Fin 2 → FractionRing (R3 k) := fun z =>
    algebraMap (R3 k) (FractionRing (R3 k)) (f z)
  have hfK : fK ≠ 0 := by
    intro hz
    apply hf
    funext z
    apply IsFractionRing.injective (R3 k) (FractionRing (R3 k))
    simpa [fK] using congrFun hz z
  have hcol0 : D.lowδ₁ d (Pi.single i0 1) = fK := by
    funext z
    simp [GradedResolutionDuality.lowδ₁, fK, f,
      Fintype.linearCombination_apply_single]
  let y0 : LinearMap.range (D.lowδ₁ d) :=
    ⟨fK, ⟨Pi.single i0 1, hcol0⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro hy
    apply hfK
    exact congrArg Subtype.val hy
  have hspan := (finrank_eq_one_iff_of_nonzero' y0 hy0).mp hrNat
  intro i
  let iK : Fin 2 → FractionRing (R3 k) := fun z =>
    algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i.1 z)
  have hcoli : D.lowδ₁ d (Pi.single i 1) = iK := by
    funext z
    simp [GradedResolutionDuality.lowδ₁, iK,
      Fintype.linearCombination_apply_single]
  let yi : LinearMap.range (D.lowδ₁ d) :=
    ⟨iK, ⟨Pi.single i 1, hcoli⟩⟩
  obtain ⟨a, ha⟩ := hspan yi
  have hline : ∀ z, algebraMap (R3 k) (FractionRing (R3 k)) (D.δ₁ i.1 z) =
      (a * algebraMap (R3 k) (FractionRing (R3 k)) c) *
        algebraMap (R3 k) (FractionRing (R3 k)) (v z) := by
    intro z
    have haz := congrFun (congrArg Subtype.val ha) z
    change a * fK z = iK z at haz
    change iK z = _
    rw [← haz]
    simp only [fK, iK, hfactor z, map_mul]
    ring
  obtain ⟨r, hr⟩ := primitive_line_saturated_fraction hprim
    (a * algebraMap (R3 k) (FractionRing (R3 k)) c) hline
  refine ⟨r, ?_⟩
  funext z
  simpa [Pi.smul_apply, smul_eq_mul] using hr z

/-- The polynomial (rather than localized) restriction of the first
differential to shifts strictly below `d`. -/
noncomputable def lowFirstPolynomial
    {I : Ideal (R3 k)} {e : ℕ}
    {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ) :
    (D.LowP d → R3 k) →ₗ[R3 k] (Fin 2 → R3 k) :=
  Fintype.linearCombination (R3 k) (fun i => D.δ₁ i.1)

/-- A scalar multiplying a nonzero homogeneous primitive pair to a
homogeneous pair is itself homogeneous, with the complementary degree. -/
lemma homogeneous_coefficient_of_primitive_multiple
    {a n : ℕ} {v f : Fin 2 → R3 k} {c : R3 k}
    (hprim : IsRelPrime (v 0) (v 1))
    (hvhom : ∀ z, MvPolynomial.IsHomogeneous (v z) a)
    (hfhom : ∀ z, MvPolynomial.IsHomogeneous (f z) n)
    (hfactor : f = c • v) :
    MvPolynomial.IsHomogeneous c (n - a) := by
  by_cases hc : c = 0
  · rw [hc]
    exact MvPolynomial.isHomogeneous_zero (Fin 3) k (n - a)
  obtain ⟨z, hvz⟩ : ∃ z, v z ≠ 0 := by
    rcases hprim.ne_zero_or_ne_zero with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have hmul : c * v z = f z := by
    have hz := congrFun hfactor z
    simpa [Pi.smul_apply, smul_eq_mul] using hz.symm
  obtain ⟨b, a', hsum, hchom, hvhom'⟩ :=
    homogeneous_factors_of_mul_eq hc hvz hmul (hfhom z)
  have haa : a' = a := hvhom'.inj_right (hvhom z) hvz
  have hba : b = n - a := by omega
  simpa [hba] using hchom

/-- The homogeneous degree-`t` part of a primitive rank-one module `vJ`
is exactly the image of the complementary homogeneous piece of `J`. -/
lemma homogeneousPiece_primitiveIdealLine_eq_vJPiece
    (J : Ideal (R3 k)) (hJ : J.IsHomogeneous
      (homogeneousSubmodule (Fin 3) k))
    {v : Fin 2 → R3 k} {a : ℕ}
    (hprim : IsRelPrime (v 0) (v 1))
    (hvhom : ∀ z, MvPolynomial.IsHomogeneous (v z) a)
    {t : ℤ} (ht : 0 ≤ t) :
    LinearMap.range (vectorHomogeneousComponent t.toNat) ⊓
        Submodule.restrictScalars k
          (Submodule.map
            (LinearMap.toSpanSingleton (R3 k) (Fin 2 → R3 k) v)
            (J : Submodule (R3 k) (R3 k))) =
      vJPiece J v a t := by
  classical
  ext u
  by_cases hta : 0 ≤ t - (a : ℤ)
  · rw [vJPiece, if_pos hta]
    constructor
    · intro hu
      have huhom := vectorHomogeneousComponent_mem_range_iff.mp hu.1
      obtain ⟨r, hrJ, hru⟩ := hu.2
      have hfactor : u = r • v := by
        simpa [LinearMap.toSpanSingleton_apply] using hru.symm
      have hrhom0 := homogeneous_coefficient_of_primitive_multiple
        hprim hvhom huhom hfactor
      have hdeg : t.toNat - a = (t - (a : ℤ)).toNat := by
        have htt : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht
        have htaNat : a ≤ t.toNat := by
          have hz : (a : ℤ) ≤ (t.toNat : ℤ) := by omega
          exact_mod_cast hz
        have hz : ((t.toNat - a : ℕ) : ℤ) = t - (a : ℤ) := by
          rw [Nat.cast_sub htaNat, htt]
        have hz' : ((t.toNat - a : ℕ) : ℤ) =
            (((t - (a : ℤ)).toNat : ℕ) : ℤ) := by
          rw [hz, Int.toNat_of_nonneg hta]
        exact_mod_cast hz'
      have hrhom : MvPolynomial.IsHomogeneous r
          (t - (a : ℤ)).toNat := by simpa only [hdeg] using hrhom0
      refine ⟨r, ⟨hrhom, hrJ⟩, ?_⟩
      simpa [vectorMul, LinearMap.toSpanSingleton_apply] using hfactor.symm
    · intro hu
      obtain ⟨w, hw, rfl⟩ := hu
      have hdeg : (t - (a : ℤ)).toNat + a = t.toNat := by
        omega
      constructor
      · apply vectorHomogeneousComponent_mem_range_iff.mpr
        intro z
        have hh := hw.1.mul (hvhom z)
        rw [hdeg] at hh
        simpa [vectorMul, LinearMap.toSpanSingleton_apply,
          Pi.smul_apply, smul_eq_mul] using hh
      · change vectorMul v w ∈ Submodule.restrictScalars k
          (Submodule.map
            (LinearMap.toSpanSingleton (R3 k) (Fin 2 → R3 k) v)
            (J : Submodule (R3 k) (R3 k)))
        refine ⟨w, hw.2, ?_⟩
        rfl
  · rw [vJPiece, if_neg hta]
    constructor
    · intro hu
      have huhom := vectorHomogeneousComponent_mem_range_iff.mp hu.1
      obtain ⟨r, hrJ, hru⟩ := hu.2
      have hfactor : u = r • v := by
        simpa [LinearMap.toSpanSingleton_apply] using hru.symm
      have hu0 : u = 0 := by
        by_cases hr : r = 0
        · simp [hfactor, hr]
        obtain ⟨z, hvz⟩ : ∃ z, v z ≠ 0 := by
          rcases hprim.ne_zero_or_ne_zero with h0 | h1
          · exact ⟨0, h0⟩
          · exact ⟨1, h1⟩
        have hmul : r * v z = u z := by
          have hz := congrFun hfactor z
          simpa [Pi.smul_apply, smul_eq_mul] using hz.symm
        obtain ⟨b, a', hsum, hrh, hvh⟩ :=
          homogeneous_factors_of_mul_eq hr hvz hmul (huhom z)
        have haa : a' = a := hvh.inj_right (hvhom z) hvz
        have hle : a ≤ t.toNat := by omega
        have htt : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht
        exfalso
        apply hta
        have hz : (a : ℤ) ≤ (t.toNat : ℤ) := by exact_mod_cast hle
        rw [Int.toNat_of_nonneg ht] at hz
        omega
      show u ∈ (⊥ : Submodule k (Fin 2 → R3 k))
      simpa using hu0
    · intro hu
      have hu0 : u = 0 := by simpa using hu
      subst u
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩

lemma pShift_ne_of_p_eq_zero
    {I : Ideal (R3 k)} {e : ℕ}
    {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]
    (D : GradedResolutionDuality I e β₁ β₂) {d : ℤ}
    (hp : D.p d = 0) (i : β₁) : D.pShift i ≠ d := by
  intro hi
  unfold GradedResolutionDuality.p shiftMultiplicity at hp
  have hcard : (Finset.univ.filter fun j => D.pShift j = d).card = 0 := by
    exact_mod_cast hp
  have hempty := Finset.card_eq_zero.mp hcard
  have himem : i ∈ Finset.univ.filter fun j => D.pShift j = d := by
    simp [hi]
  rw [hempty] at himem
  simp at himem

lemma lowFirstPolynomial_apply_eq_d₁_of_high_eq_zero
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA)
    {β₂ : Type*} [Fintype β₂]
    (D : GradedResolutionDuality I e C.β₁ β₂)
    (hδ : ∀ i, D.δ₁ i = C.d₁ (Pi.single i 1))
    (d : ℤ) (y : C.β₁ → R3 k)
    (hy : ∀ i, ¬ D.pShift i < d → y i = 0) :
    lowFirstPolynomial D d (fun i => y i.1) = C.d₁ y := by
  classical
  let term : C.β₁ → (Fin 2 → R3 k) := fun i =>
    y i • C.d₁ (Pi.single i 1)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : C.β₁ => D.pShift i < d) term
  have hhigh : (∑ i : {i : C.β₁ // ¬ D.pShift i < d}, term i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [term, hy i.1 i.2]
  have hlow : (∑ i : D.LowP d, term i.1) = ∑ i, term i := by
    rw [hhigh, add_zero] at hsplit
    exact hsplit
  calc
    lowFirstPolynomial D d (fun i => y i.1) =
        ∑ i : D.LowP d, term i.1 := by
      simp only [lowFirstPolynomial, Fintype.linearCombination_apply, term]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hδ i.1]
    _ = ∑ i, term i := hlow
    _ = C.d₁ y := by
      rw [← C.firstRelations_d₁_eq]
      rfl

/-- Up through the critical degree, and when no first shift equals `d`,
the homogeneous kernel piece is obtained from precisely the columns whose
shifts are strictly below `d`. -/
lemma minimalKernelPiece_eq_lowFirstHomogeneousPiece
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    {β₂ : Type*} [Fintype β₂]
    (D : GradedResolutionDuality I e C.β₁ β₂)
    (hshift : ∀ i, D.pShift i = (C.pShift i : ℤ))
    (hδ : ∀ i, D.δ₁ i = C.d₁ (Pi.single i 1))
    {d t : ℤ} (hp : D.p d = 0) (ht : 0 ≤ t) (htd : t ≤ d) :
    minimalKernelPiece hA C t =
      LinearMap.range (vectorHomogeneousComponent t.toNat) ⊓
        Submodule.restrictScalars k
          (LinearMap.range (lowFirstPolynomial D d)) := by
  classical
  ext u
  constructor
  · intro hu
    rw [minimalKernelPiece, dif_pos ht, Submodule.mem_inf] at hu
    refine ⟨hu.1, ?_⟩
    obtain ⟨c, hc⟩ := hu.2
    have hc' : C.d₁ c = u := hc
    let y : C.β₁ → R3 k := shiftedProjection C.pShift t.toNat c
    have hyu : C.d₁ y = u := by
      let H := C.firstRelations
      have hgraded := H.d₁_shiftedComponent t.toNat c
      have hcomponent : vectorHomogeneousComponent t.toNat u = u := by
        funext z
        have huz := vectorHomogeneousComponent_mem_range_iff.mp hu.1 z
        simpa [vectorHomogeneousComponent_apply] using
          (MvPolynomial.homogeneousComponent_of_mem
            (m := t.toNat) (n := t.toNat)
            ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr huz))
      have hgraded' : C.d₁ y = vectorHomogeneousComponent t.toNat (C.d₁ c) := by
        simpa [y, H, C.firstRelations_d₁_eq, shiftedProjection,
          HomogeneousFirstRelations.shiftedComponent] using hgraded
      rw [hc', hcomponent] at hgraded'
      exact hgraded'
    have hyhigh : ∀ i, ¬ D.pShift i < d → y i = 0 := by
      intro i hi
      have hnotle : ¬ C.pShift i ≤ t.toNat := by
        intro hle
        have hleZ : D.pShift i ≤ t := by
          have htt : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht
          rw [hshift i, ← htt]
          exact_mod_cast hle
        have heq : D.pShift i = d := by omega
        exact pShift_ne_of_p_eq_zero D hp i heq
      simp [y, shiftedProjection_apply, hnotle]
    refine ⟨(fun i => y i.1), ?_⟩
    exact (lowFirstPolynomial_apply_eq_d₁_of_high_eq_zero
      C D hδ d y hyhigh).trans hyu
  · rintro ⟨huhom, hulow⟩
    rw [minimalKernelPiece, dif_pos ht, Submodule.mem_inf]
    refine ⟨huhom, ?_⟩
    obtain ⟨x, hx⟩ := hulow
    let y : C.β₁ → R3 k := fun i =>
      if hi : D.pShift i < d then x ⟨i, hi⟩ else 0
    have hyhigh : ∀ i, ¬ D.pShift i < d → y i = 0 := by
      intro i hi
      simp [y, hi]
    refine ⟨y, ?_⟩
    change C.d₁ y = u
    rw [← lowFirstPolynomial_apply_eq_d₁_of_high_eq_zero C D hδ d y hyhigh]
    have hyx : (fun i : D.LowP d => y i.1) = x := by
      funext i
      simp [y, i.2]
    rw [hyx]
    exact hx

/-- Ungraded equation (7): in the rank-one branch, the image of the
low-shift first differential is `vJ` for a primitive vector `v` and an
actual ideal `J` of the polynomial ring.  The later critical construction
only still has to prove that `v` and `J` respect the grading and that the
degreewise truncation agrees with this full range equality. -/
lemma rank_one_low_range_eq_primitive_ideal
    {I : Ideal (R3 k)} {e : ℕ}
    {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]
    (D : GradedResolutionDuality I e β₁ β₂) (d : ℤ)
    (hr : D.resolutionRank d = 1) :
    ∃ (a : ℕ) (v : Fin 2 → R3 k) (J : Ideal (R3 k)),
      (a : ℤ) < d ∧ IsRelPrime (v 0) (v 1) ∧
      (∀ z, MvPolynomial.IsHomogeneous (v z) a) ∧
      J.IsHomogeneous (homogeneousSubmodule (Fin 3) k) ∧
      LinearMap.range (lowFirstPolynomial D d) =
        Submodule.map
          (LinearMap.toSpanSingleton (R3 k) (Fin 2 → R3 k) v)
          (J : Submodule (R3 k) (R3 k)) := by
  classical
  obtain ⟨a, v, had, hprim, hvhom, hcols⟩ :=
    rank_one_low_columns_primitive_line D d hr
  have hv : v ≠ 0 := by
    intro hz
    rcases hprim.ne_zero_or_ne_zero with h0 | h1
    · exact h0 (congrFun hz 0)
    · exact h1 (congrFun hz 1)
  choose coeff hcoeff using hcols
  have hcoeffhom : ∀ i, SetLike.IsHomogeneousElem
      (homogeneousSubmodule (Fin 3) k) (coeff i) := by
    intro i
    let n := (D.pShift i.1).toNat
    refine ⟨n - a, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr ?_⟩
    apply homogeneous_coefficient_of_primitive_multiple hprim hvhom
      (D.δ₁_homogeneous i.1)
    exact hcoeff i
  let J : Ideal (R3 k) := Ideal.span (Set.range coeff)
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin 3) k) := by
    apply Ideal.homogeneous_span
    rintro x ⟨i, rfl⟩
    exact hcoeffhom i
  have hmap : lowFirstPolynomial D d =
      (LinearMap.toSpanSingleton (R3 k) (Fin 2 → R3 k) v).comp
        (Fintype.linearCombination (R3 k) coeff) := by
    apply LinearMap.ext
    intro x
    funext z
    simp only [lowFirstPolynomial, Fintype.linearCombination_apply,
      LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hiz := congrFun (hcoeff i) z
    simp only [Pi.smul_apply, smul_eq_mul] at hiz
    rw [hiz]
    ring
  refine ⟨a, v, J, had, hprim, hvhom, hJhom, ?_⟩
  rw [hmap, LinearMap.range_comp, Fintype.range_linearCombination]

/-- The rank-one and `p_d = 0` hypotheses now imply the complete graded
equation (7), including negative degrees. -/
lemma rank_one_critical_equation7
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    {β₂ : Type*} [Fintype β₂]
    (D : GradedResolutionDuality I e C.β₁ β₂)
    (hshift : ∀ i, D.pShift i = (C.pShift i : ℤ))
    (hδ : ∀ i, D.δ₁ i = C.d₁ (Pi.single i 1))
    (d : ℤ) (hr : D.resolutionRank d = 1) (hp : D.p d = 0) :
    ∃ (a : ℕ) (v : Fin 2 → R3 k) (J : Ideal (R3 k)),
      (a : ℤ) < d ∧ IsRelPrime (v 0) (v 1) ∧
      (∀ z, MvPolynomial.IsHomogeneous (v z) a) ∧
      J.IsHomogeneous (homogeneousSubmodule (Fin 3) k) ∧
      ∀ t : ℤ, t ≤ d → minimalKernelPiece hA C t = vJPiece J v a t := by
  obtain ⟨a, v, J, had, hprim, hvhom, hJhom, hrange⟩ :=
    rank_one_low_range_eq_primitive_ideal D d hr
  refine ⟨a, v, J, had, hprim, hvhom, hJhom, ?_⟩
  intro t htd
  by_cases ht : 0 ≤ t
  · rw [minimalKernelPiece_eq_lowFirstHomogeneousPiece hA C D
        hshift hδ hp ht htd, hrange]
    exact homogeneousPiece_primitiveIdealLine_eq_vJPiece
      J hJhom hprim hvhom ht
  · have htneg : t < 0 := by omega
    rw [minimalKernelPiece_zero_of_neg hA C htneg, vJPiece,
      if_neg (show ¬ 0 ≤ t - (a : ℤ) by omega)]

/-- The annihilator of the Matlis-dual element represented by `v`. -/
noncomputable def matlisAnnihilator
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (v : Fin 2 → R3 k) : Ideal (R3 k) :=
  (Submodule.span (R3 k) ({inverseSystemMap hA v} : Set (MatlisDual I))).annihilator

lemma matlisComponent_eq_self_of_mem
    {I : Ideal (R3 k)} (hI : I.IsHomogeneous
      (homogeneousSubmodule (Fin 3) k)) {n : ℕ}
    {phi : MatlisDual I} (hphi : phi ∈ matlisPiece I hI n) :
    matlisComponent I hI n phi = phi := by
  apply MatlisDual.ext
  apply LinearMap.ext
  intro x
  change phi (quotientComponent I hI n x) = phi x
  exact (matlisPiece_apply_projection I hI n ⟨phi, hphi⟩ x).symm

lemma matlisComponent_eq_zero_of_mem
    {I : Ideal (R3 k)} (hI : I.IsHomogeneous
      (homogeneousSubmodule (Fin 3) k)) {m n : ℕ} (hmn : m ≠ n)
    {phi : MatlisDual I} (hphi : phi ∈ matlisPiece I hI n) :
    matlisComponent I hI m phi = 0 := by
  apply MatlisDual.ext
  apply LinearMap.ext
  intro x
  change phi (quotientComponent I hI m x) = 0
  rw [matlisPiece_apply_projection I hI n ⟨phi, hphi⟩]
  have hx := quotientComponent_mem_quotPiece I hI m x
  rw [quotientComponent_eq_zero_of_mem I hI hmn.symm hx, map_zero]

lemma inverseSystemMap_homogeneous_vector_mem
    {I : Ideal (R3 k)} {e a : ℕ} (hA : IsTypeTwoLevel I e)
    (hae : a ≤ e) {v : Fin 2 → R3 k}
    (hv : ∀ z, MvPolynomial.IsHomogeneous (v z) a) :
    inverseSystemMap hA v ∈ matlisPiece I hA.homogeneous (e - a) := by
  let u : Fin 2 → homogeneousSubmodule (Fin 3) k
      (e - (e - a)) := fun z => ⟨v z, by
        rw [Nat.sub_sub_self hae]
        exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hv z)⟩
  have hu := inverseSystemMap_homogeneous_mem hA (Nat.sub_le e a) u
  have huv : (fun i => ((u i : homogeneousSubmodule (Fin 3) k
      (e - (e - a))) : R3 k)) = v := by rfl
  simpa [huv] using hu

/-- Homogeneous components of a scalar relation on a pure Matlis element
are again scalar relations. -/
lemma homogeneousComponent_smul_eq_zero_of_pure_matlis
    {I : Ideal (R3 k)} (hI : I.IsHomogeneous
      (homogeneousSubmodule (Fin 3) k)) {E : ℕ}
    {H : MatlisDual I} (hH : H ∈ matlisPiece I hI E)
    {f : R3 k} (hf : f • H = 0) (q : ℕ) :
    MvPolynomial.homogeneousComponent q f • H = 0 := by
  classical
  let fq : ℕ → R3 k := fun n => MvPolynomial.homogeneousComponent n f
  have hfqhom : ∀ n, MvPolynomial.IsHomogeneous (fq n) n := fun n =>
    MvPolynomial.homogeneousComponent_isHomogeneous n f
  by_cases hqdeg : f.totalDegree < q
  · rw [MvPolynomial.homogeneousComponent_eq_zero q f hqdeg, zero_smul]
  by_cases hqE : E < q
  · exact matlisPiece_smul_eq_zero_of_lt hI (hfqhom q) hqE hH
  have hqle : q ≤ E := by omega
  have hqmem : q ∈ Finset.range (f.totalDegree + 1) := by simp; omega
  have hsum : ∑ n ∈ Finset.range (f.totalDegree + 1), fq n = f := by
    simpa [fq] using MvPolynomial.sum_homogeneousComponent f
  have hsumzero : (∑ n ∈ Finset.range (f.totalDegree + 1), fq n • H) = 0 := by
    rw [← Finset.sum_smul, hsum, hf]
  have hproject := congrArg
    (matlisComponent I hI (E - q)) hsumzero
  rw [map_sum, map_zero] at hproject
  have hsingle :
      (∑ n ∈ Finset.range (f.totalDegree + 1),
        matlisComponent I hI (E - q) (fq n • H)) = fq q • H := by
    rw [Finset.sum_eq_single q]
    · have hmem : fq q • H ∈ matlisPiece I hI (E - q) := by
        simpa using matlisPiece_smul hI (hfqhom q) hqle hH
      exact matlisComponent_eq_self_of_mem hI hmem
    · intro n hn hnq
      by_cases hnE : n ≤ E
      · have hmem : fq n • H ∈ matlisPiece I hI (E - n) := by
          simpa using matlisPiece_smul hI (hfqhom n) hnE hH
        apply matlisComponent_eq_zero_of_mem hI
          (show E - q ≠ E - n by omega) hmem
      · have hz : fq n • H = 0 :=
          matlisPiece_smul_eq_zero_of_lt hI (hfqhom n) (by omega) hH
        rw [hz, map_zero]
    · intro hnot
      exact (hnot hqmem).elim
  rw [hsingle] at hproject
  exact hproject

lemma matlisAnnihilator_isHomogeneous
    {I : Ideal (R3 k)} {e a : ℕ} (hA : IsTypeTwoLevel I e)
    (hae : a ≤ e) {v : Fin 2 → R3 k}
    (hv : ∀ z, MvPolynomial.IsHomogeneous (v z) a) :
    (matlisAnnihilator hA v).IsHomogeneous
      (homogeneousSubmodule (Fin 3) k) := by
  intro q f hf
  have hgoal : MvPolynomial.homogeneousComponent q f ∈ matlisAnnihilator hA v := by
    rw [matlisAnnihilator, Submodule.mem_annihilator_span_singleton] at hf ⊢
    exact homogeneousComponent_smul_eq_zero_of_pure_matlis hA.homogeneous
      (inverseSystemMap_homogeneous_vector_mem hA hae hv) hf q
  rw [← MvPolynomial.decomposition.decompose'_apply] at hgoal
  exact hgoal

lemma originalIdeal_le_matlisAnnihilator
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (v : Fin 2 → R3 k) : I ≤ matlisAnnihilator hA v := by
  intro f hf
  rw [matlisAnnihilator, Submodule.mem_annihilator_span_singleton]
  apply MatlisDual.ext
  apply LinearMap.ext
  intro x
  change (inverseSystemMap hA v)
    (Ideal.Quotient.mk I f * x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, zero_mul, map_zero]

noncomputable instance matlisAnnihilator_quotient_finiteDimensional
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (v : Fin 2 → R3 k) :
    FiniteDimensional k (R3 k ⧸ matlisAnnihilator hA v) := by
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  let F := (Ideal.Quotient.factorₐ k
    (originalIdeal_le_matlisAnnihilator hA v)).toLinearMap
  exact FiniteDimensional.of_surjective F
    (Ideal.Quotient.factor_surjective
      (originalIdeal_le_matlisAnnihilator hA v))

lemma matlisAnnihilator_vanish_above
    {I : Ideal (R3 k)} {e a : ℕ} (hA : IsTypeTwoLevel I e)
    (hae : a ≤ e) {v : Fin 2 → R3 k}
    (hv : ∀ z, MvPolynomial.IsHomogeneous (v z) a)
    {n : ℕ} (hn : e - a < n) :
    quotPiece (matlisAnnihilator hA v) n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨f, hfhom, rfl⟩ := Submodule.mem_map.mp hx
  change Ideal.Quotient.mk (matlisAnnihilator hA v) f = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [matlisAnnihilator, Submodule.mem_annihilator_span_singleton]
  exact matlisPiece_smul_eq_zero_of_lt hA.homogeneous
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hfhom) hn
    (inverseSystemMap_homogeneous_vector_mem hA hae hv)

noncomputable def cyclicMatlisMap
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (v : Fin 2 → R3 k) :
    (R3 k ⧸ matlisAnnihilator hA v) →ₗ[k] MatlisDual I :=
  Submodule.liftQ ((matlisAnnihilator hA v).restrictScalars k)
    ((LinearMap.toSpanSingleton (R3 k) (MatlisDual I)
      (inverseSystemMap hA v)).restrictScalars k) (by
        intro f hf
        rw [LinearMap.mem_ker]
        exact (Submodule.mem_annihilator_span_singleton
          (inverseSystemMap hA v) f).mp hf)

@[simp] lemma cyclicMatlisMap_mk
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (v : Fin 2 → R3 k) (f : R3 k) :
    cyclicMatlisMap hA v (Ideal.Quotient.mk (matlisAnnihilator hA v) f) =
      f • inverseSystemMap hA v := rfl

lemma cyclicMatlisMap_injective
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (v : Fin 2 → R3 k) : Function.Injective (cyclicMatlisMap hA v) := by
  intro x y hxy
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [cyclicMatlisMap_mk, cyclicMatlisMap_mk] at hxy
  apply Ideal.Quotient.eq.mpr
  rw [matlisAnnihilator, Submodule.mem_annihilator_span_singleton,
    sub_smul, hxy, sub_self]

lemma cyclicMatlisMap_mul
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (v : Fin 2 → R3 k) (f : R3 k)
    (x : R3 k ⧸ matlisAnnihilator hA v) :
    cyclicMatlisMap hA v
        (Ideal.Quotient.mk (matlisAnnihilator hA v) f * x) =
      f • cyclicMatlisMap hA v x := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [← map_mul, cyclicMatlisMap_mk, mul_smul]

lemma cyclicMatlisMap_socle_mem
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    {v : Fin 2 → R3 k} {x : R3 k ⧸ matlisAnnihilator hA v}
    (hx : x ∈ socle (matlisAnnihilator hA v)) :
    cyclicMatlisMap hA v x ∈ matlisDualSocle hA := by
  rw [matlisDualSocle_mem_iff]
  intro j
  rw [← cyclicMatlisMap_mul, hx j]
  exact map_zero _

lemma matlisAnnihilator_topPiece_ne_bot
    {I : Ideal (R3 k)} {e a : ℕ} (hA : IsTypeTwoLevel I e)
    (hae : a ≤ e) {v : Fin 2 → R3 k}
    (hv : ∀ z, MvPolynomial.IsHomogeneous (v z) a)
    (hHne : inverseSystemMap hA v ≠ 0) :
    quotPiece (matlisAnnihilator hA v) (e - a) ≠ ⊥ := by
  let H : MatlisDual I := inverseSystemMap hA v
  have hHpure : H ∈ matlisPiece I hA.homogeneous (e - a) :=
    inverseSystemMap_homogeneous_vector_mem hA hae hv
  obtain ⟨x, hx⟩ : ∃ x : R3 k ⧸ I, H x ≠ 0 := by
    have hval : H.val ≠ 0 := by
      intro hz
      apply hHne
      apply MatlisDual.ext
      exact hz
    simpa using DFunLike.ne_iff.mp hval
  let y := quotientComponent I hA.homogeneous (e - a) x
  have hyx : H y = H x :=
    matlisPiece_apply_projection I hA.homogeneous (e - a) ⟨H, hHpure⟩ x |>.symm
  have hymem := quotientComponent_mem_quotPiece I hA.homogeneous (e - a) x
  obtain ⟨f, hfhom, hfy⟩ := Submodule.mem_map.mp hymem
  have hHf : H (Ideal.Quotient.mk I f) ≠ 0 := by
    have hmk : (Ideal.Quotient.mkₐ k I).toLinearMap f =
        Ideal.Quotient.mk I f := rfl
    rw [← hmk, hfy, hyx]
    exact hx
  let z : R3 k ⧸ matlisAnnihilator hA v :=
    Ideal.Quotient.mk (matlisAnnihilator hA v) f
  have hzmem : z ∈ quotPiece (matlisAnnihilator hA v) (e - a) := by
    exact Submodule.mem_map.mpr ⟨f, hfhom, rfl⟩
  intro hbot
  have hz0 : z = 0 := by
    rw [hbot] at hzmem
    simpa using hzmem
  have hfAnn : f ∈ matlisAnnihilator hA v :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz0
  have hfzero := (Submodule.mem_annihilator_span_singleton H f).mp hfAnn
  have heval : (f • H) (Ideal.Quotient.mk I 1) = 0 := by
    rw [hfzero]; rfl
  apply hHf
  simpa using heval

lemma matlisAnnihilator_socle_one
    {I : Ideal (R3 k)} {e a : ℕ} (hA : IsTypeTwoLevel I e)
    (hae : a ≤ e) {v : Fin 2 → R3 k}
    (hv : ∀ z, MvPolynomial.IsHomogeneous (v z) a)
    (hHne : inverseSystemMap hA v ≠ 0) :
    finrank k (socle (matlisAnnihilator hA v)) = 1 := by
  letI : FiniteDimensional k (R3 k ⧸ matlisAnnihilator hA v) :=
    matlisAnnihilator_quotient_finiteDimensional hA v
  letI : FiniteDimensional k (R3 k ⧸ I) := hA.finiteDimensional
  let F : socle (matlisAnnihilator hA v) →ₗ[k] matlisDualSocle hA :=
    { toFun := fun x => ⟨cyclicMatlisMap hA v x.1,
          cyclicMatlisMap_socle_mem hA x.2⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro c x; apply Subtype.ext; simp }
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply cyclicMatlisMap_injective hA v
    exact congrArg Subtype.val hxy
  have hupper := LinearMap.finrank_le_finrank_of_injective hFinj
  rw [matlisDualSocle_finrank hA] at hupper
  let H : MatlisDual I := inverseSystemMap hA v
  have hHpure : H ∈ matlisPiece I hA.homogeneous (e - a) :=
    inverseSystemMap_homogeneous_vector_mem hA hae hv
  obtain ⟨x, hx⟩ : ∃ x : R3 k ⧸ I, H x ≠ 0 := by
    have hval : H.val ≠ 0 := by
      intro hz
      apply hHne
      apply MatlisDual.ext
      exact hz
    simpa using DFunLike.ne_iff.mp hval
  let y := quotientComponent I hA.homogeneous (e - a) x
  have hyx : H y = H x :=
    matlisPiece_apply_projection I hA.homogeneous (e - a) ⟨H, hHpure⟩ x |>.symm
  have hymem := quotientComponent_mem_quotPiece I hA.homogeneous (e - a) x
  obtain ⟨f, hfhom, hfy⟩ := Submodule.mem_map.mp hymem
  have hHf : H (Ideal.Quotient.mk I f) ≠ 0 := by
    have hmk : (Ideal.Quotient.mkₐ k I).toLinearMap f =
        Ideal.Quotient.mk I f := rfl
    rw [← hmk, hfy, hyx]
    exact hx
  let z : R3 k ⧸ matlisAnnihilator hA v :=
    Ideal.Quotient.mk (matlisAnnihilator hA v) f
  have hzmem : z ∈ socle (matlisAnnihilator hA v) := by
    intro j
    change Ideal.Quotient.mk (matlisAnnihilator hA v)
      (MvPolynomial.X j * f) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [matlisAnnihilator, Submodule.mem_annihilator_span_singleton]
    have hprod : MvPolynomial.IsHomogeneous
        (MvPolynomial.X j * f) ((e - a) + 1) := by
      have h := (MvPolynomial.isHomogeneous_X k j).mul
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hfhom)
      rwa [Nat.add_comm] at h
    exact matlisPiece_smul_eq_zero_of_lt hA.homogeneous hprod (by omega) hHpure
  have hz_ne : z ≠ 0 := by
    intro hz
    have hfAnn : f ∈ matlisAnnihilator hA v :=
      Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hfzero := (Submodule.mem_annihilator_span_singleton H f).mp hfAnn
    have heval : (f • H) (Ideal.Quotient.mk I 1) = 0 := by
      rw [hfzero]; rfl
    apply hHf
    simpa using heval
  have hnonzero : socle (matlisAnnihilator hA v) ≠ ⊥ := by
    intro hbot
    have : z = 0 := by
      have := hzmem
      rw [hbot] at this
      simpa using this
    exact hz_ne this
  have hlower : 0 < finrank k (socle (matlisAnnihilator hA v)) := by
    rw [finrank_pos_iff]
    exact Submodule.nontrivial_iff_ne_bot.mpr hnonzero
  omega

lemma matlisAnnihilator_socle_concentrated
    {I : Ideal (R3 k)} {e a : ℕ} (hA : IsTypeTwoLevel I e)
    (hae : a ≤ e) {v : Fin 2 → R3 k}
    (hv : ∀ z, MvPolynomial.IsHomogeneous (v z) a)
    (hHne : inverseSystemMap hA v ≠ 0) :
    socle (matlisAnnihilator hA v) ≤
      quotPiece (matlisAnnihilator hA v) (e - a) := by
  letI : FiniteDimensional k (R3 k ⧸ matlisAnnihilator hA v) :=
    matlisAnnihilator_quotient_finiteDimensional hA v
  let Ann := matlisAnnihilator hA v
  let E := e - a
  have htop_le : quotPiece Ann E ≤ socle Ann := by
    intro x hx
    intro j
    have hmul : Ideal.Quotient.mk Ann (MvPolynomial.X j) * x ∈
        quotPiece Ann (1 + E) :=
      quotPiece_mul_homogeneous (MvPolynomial.isHomogeneous_X k j) hx
    have hvz : quotPiece Ann (1 + E) = ⊥ := by
      apply matlisAnnihilator_vanish_above hA hae hv
      omega
    rw [hvz] at hmul
    simpa using hmul
  have htop_ne : quotPiece Ann E ≠ ⊥ := by
    exact matlisAnnihilator_topPiece_ne_bot hA hae hv hHne
  have htop_pos : 0 < finrank k (quotPiece Ann E) := by
    rw [finrank_pos_iff]
    exact Submodule.nontrivial_iff_ne_bot.mpr htop_ne
  have hsoc_one : finrank k (socle Ann) = 1 :=
    matlisAnnihilator_socle_one hA hae hv hHne
  have heq : quotPiece Ann E = socle Ann := by
    apply Submodule.eq_of_le_of_finrank_le htop_le
    rw [hsoc_one]
    omega
  exact heq.ge

lemma matlisAnnihilator_eq_top_iff
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (v : Fin 2 → R3 k) :
    matlisAnnihilator hA v = ⊤ ↔ inverseSystemMap hA v = 0 := by
  constructor
  · intro htop
    have hone : (1 : R3 k) ∈ matlisAnnihilator hA v := by rw [htop]; simp
    rw [matlisAnnihilator, Submodule.mem_annihilator_span_singleton,
      one_smul] at hone
    exact hone
  · intro hzero
    apply top_unique
    intro f hf
    rw [matlisAnnihilator, Submodule.mem_annihilator_span_singleton,
      hzero, smul_zero]

/-- Equation (7) identifies the coefficient ideal with the annihilator of
`H = inverseSystemMap v` throughout the critical low-degree range. -/
lemma equation7_low_mem_iff_matlisAnnihilator
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    {d : ℤ} {a : ℕ} {v : Fin 2 → R3 k} {J : Ideal (R3 k)}
    (hprim : IsRelPrime (v 0) (v 1))
    (hvhom : ∀ z, MvPolynomial.IsHomogeneous (v z) a)
    (hequation : ∀ t : ℤ, t ≤ d →
      minimalKernelPiece hA C t = vJPiece J v a t) :
    ∀ n : ℕ, (n : ℤ) ≤ d - (a : ℤ) →
      ∀ f : R3 k, MvPolynomial.IsHomogeneous f n →
        (f ∈ J ↔ f ∈ matlisAnnihilator hA v) := by
  classical
  intro n hn f hf
  let t : ℤ := (n : ℤ) + (a : ℤ)
  have ht : 0 ≤ t := by simp only [t]; omega
  have htd : t ≤ d := by omega
  have hta : 0 ≤ t - (a : ℤ) := by simp [t]
  have hdeg : (t - (a : ℤ)).toNat = n := by simp [t]
  have hvne : v ≠ 0 := by
    intro hz
    rcases hprim.ne_zero_or_ne_zero with h0 | h1
    · exact h0 (congrFun hz 0)
    · exact h1 (congrFun hz 1)
  constructor
  · intro hfJ
    have hfvPiece : f • v ∈ vJPiece J v a t := by
      rw [vJPiece, if_pos hta]
      refine ⟨f, ⟨?_, hfJ⟩, ?_⟩
      · simpa [hdeg] using hf
      · rfl
    have hfvKernel : f • v ∈ minimalKernelPiece hA C t := by
      rw [hequation t htd]
      exact hfvPiece
    have hzero : inverseSystemMap hA (f • v) = 0 :=
      (minimalKernelPiece_mem_iff hA C ht (f • v)).mp hfvKernel |>.2
    rw [matlisAnnihilator, Submodule.mem_annihilator_span_singleton]
    simpa using hzero
  · intro hfAnn
    have hzero : inverseSystemMap hA (f • v) = 0 := by
      rw [map_smul]
      have := (Submodule.mem_annihilator_span_singleton
        (inverseSystemMap hA v) f).mp hfAnn
      exact this
    have hfvh : ∀ z, MvPolynomial.IsHomogeneous ((f • v) z) t.toNat := by
      intro z
      have htz : t.toNat = n + a := by
        omega
      have hh := hf.mul (hvhom z)
      rw [htz] at *
      simpa [Pi.smul_apply, smul_eq_mul] using hh
    have hfvKernel : f • v ∈ minimalKernelPiece hA C t :=
      (minimalKernelPiece_mem_iff hA C ht (f • v)).mpr ⟨hfvh, hzero⟩
    have hfvPiece : f • v ∈ vJPiece J v a t := by
      rw [← hequation t htd]
      exact hfvKernel
    rw [vJPiece, if_pos hta] at hfvPiece
    obtain ⟨g, hg, hgf⟩ := hfvPiece
    have hgf' : g • v = f • v := by
      simpa [vectorMul, LinearMap.toSpanSingleton_apply] using hgf
    have hgfscalar : g = f := by
      obtain ⟨z, hvz⟩ : ∃ z, v z ≠ 0 := by
        by_contra h
        push Not at h
        exact hvne (funext h)
      have hz := congrFun hgf' z
      simp only [Pi.smul_apply, smul_eq_mul] at hz
      exact mul_right_cancel₀ hvz hz
    simpa [hgfscalar] using hg.2

structure CriticalBranchAlgebraData
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA) (d : ℤ) where
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
  equation7 : ∀ t : ℤ, t ≤ d →
    minimalKernelPiece hA C t = vJPiece J v a t
  annihilator_case : Ann = ⊤ ∨
    GradedResolutionDuality.GorensteinAnnihilatorData Ann (e - a)

/-- The sole remaining algebraic fact in the critical branch: the
annihilator of a pure homogeneous element of the Matlis dual is either the
unit ideal (the element is zero) or an Artinian Gorenstein ideal of the
complementary socle degree. -/
structure MatlisAnnihilatorGorensteinProperty
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) : Prop where
  gorenstein : ∀ (a : ℕ), a ≤ e → ∀ v : Fin 2 → R3 k,
    (∀ z, MvPolynomial.IsHomogeneous (v z) a) →
    inverseSystemMap hA v ≠ 0 →
    GradedResolutionDuality.GorensteinAnnihilatorData
        (matlisAnnihilator hA v) (e - a)

noncomputable def MatlisAnnihilatorGorensteinProperty.ofLevel
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    MatlisAnnihilatorGorensteinProperty hA := by
  refine { gorenstein := ?_ }
  intro a hae v hv hHne
  exact
    { homogeneous := matlisAnnihilator_isHomogeneous hA hae hv
      proper := fun htop => hHne ((matlisAnnihilator_eq_top_iff hA v).mp htop)
      finiteDimensional := matlisAnnihilator_quotient_finiteDimensional hA v
      vanish_above := fun n hn =>
        matlisAnnihilator_vanish_above hA hae hv hn
      socle_concentrated :=
        matlisAnnihilator_socle_concentrated hA hae hv hHne
      socle_one := matlisAnnihilator_socle_one hA hae hv hHne }

namespace CriticalBranchAlgebraData

variable {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}

noncomputable def toCriticalBranchCertificate
    (C : GradedMinimalFreeComplex I e hA)
    {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]
    (D : GradedResolutionDuality I e β₁ β₂)
    (d : ℤ) (hd : 2 ≤ d) (hde : d ≤ (e : ℤ))
    (B : CriticalBranchAlgebraData C d) :
    GradedResolutionDuality.CriticalBranchCertificate D d := by
  refine
    { two_le_d := hd
      d_le_e := hde
      a := B.a
      a_lt_d := B.a_lt_d
      v := B.v
      v_primitive := B.v_primitive
      v_homogeneous := B.v_homogeneous
      J := B.J
      J_homogeneous := B.J_homogeneous
      Ann := B.Ann
      low_mem_iff := B.low_mem_iff
      kernelPiece := minimalKernelPiece hA C
      equation7 := B.equation7
      presentation_exact := ?_
      annihilator_case := B.annihilator_case }
  intro t hdt htd
  have ht0 : 0 ≤ t := by omega
  have hte : t ≤ (e : ℤ) := htd.trans hde
  exact minimalKernelPiece_surjectivePresentation hA C ht0 hte

end CriticalBranchAlgebraData

/-- The critical-branch input after removing the presentation bookkeeping
that is already forced by the minimal complex. -/
structure CriticalBranchAlgebraPackage
    {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}
    (C : GradedMinimalFreeComplex I e hA)
    (D : GradedResolutionDuality I e C.β₁ C.β₂) : Prop where
  critical : ∀ d : ℤ, 2 ≤ d → d ≤ (e : ℤ) →
    D.resolutionRank d = 1 → D.p d = 0 →
    reversedHilb I e d - 2 * reversedHilb I e (d - 1) +
      reversedHilb I e (d - 2) = 1 →
    Nonempty (CriticalBranchAlgebraData C d)

/-- All primitive-line, homogeneous-ideal, low-annihilator, and equation
(7) fields of the critical branch are forced by the two numerical rank
hypotheses.  Only the standard cyclic-Matlis Gorenstein fact remains as an
input to this constructor. -/
noncomputable def criticalBranchAlgebraPackage_of_matlisAnnihilator
    {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex I e hA)
    (D : GradedResolutionDuality I e C.β₁ C.β₂)
    (hshift : ∀ i, D.pShift i = (C.pShift i : ℤ))
    (hδ : ∀ i, D.δ₁ i = C.d₁ (Pi.single i 1))
    (G : MatlisAnnihilatorGorensteinProperty hA) :
    CriticalBranchAlgebraPackage C D := by
  refine { critical := ?_ }
  intro d hd hde hr hp hΔ
  obtain ⟨a, v, J, had, hprim, hvhom, hJhom, hequation⟩ :=
    rank_one_critical_equation7 hA C D hshift hδ d hr hp
  have hae : a ≤ e := by
    exact_mod_cast (show (a : ℤ) ≤ (e : ℤ) by omega)
  refine ⟨{
    a := a
    a_lt_d := had
    v := v
    v_primitive := hprim
    v_homogeneous := hvhom
    J := J
    J_homogeneous := hJhom
    Ann := matlisAnnihilator hA v
    low_mem_iff := equation7_low_mem_iff_matlisAnnihilator
      hA C hprim hvhom hequation
    equation7 := hequation
    annihilator_case := by
      by_cases hH : inverseSystemMap hA v = 0
      · exact Or.inl ((matlisAnnihilator_eq_top_iff hA v).mpr hH)
      · exact Or.inr (G.gorenstein a hae v hvhom hH) }⟩

namespace CriticalBranchAlgebraPackage

variable {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}

noncomputable def toResolutionPackage
    (C : GradedMinimalFreeComplex I e hA)
    (D : GradedResolutionDuality I e C.β₁ C.β₂)
    (P : CriticalBranchAlgebraPackage C D) : D.ResolutionPackage := by
  refine { critical := ?_ }
  intro d hd hde hr hp hΔ
  obtain ⟨B⟩ := P.critical d hd hde hr hp hΔ
  exact ⟨B.toCriticalBranchCertificate C D d hd hde⟩

end CriticalBranchAlgebraPackage

/-- Final `Fin n₁`/`Fin n₂` packaging.  The concrete minimal complex created
by `ofLevel` already uses `Fin` index types, so no additional basis transport
is hidden here. -/
theorem hasGradedResolutionPackage_of_reduced_data
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (L : CanonicalLastDifferentialData
      (GradedMinimalFreeComplex.ofLevel hA))
    (P : let C := GradedMinimalFreeComplex.ofLevel hA
      let D := GradedResolutionDuality.ofCanonicalLast hA C L
      CriticalBranchAlgebraPackage C D) :
    HasGradedResolutionPackage I e := by
  let C := GradedMinimalFreeComplex.ofLevel hA
  let D := GradedResolutionDuality.ofCanonicalLast hA C L
  have P' : CriticalBranchAlgebraPackage C D := P
  exact ⟨_, _, D, P'.toResolutionPackage C D⟩

/-- Package construction after discharging the entire rank-one critical
branch from the cyclic homogeneous Matlis-annihilator theorem. -/
theorem hasGradedResolutionPackage_of_canonicalLast_and_matlisAnnihilator
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (L : CanonicalLastDifferentialData
      (GradedMinimalFreeComplex.ofLevel hA))
    (G : MatlisAnnihilatorGorensteinProperty hA) :
    HasGradedResolutionPackage I e := by
  let C := GradedMinimalFreeComplex.ofLevel hA
  let D := GradedResolutionDuality.ofCanonicalLast hA C L
  have hshift : ∀ i, D.pShift i = (C.pShift i : ℤ) := by
    intro i
    rfl
  have hδ : ∀ i, D.δ₁ i = C.d₁ (Pi.single i 1) := by
    intro i
    rfl
  let P : CriticalBranchAlgebraPackage C D :=
    criticalBranchAlgebraPackage_of_matlisAnnihilator
      hA C D hshift hδ G
  exact ⟨_, _, D, P.toResolutionPackage C D⟩

theorem hasGradedResolutionPackage_of_canonicalLast
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (L : CanonicalLastDifferentialData
      (GradedMinimalFreeComplex.ofLevel hA)) :
    HasGradedResolutionPackage I e :=
  hasGradedResolutionPackage_of_canonicalLast_and_matlisAnnihilator
    e I hA L (MatlisAnnihilatorGorensteinProperty.ofLevel hA)

/-- End-to-end theorem after the two irreducible local-algebra constructions
have been supplied.  All free-basis reindexing, localized exactness,
degreewise presentations, and package assembly are discharged internally. -/
theorem theorem1_modulo_Stanley_of_reduced_data
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (L : CanonicalLastDifferentialData
      (GradedMinimalFreeComplex.ofLevel hA))
    (P : let C := GradedMinimalFreeComplex.ofLevel hA
      let D := GradedResolutionDuality.ofCanonicalLast hA C L
      CriticalBranchAlgebraPackage C D)
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 := by
  exact theorem1_of_hasGradedResolutionPackage e I hA
    (hasGradedResolutionPackage_of_reduced_data e I hA L P) hStanley

theorem theorem1_modulo_Stanley_of_canonicalLast_and_matlisAnnihilator
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (L : CanonicalLastDifferentialData
      (GradedMinimalFreeComplex.ofLevel hA))
    (G : MatlisAnnihilatorGorensteinProperty hA)
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 := by
  exact theorem1_of_hasGradedResolutionPackage e I hA
    (hasGradedResolutionPackage_of_canonicalLast_and_matlisAnnihilator
      e I hA L G) hStanley

theorem theorem1_modulo_Stanley_of_canonicalLast
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (L : CanonicalLastDifferentialData
      (GradedMinimalFreeComplex.ofLevel hA))
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 := by
  exact theorem1_of_hasGradedResolutionPackage e I hA
    (hasGradedResolutionPackage_of_canonicalLast e I hA L) hStanley

/-! The numerical theorem is now available as a checked wrapper over the
resolution package.  The only extra hypothesis in this wrapper is the
explicit package-existence proposition; the hA-only construction remains the
endpoint still to be supplied. -/

theorem theorem1_modulo_Stanley_of_hasGradedResolutionPackage
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (hResolution : HasGradedResolutionPackage I e)
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 := by
  exact theorem1_of_hasGradedResolutionPackage e I hA hResolution hStanley

/-! ## The current trust boundary

The last-differential record is now derived from the single homological
statement that the Matlis dual has last Betti number one — equivalently that
the third free module of its minimal graded resolution has rank one.  The two
theorems below are therefore the sharp form of the development: apart from
Stanley's theorem, the only remaining input is `hBetti`. -/

theorem hasGradedResolutionPackage_of_lastBetti
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (hBetti : Fintype.card (GradedMinimalFreeComplex.ofLevel hA).β₃ = 1) :
    HasGradedResolutionPackage I e :=
  hasGradedResolutionPackage_of_canonicalLast e I hA
    (CanonicalLastDifferentialData.ofCardBeta₃ _ hBetti)

theorem theorem1_modulo_Stanley_of_lastBetti
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (hBetti : Fintype.card (GradedMinimalFreeComplex.ofLevel hA).β₃ = 1)
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 :=
  theorem1_of_hasGradedResolutionPackage e I hA
    (hasGradedResolutionPackage_of_lastBetti e I hA hBetti) hStanley

end LogConcavity

#print axioms LogConcavity.CanonicalLastDifferentialData.toLastDifferentialCertificate
#print axioms LogConcavity.r3_primitive_pair_factorization
#print axioms LogConcavity.rank_one_low_range_eq_primitive_ideal
#print axioms LogConcavity.rank_one_critical_equation7
#print axioms LogConcavity.equation7_low_mem_iff_matlisAnnihilator
#print axioms LogConcavity.criticalBranchAlgebraPackage_of_matlisAnnihilator
#print axioms LogConcavity.CriticalBranchAlgebraData.toCriticalBranchCertificate
#print axioms LogConcavity.hasGradedResolutionPackage_of_canonicalLast_and_matlisAnnihilator
#print axioms LogConcavity.theorem1_modulo_Stanley_of_reduced_data
#print axioms LogConcavity.CanonicalLastDifferentialData.ofCardBeta₃
#print axioms LogConcavity.theorem1_modulo_Stanley_of_lastBetti
