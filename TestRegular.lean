import LogConcavity
import GradedResolution
import Mathlib.RingTheory.MvPolynomial.Ideal
import FormalDeps.Port.Mathlib.RingTheory.Regular.Depth

open scoped BigOperators

namespace LogConcavity

universe u
variable {k : Type u} [Field k]

open MvPolynomial Module

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
  have hsupport := (MvPolynomial.mem_ideal_span_X_image.mp hf')
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

lemma variables_isWeaklyRegular :
    RingTheory.Sequence.IsWeaklyRegular (R3 k)
      [MvPolynomial.X (R := k) (0 : Fin 3), MvPolynomial.X (R := k) (1 : Fin 3),
        MvPolynomial.X (R := k) (2 : Fin 3)] := by
  rw [RingTheory.Sequence.isWeaklyRegular_iff]
  intro i hi
  have hi3 : i < 3 := by simpa using hi
  interval_cases i
  · simpa using
      (X_isSMulRegular_mod_span (k := k) (∅ : Set (Fin 3)) (0 : Fin 3) (by simp))
  · simpa [Ideal.ofList_singleton] using
      (X_isSMulRegular_mod_span (k := k) ({0} : Set (Fin 3)) (1 : Fin 3) (by simp))
  · simpa [Ideal.ofList_cons, Ideal.ofList_singleton, sup_comm] using
      (X_isSMulRegular_mod_span (k := k) ({0, 1} : Set (Fin 3)) (2 : Fin 3) (by simp))

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
      simp only [List.mem_cons, List.mem_singleton] at hf
      rcases hf with rfl | rfl | rfl <;>
        exact Ideal.subset_span (Set.mem_range_self _)
    · apply Ideal.span_le.mpr
      rintro f ⟨i, rfl⟩
      fin_cases i <;> apply Ideal.subset_span <;> simp [xs]
  have hone : (1 : R3 k) ∈ Ideal.ofList xs := by
    have : (1 : R3 k) ∈
        Ideal.ofList xs •
          (⊤ : Submodule (R3 k) (R3 k)) := by
      rw [← htop]
      trivial
    simpa only [smul_eq_mul, Ideal.mul_top] using this
  rw [hlist] at hone
  have hc : MvPolynomial.C (1 : k) ∈
      MvPolynomial.idealOfVars (Fin 3) k ^ 1 := by simpa using hone
  have h := (MvPolynomial.C_mem_pow_idealOfVars_iff
    (sigma := Fin 3) (R := k) 1 1).mp hc
  simpa using h

example {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    Module.Finite (R3 k) (MatlisDual I) := by infer_instance

example {I : Ideal (R3 k)} {e : ℕ} (hA : IsTypeTwoLevel I e) :
    Nontrivial (MatlisDual I) := by infer_instance

open CategoryTheory Abelian

lemma dualMap_surjective_of_ext_one_subsingleton
    {R K F M : Type*} [CommRing R] [Small.{u} R]
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
  apply LinearMap.ext
  intro y
  have hx' := congrArg ModuleCat.Hom.hom
    ((Ext.mk₀_bijective _ _).injective hx)
  simpa [psi, LinearMap.dualMap_apply, Ext.bilinearComp_apply_apply,
    Ext.mk₀_comp_mk₀] using DFunLike.congr_fun hx' y

end LogConcavity
