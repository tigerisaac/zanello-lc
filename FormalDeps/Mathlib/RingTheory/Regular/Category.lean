/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Categorical constructions for `IsSMulRegular`
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Abelian Ideal Pointwise

lemma LinearMap.exact_lsmul_mkQ_smul_top (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]

alias LinearMap.exact_smul_id_smul_top_mkQ := LinearMap.exact_lsmul_mkQ_smul_top

namespace ModuleCat

/-- The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x : R` on `M`. -/
@[simps!]
def smulShortComplex (r : R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ
    (LinearMap.exact_lsmul_mkQ_smul_top M r).linearMap_comp_eq_zero

@[simp]
lemma smulShortComplex_f_eq_smul_id (r : R) : (M.smulShortComplex r).f = r • 𝟙 M := rfl

lemma smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact :=
  ModuleCat.shortComplex_exact _ (LinearMap.exact_lsmul_mkQ_smul_top M r)

instance smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g := by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

end ModuleCat

variable {M} in
lemma IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (ModuleCat.smulShortComplex M r).ShortExact where
  exact := ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using! reg

lemma Submodule.smul_top_eq_comap_smul_top_of_surjective {R M M₂ : Type*} [CommSemiring R]
    [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R M₂] (I : Ideal R) (f : M →ₗ[R] M₂)
    (h : Function.Surjective f) : I • ⊤ ⊔ (LinearMap.ker f) = comap f (I • ⊤) := by
  have hsmul : I • (⊤ : Submodule R M) ≤ comap f (I • ⊤) :=
    Submodule.map_le_iff_le_comap.mp <| le_of_eq_of_le
      (Submodule.map_smul'' _ _ _) (smul_mono_right _ le_top)
  refine le_antisymm (sup_le hsmul (LinearMap.ker_le_comap f)) ?_
  rw [← Submodule.comap_map_eq f (I • (⊤ : Submodule R M)),
    Submodule.comap_le_comap_iff_of_surjective h,
    Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr h]

open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian Pointwise
variable {R : Type u} [CommRing R] [Small.{v} R] {M N : ModuleCat.{v} R} {n : ℕ}
  [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

lemma ext_hom_eq_zero_of_mem_ann {r : R} (mem_ann : r ∈ Module.annihilator R N) (n : ℕ) :
    AddCommGrpCat.ofHom (((Ext.mk₀ (r • (𝟙 M)))).postcomp N (add_zero n)) = 0 := by
  ext h
  have smul (L : ModuleCat.{v} R): Ext.mk₀ (r • 𝟙 L) = r • Ext.mk₀ (𝟙 L) := by
    simp [Ext.smul_eq_comp_mk₀]
  have eq0 : r • (𝟙 N) = 0 := ModuleCat.hom_ext
    (LinearMap.ext (fun x ↦ Module.mem_annihilator.mp mem_ann _))
  have : r • h = (Ext.mk₀ (r • (𝟙 N))).comp h (zero_add n) := by simp [smul]
  simp only [smul, AddCommGrpCat.hom_ofHom, AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply,
    Ext.comp_smul, Ext.comp_mk₀_id, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
  simp [this, eq0]
