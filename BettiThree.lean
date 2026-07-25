import ModuloStanley
import KoszulHomology

/-!
# The last Betti number is one

This file discharges `hBetti`, the single non-Stanley hypothesis of
[`ModuloStanley.lean`](ModuloStanley.lean), by instantiating the Koszul
machinery of [`KoszulHomology.lean`](KoszulHomology.lean) at the minimal
graded free complex of the Matlis dual.

The complex `C` resolves `MatlisDual I`:

```
(β₃ → R) --d₃--> (β₂ → R) --d₂--> (β₁ → R) --d₁--> (Fin 2 → R) --inverseSystemMap--> MatlisDual I → 0
```

is exact, `d₃` is injective, the free modules are Koszul-acyclic, and
minimality of `d₃` says its entries lie in the irrelevant ideal, hence its
image lies in `m (β₂ → R)`.  So `socleEquivH₀OfResolution` applies and gives

```
Soc (MatlisDual I) ≅ (β₃ → R) ⧸ m (β₃ → R),
```

whose `k`-dimensions are `1` (`matlisDualSocle_finrank`) and
`Fintype.card β₃` (`finrank_H₀Pi`) respectively.
-/

open scoped BigOperators

namespace LogConcavity

universe u
variable {k : Type u} [Field k]

open MvPolynomial Module Koszul
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Classical.decEq
attribute [local instance] GradedMinimalFreeComplex.fintype₁
attribute [local instance] GradedMinimalFreeComplex.fintype₂
attribute [local instance] GradedMinimalFreeComplex.fintype₃

variable {I : Ideal (R3 k)} {e : ℕ}

/-- Minimality of the last differential, in the form the Koszul chain wants:
its image lies in `m F₂`, the degree-one Koszul boundaries of `F₂`. -/
lemma range_d₃_le_range_koszulD₁ (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex.{u, 0, 0, 0} I e hA) :
    LinearMap.range C.d₃ ≤ LinearMap.range (d₁ k (C.β₂ → R3 k)) := by
  rintro _ ⟨x, rfl⟩
  apply mem_range_d₁_pi_of_entries_mem
  intro g
  rw [← single_expansion x, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ ?_
  exact C.d₃_minimal a g

/-- The socle of the Matlis dual is the top of the resolution: the Koszul
chain applied to the minimal graded free complex. -/
noncomputable def socleEquivLastFree (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex.{u, 0, 0, 0} I e hA) :
    LinearMap.ker (d₃ k (MatlisDual I)) ≃ₗ[R3 k] H₀ k (C.β₃ → R3 k) :=
  socleEquivH₀OfResolution C.d₁ C.d₂ C.d₃ (inverseSystemMap hA)
    (inverseSystemMap_surjective hA) C.d₁_range.symm C.d₂_range.symm C.d₃_range.symm
    C.d₃_injective (range_d₃_le_range_koszulD₁ hA C) acyclic_pi acyclic_pi acyclic_pi

/-- The top of the Koszul complex on the Matlis dual is its socle, as computed
in `ModuloStanley`. -/
lemma restrictScalars_ker_d₃_eq_matlisDualSocle (hA : IsTypeTwoLevel I e) :
    (LinearMap.ker (d₃ k (MatlisDual I))).restrictScalars k = matlisDualSocle hA := by
  ext φ
  simp only [Submodule.restrictScalars_mem]
  exact mem_ker_d₃_iff φ

/-- **The last Betti number is one.**  The third free module of the minimal
graded free complex of the Matlis dual has rank one, because that rank is the
`k`-dimension of the socle of the Matlis dual, which is one. -/
theorem card_beta₃_eq_one (hA : IsTypeTwoLevel I e)
    (C : GradedMinimalFreeComplex.{u, 0, 0, 0} I e hA) :
    Fintype.card C.β₃ = 1 := by
  -- the socle, as a `k`-vector space, is the reduction of the last free module
  have hequiv : LinearMap.ker (d₃ k (MatlisDual I)) ≃ₗ[k] H₀ k (C.β₃ → R3 k) :=
    (socleEquivLastFree hA C).restrictScalars k
  have hcard : finrank k (LinearMap.ker (d₃ k (MatlisDual I))) = Fintype.card C.β₃ := by
    rw [hequiv.finrank_eq, finrank_H₀Pi]
  -- and it is one-dimensional
  have hone : finrank k (LinearMap.ker (d₃ k (MatlisDual I))) = 1 := by
    have h := congrArg (fun p : Submodule k (MatlisDual I) => finrank k p)
      (restrictScalars_ker_d₃_eq_matlisDualSocle hA)
    rw [matlisDualSocle_finrank hA] at h
    exact h
  omega

/-- `hBetti`, discharged for the canonical complex. -/
theorem card_beta₃_ofLevel_eq_one (hA : IsTypeTwoLevel I e) :
    Fintype.card (GradedMinimalFreeComplex.ofLevel hA).β₃ = 1 :=
  card_beta₃_eq_one hA _

/-- **Theorem 1, modulo Stanley's theorem only.**  Log-concavity of the
Hilbert function of a codimension-three type-two level algebra, with
`IsTypeTwoLevel` and Stanley's theorem as the only inputs. -/
theorem theorem1_modulo_Stanley
    (e : ℕ) (I : Ideal (R3 k)) (hA : IsTypeTwoLevel I e)
    (hStanley : ∀ B E, GorensteinQuotientHF k B E →
      ∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ E → B j ≤ B i) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (e : ℤ) - 1 →
      hilb I (i - 1) * hilb I (i + 1) ≤ hilb I i ^ 2 :=
  theorem1_modulo_Stanley_of_lastBetti e I hA (card_beta₃_ofLevel_eq_one hA) hStanley

end LogConcavity

/-! ## Axiom audit -/

#print axioms LogConcavity.card_beta₃_eq_one
#print axioms LogConcavity.card_beta₃_ofLevel_eq_one
#print axioms LogConcavity.theorem1_modulo_Stanley
