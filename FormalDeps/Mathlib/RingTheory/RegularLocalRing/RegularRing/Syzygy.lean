/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.RegularLocalRing.RegularRing.GlobalDimension
import Mathlib.RingTheory.RegularLocalRing.RegularRing.Polynomial

/-!

# Hilbert's Syzygy Theorem

Note: this file is deliberately a legacy (non-`module`) file, matching
`RegularRing/Polynomial.lean` which it imports.

-/

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing

lemma IsRegularLocalRing.of_isField (h : IsField R) : IsRegularLocalRing R := by
  let _ : Field R := h.toField
  apply (isRegularLocalRing_iff R).mpr
  simp [maximalIdeal_eq_bot]

lemma IsRegularRing.of_isField (h : IsField R) : IsRegularRing R := by
  let _ : Field R := h.toField
  refine isRegularRing_iff.mpr (fun p hp ↦ ?_)
  have nmem : 0 ∉ p.primeCompl := by simp
  let _ := IsRegularLocalRing.of_isField R h
  exact IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective
    (algebraMap R (Localization.AtPrime p)) (Field.localization_map_bijective nmem))

lemma IsRegularLocalRing.of_isRegularRing [IsLocalRing R] [IsRegularRing R] :
    IsRegularLocalRing R :=
  IsRegularLocalRing.of_isRegularRing_of_isLocalRing R

lemma IsRegularLocalRing.of_isDVR [IsDomain R] [IsDiscreteValuationRing R] :
    IsRegularLocalRing R := by
  apply (isRegularLocalRing_iff R).mpr (le_antisymm _ (ringKrullDim_le_spanFinrank_maximalIdeal R))
  simp only [(IsPrincipalIdealRing.ringKrullDim_eq_one R) (IsDiscreteValuationRing.not_isField R),
    Nat.cast_le_one]
  rcases IsPrincipalIdealRing.principal (maximalIdeal R) with ⟨x, hx⟩
  rw [← Set.ncard_singleton x, hx]
  exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)

lemma IsRegularRing.of_isPID [IsDomain R] [IsPrincipalIdealRing R] : IsRegularRing R := by
  by_cases isf : IsField R
  · exact IsRegularRing.of_isField R isf
  · refine isRegularRing_iff.mpr (fun p hp ↦ ?_)
    by_cases eqbot : p = ⊥
    · have : IsField (Localization.AtPrime p) := by
        rw [isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
        simp [eqbot]
      exact IsRegularLocalRing.of_isField _ this
    · have : p.IsMaximal := IsPrime.to_maximal_ideal eqbot
      apply (isRegularLocalRing_iff _).mpr
        (le_antisymm _ (ringKrullDim_le_spanFinrank_maximalIdeal _))
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p,
        IsPrincipalIdealRing.height_eq_one_of_isMaximal p isf,
        ← Localization.AtPrime.map_eq_maximalIdeal, WithBot.coe_one, Nat.cast_le_one]
      rcases IsPrincipalIdealRing.principal p with ⟨x, hx⟩
      simp only [hx, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
      exact le_of_le_of_eq (Submodule.spanFinrank_span_le_ncard_of_finite
        (Set.finite_singleton _)) (Set.ncard_singleton _)

theorem Hilberts_Syzygy (k : Type u) [Field k] [Small.{v, u} k] (n : ℕ) :
    globalDimension.{v} (MvPolynomial (Fin n) k) = n := by
  let _ : IsRegularRing k := IsRegularRing.of_isField k (Field.toIsField k)
  let _ : IsRegularRing (MvPolynomial (Fin n) k) := MvPolynomial.isRegularRing_of_isRegularRing k n
  simp [IsRegularRing.globalDimension_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
