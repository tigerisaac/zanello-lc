import FormalDeps.Port.Mathlib.RingTheory.RegularLocalRing.RegularRing.Syzygy
import FormalDeps.Port.Mathlib.RingTheory.GlobalDimension

/-!
The source files below are a project-local import of the ported `Mathlib.*`
modules. The one copied category file only adds declarations missing from the
stock Mathlib module; the remaining ported declarations use their upstream
names so downstream proofs can use the existing APIs unchanged.
-/

namespace FormalDeps

universe u v

open CategoryTheory

variable {k : Type u} [Field k] [Small.{v, u} k]

/-- Hilbert's syzygy theorem exposed through the project-local FormalDeps
bridge.  The declaration is intentionally a thin alias: the proof remains
the audited port in `FormalDeps/Port`. -/
theorem hilbertsSyzygy (n : ℕ) :
    _root_.globalDimension.{v} (MvPolynomial (Fin n) k) = n := by
  exact _root_.Hilberts_Syzygy k n

/-- The project-facing projective-dimension consequence of the global
dimension computation.  It is stated for all modules, hence in particular
for finitely generated modules. -/
theorem projectiveDimensionLEOfPolynomial
    (n : ℕ) (M : ModuleCat.{v} (MvPolynomial (Fin n) k)) :
    HasProjectiveDimensionLE M n := by
  apply (_root_.globalDimension_le_iff
    (MvPolynomial (Fin n) k) n).mp
  rw [hilbertsSyzygy]

end FormalDeps

/-! ## Axiom audit for the imported homological prerequisites

These are the ported results the main development relies on.  They are
audited here, inside the ordinary `lake build`, so CI checks them on every
run together with everything else. -/

#print axioms Hilberts_Syzygy
#print axioms AuslanderBuchsbaum
#print axioms depth_le_ringKrullDim
#print axioms IsRegularLocalRing.globalDimension_eq_ringKrullDim
#print axioms IsRegularRing.globalDimension_eq_ringKrullDim
#print axioms Polynomial.isRegularRing_of_isRegularRing
#print axioms MvPolynomial.isRegularRing_of_isRegularRing
#print axioms free_of_isMaximalCohenMacaulay_of_isRegularLocalRing
#print axioms FormalDeps.hilbertsSyzygy
#print axioms FormalDeps.projectiveDimensionLEOfPolynomial
