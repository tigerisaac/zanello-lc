import LogConcavity

open scoped BigOperators

namespace LogConcavity

variable {k : Type*} [Field k]

open Module

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000

/-- The full `k`-linear dual of the Artinian quotient.  A wrapper keeps its
contragredient `R`-action distinct from the ordinary pointwise actions on
linear maps. -/
@[ext]
structure MatlisDual (I : Ideal (R3 k)) where
  val : Module.Dual k (R3 k ⧸ I)

noncomputable def matlisDualEquiv (I : Ideal (R3 k)) :
    MatlisDual I ≃ Module.Dual k (R3 k ⧸ I) where
  toFun := MatlisDual.val
  invFun := MatlisDual.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

noncomputable instance (I : Ideal (R3 k)) : AddCommGroup (MatlisDual I) :=
  Equiv.addCommGroup (matlisDualEquiv I)

noncomputable instance (I : Ideal (R3 k)) : Module k (MatlisDual I) :=
  Equiv.module k (matlisDualEquiv I)

noncomputable instance (I : Ideal (R3 k)) : CoeFun (MatlisDual I)
    (fun _ => (R3 k ⧸ I) → k) where
  coe φ := φ.val

@[simp] lemma matlisDual_apply_mk (I : Ideal (R3 k))
    (φ : Module.Dual k (R3 k ⧸ I)) (x : R3 k ⧸ I) :
    (MatlisDual.mk φ : MatlisDual I) x = φ x := rfl

@[simp] lemma matlisDual_add_apply (I : Ideal (R3 k))
    (φ ψ : MatlisDual I) (x : R3 k ⧸ I) :
    (φ + ψ) x = φ x + ψ x := rfl

@[simp] lemma matlisDual_k_smul_apply (I : Ideal (R3 k))
    (c : k) (φ : MatlisDual I) (x : R3 k ⧸ I) :
    (c • φ) x = c * φ x := rfl

/-- Multiplication by a polynomial on the quotient, as a `k`-linear map. -/
noncomputable def quotientMul (I : Ideal (R3 k)) (r : R3 k) :
    (R3 k ⧸ I) →ₗ[k] (R3 k ⧸ I) :=
  LinearMap.mulLeft k (Ideal.Quotient.mk I r)

@[simp] lemma quotientMul_apply (I : Ideal (R3 k)) (r : R3 k) (x : R3 k ⧸ I) :
    quotientMul I r x = Ideal.Quotient.mk I r * x := rfl

/-- The contragredient polynomial action on the full dual. -/
noncomputable instance matlisDualSMul (I : Ideal (R3 k)) :
    SMul (R3 k) (MatlisDual I) where
  smul r φ := ⟨(quotientMul I r).dualMap φ.val⟩

@[simp] lemma matlisDual_smul_apply (I : Ideal (R3 k)) (r : R3 k)
    (φ : MatlisDual I) (x : R3 k ⧸ I) :
    (r • φ) x = φ (Ideal.Quotient.mk I r * x) := rfl

noncomputable instance matlisDualModule (I : Ideal (R3 k)) :
    Module (R3 k) (MatlisDual I) :=
  Module.ofMinimalAxioms
    (fun _ _ _ => rfl)
    (fun r s φ => by
      apply MatlisDual.ext
      apply LinearMap.ext
      intro x
      change φ (Ideal.Quotient.mk I (r + s) * x) =
        φ (Ideal.Quotient.mk I r * x) + φ (Ideal.Quotient.mk I s * x)
      rw [map_add, add_mul, φ.val.map_add])
    (fun r s φ => by
      apply MatlisDual.ext
      apply LinearMap.ext
      intro x
      change φ (Ideal.Quotient.mk I (r * s) * x) =
        φ (Ideal.Quotient.mk I s * (Ideal.Quotient.mk I r * x))
      rw [map_mul (Ideal.Quotient.mk I),
        mul_comm (Ideal.Quotient.mk I r) (Ideal.Quotient.mk I s), mul_assoc])
    (fun φ => by
      apply MatlisDual.ext
      apply LinearMap.ext
      intro x
      change φ (Ideal.Quotient.mk I 1 * x) = φ x
      rw [map_one, one_mul])

@[simp] lemma matlisDual_C_smul (I : Ideal (R3 k)) (c : k) (φ : MatlisDual I) :
    (MvPolynomial.C c : R3 k) • φ = c • φ := by
  apply MatlisDual.ext
  apply LinearMap.ext
  intro x
  change φ (Ideal.Quotient.mk I (algebraMap k (R3 k) c) * x) = c * φ x
  rw [Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def, map_smul]
  rfl

noncomputable instance matlisDualScalarTower (I : Ideal (R3 k)) :
    IsScalarTower k (R3 k) (MatlisDual I) :=
  IsScalarTower.of_algebraMap_smul (A := R3 k) (M := MatlisDual I) fun c φ => by
    rw [show algebraMap k (R3 k) c = MvPolynomial.C c from rfl]
    exact matlisDual_C_smul I c φ

noncomputable instance matlisDual_finiteDimensional (I : Ideal (R3 k))
    [FiniteDimensional k (R3 k ⧸ I)] : FiniteDimensional k (MatlisDual I) := by
  let f : MatlisDual I →ₗ[k] Module.Dual k (R3 k ⧸ I) :=
    { toFun := MatlisDual.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective f fun x y h => MatlisDual.ext h

noncomputable instance matlisDual_isArtinian (I : Ideal (R3 k))
    [FiniteDimensional k (R3 k ⧸ I)] : IsArtinian (R3 k) (MatlisDual I) :=
  isArtinian_of_tower k inferInstance

/-- The degree-`n` projection on a homogeneous quotient. -/
noncomputable def quotientComponent (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)) (n : ℕ) :
    (R3 k ⧸ I) →ₗ[k] (R3 k ⧸ I) :=
  Submodule.liftQ (I.restrictScalars k)
    ((Ideal.Quotient.mkₐ k I).toLinearMap.comp
      (MvPolynomial.homogeneousComponent n)) (by
        intro f hf
        rw [LinearMap.mem_ker]
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [← MvPolynomial.decomposition.decompose'_apply]
        exact hI n hf)

@[simp] lemma quotientComponent_mk (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)) (n : ℕ) (f : R3 k) :
    quotientComponent I hI n (Ideal.Quotient.mk I f) =
      Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent n f) := by
  rfl

lemma quotientComponent_mem_quotPiece (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    (n : ℕ) (x : R3 k ⧸ I) : quotientComponent I hI n x ∈ quotPiece I n := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientComponent_mk]
  exact Submodule.mem_map.mpr
    ⟨MvPolynomial.homogeneousComponent n f,
      MvPolynomial.homogeneousComponent_mem n f, rfl⟩

lemma quotientComponent_eq_self_of_mem (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    (n : ℕ) {x : R3 k ⧸ I} (hx : x ∈ quotPiece I n) :
    quotientComponent I hI n x = x := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  change quotientComponent I hI n (Ideal.Quotient.mk I f) = Ideal.Quotient.mk I f
  rw [quotientComponent_mk,
    MvPolynomial.homogeneousComponent_of_mem hf, if_pos rfl]

lemma quotientComponent_eq_zero_of_mem (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    {m n : ℕ} (hmn : m ≠ n) {x : R3 k ⧸ I} (hx : x ∈ quotPiece I n) :
    quotientComponent I hI m x = 0 := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  change quotientComponent I hI m (Ideal.Quotient.mk I f) = 0
  rw [quotientComponent_mk,
    MvPolynomial.homogeneousComponent_of_mem hf, if_neg hmn, map_zero]

/-- Projection of the full Matlis dual onto functionals supported in degree `n`. -/
noncomputable def matlisComponent (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)) (n : ℕ) :
    MatlisDual I →ₗ[k] MatlisDual I where
  toFun φ := ⟨(quotientComponent I hI n).dualMap φ.val⟩
  map_add' := fun _ _ => MatlisDual.ext rfl
  map_smul' := fun _ _ => MatlisDual.ext rfl

@[simp] lemma matlisComponent_apply (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    (n : ℕ) (φ : MatlisDual I) (x : R3 k ⧸ I) :
    matlisComponent I hI n φ x = φ (quotientComponent I hI n x) := rfl

/-- The homogeneous degree dual to the degree-`n` quotient piece. -/
noncomputable def matlisPiece (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)) (n : ℕ) :
    Submodule k (MatlisDual I) := LinearMap.range (matlisComponent I hI n)

/-- Restrict a homogeneous Matlis functional to its quotient piece. -/
noncomputable def matlisPieceRestrict (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)) (n : ℕ) :
    matlisPiece I hI n →ₗ[k] Module.Dual k (quotPiece I n) where
  toFun φ := φ.1.val.comp (quotPiece I n).subtype
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

lemma matlisPiece_apply_projection (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    (n : ℕ) (φ : matlisPiece I hI n) (x : R3 k ⧸ I) :
    φ.1 x = φ.1 (quotientComponent I hI n x) := by
  obtain ⟨ψ, hψ⟩ := φ.2
  have hproj := quotientComponent_eq_self_of_mem I hI n
    (quotientComponent_mem_quotPiece I hI n x)
  change φ.1.val x = φ.1.val (quotientComponent I hI n x)
  rw [← hψ]
  change ψ.val (quotientComponent I hI n x) =
    ψ.val (quotientComponent I hI n (quotientComponent I hI n x))
  rw [hproj]

theorem matlisPieceRestrict_bijective (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)) (n : ℕ) :
    Function.Bijective (matlisPieceRestrict I hI n) := by
  constructor
  · intro φ ψ h
    apply Subtype.ext
    apply MatlisDual.ext
    apply LinearMap.ext
    intro x
    rw [matlisPiece_apply_projection I hI n φ x,
      matlisPiece_apply_projection I hI n ψ x]
    have hx := quotientComponent_mem_quotPiece I hI n x
    exact DFunLike.congr_fun h ⟨quotientComponent I hI n x, hx⟩
  · intro ell
    let proj : (R3 k ⧸ I) →ₗ[k] quotPiece I n :=
      LinearMap.codRestrict (quotPiece I n) (quotientComponent I hI n)
        (quotientComponent_mem_quotPiece I hI n)
    let φ : MatlisDual I := ⟨ell.comp proj⟩
    have hfixed : matlisComponent I hI n φ = φ := by
      apply MatlisDual.ext
      apply LinearMap.ext
      intro x
      change ell (proj (quotientComponent I hI n x)) = ell (proj x)
      apply congrArg ell
      apply Subtype.ext
      exact quotientComponent_eq_self_of_mem I hI n
        (quotientComponent_mem_quotPiece I hI n x)
    let φ' : matlisPiece I hI n := ⟨φ, ⟨φ, hfixed⟩⟩
    refine ⟨φ', ?_⟩
    apply LinearMap.ext
    intro x
    change ell (proj x.1) = ell x
    apply congrArg ell
    apply Subtype.ext
    exact quotientComponent_eq_self_of_mem I hI n x.2

/-- A homogeneous piece of the full Matlis dual is exactly the dual of the
corresponding quotient piece. -/
noncomputable def matlisPieceEquiv (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)) (n : ℕ) :
    matlisPiece I hI n ≃ₗ[k] Module.Dual k (quotPiece I n) :=
  LinearEquiv.ofBijective (matlisPieceRestrict I hI n)
    (matlisPieceRestrict_bijective I hI n)

lemma finrank_matlisPiece (I : Ideal (R3 k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)) (n : ℕ) :
    finrank k (matlisPiece I hI n) = finrank k (quotPiece I n) := by
  rw [(matlisPieceEquiv I hI n).finrank_eq, Subspace.dual_finrank_eq]

lemma quotientComponent_eq_zero_above {I : Ideal (R3 k)} {e n : ℕ}
    (hA : IsTypeTwoLevel I e) (hn : e < n) (x : R3 k ⧸ I) :
    quotientComponent I hA.homogeneous n x = 0 := by
  have hx := quotientComponent_mem_quotPiece I hA.homogeneous n x
  rw [hA.vanish_above n hn] at hx
  simpa using hx

/-- The quotient is the finite direct sum of its pieces through the socle
degree.  This is an equality of actual quotient elements, not just a Hilbert
function identity. -/
theorem sum_quotientComponent {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (x : R3 k ⧸ I) :
    (∑ n ∈ Finset.range (e + 1), quotientComponent I hA.homogeneous n x) = x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hfull :
      (∑ n ∈ Finset.range (f.totalDegree + 1),
        quotientComponent I hA.homogeneous n (Ideal.Quotient.mk I f)) =
          Ideal.Quotient.mk I f := by
    simp_rw [quotientComponent_mk]
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  by_cases hdeg : f.totalDegree ≤ e
  · calc
      _ = ∑ n ∈ Finset.range (f.totalDegree + 1),
          quotientComponent I hA.homogeneous n (Ideal.Quotient.mk I f) := by
        symm
        apply Finset.sum_subset
        · exact Finset.range_mono (Nat.add_le_add_right hdeg 1)
        · intro n hnE hnT
          have htd : f.totalDegree < n := by
            simp only [Finset.mem_range] at hnE hnT
            omega
          rw [quotientComponent_mk,
            MvPolynomial.homogeneousComponent_eq_zero n f htd, map_zero]
      _ = Ideal.Quotient.mk I f := hfull
  · calc
      _ = ∑ n ∈ Finset.range (f.totalDegree + 1),
          quotientComponent I hA.homogeneous n (Ideal.Quotient.mk I f) := by
        apply Finset.sum_subset
        · exact Finset.range_mono
            (Nat.add_le_add_right (by omega : e ≤ f.totalDegree) 1)
        · intro n hnT hnE
          simp only [Finset.mem_range] at hnT hnE
          exact quotientComponent_eq_zero_above hA (by omega) _
      _ = Ideal.Quotient.mk I f := hfull

noncomputable def matlisEval (I : Ideal (R3 k)) (x : R3 k ⧸ I) :
    MatlisDual I →ₗ[k] k where
  toFun phi := phi x
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] lemma matlisEval_apply (I : Ideal (R3 k)) (x : R3 k ⧸ I)
    (phi : MatlisDual I) : matlisEval I x phi = phi x := rfl

/-- The dual projections also sum to the identity. -/
theorem sum_matlisComponent {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (phi : MatlisDual I) :
    (∑ n ∈ Finset.range (e + 1), matlisComponent I hA.homogeneous n phi) = phi := by
  apply MatlisDual.ext
  apply LinearMap.ext
  intro x
  change matlisEval I x
      (∑ n ∈ Finset.range (e + 1), matlisComponent I hA.homogeneous n phi) =
    matlisEval I x phi
  rw [map_sum]
  simp_rw [show ∀ n, matlisEval I x (matlisComponent I hA.homogeneous n phi) =
    phi (quotientComponent I hA.homogeneous n x) from fun _ => rfl]
  rw [← map_sum, sum_quotientComponent hA x]
  rfl

/-- The grading on the Matlis dual, reindexed so that duals of the top
quotient piece have degree zero. -/
noncomputable def reversedMatlisPiece {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (d : ℕ) : Submodule k (MatlisDual I) :=
  if d ≤ e then matlisPiece I hA.homogeneous (e - d) else ⊥

/-- The reindexed piece is the vector-space dual used by the numerical
development. -/
noncomputable def reversedMatlisPieceEquiv {I : Ideal (R3 k)} {e d : ℕ}
    (hA : IsTypeTwoLevel I e) (hd : d ≤ e) :
    reversedMatlisPiece hA d ≃ₗ[k] gradedDualPiece I e d := by
  rw [reversedMatlisPiece, if_pos hd]
  exact matlisPieceEquiv I hA.homogeneous (e - d)

lemma finrank_reversedMatlisPiece {I : Ideal (R3 k)} {e d : ℕ}
    (hA : IsTypeTwoLevel I e) (hd : d ≤ e) :
    finrank k (reversedMatlisPiece hA d) = finrank k (quotPiece I (e - d)) := by
  rw [(reversedMatlisPieceEquiv hA hd).finrank_eq,
    Subspace.dual_finrank_eq]

/-- Taking the degree-`n` component of a product by a homogeneous degree-`m`
polynomial takes the degree-`n-m` component of the other factor. -/
lemma homogeneousComponent_mul_left {m n : ℕ} {r f : R3 k}
    (hr : MvPolynomial.IsHomogeneous r m) (hmn : m ≤ n) :
    MvPolynomial.homogeneousComponent n (r * f) =
      r * MvPolynomial.homogeneousComponent (n - m) f := by
  rw [← MvPolynomial.decomposition.decompose'_apply,
    ← MvPolynomial.decomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_left_mem_of_le
    (MvPolynomial.homogeneousSubmodule (Fin 3) k)
    ((MvPolynomial.mem_homogeneousSubmodule m r).mpr hr) hmn

/-- Quotient degree projection commutes with multiplication by a homogeneous
polynomial, with the expected shift. -/
lemma quotientComponent_mul_left {I : Ideal (R3 k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    {m n : ℕ} {r : R3 k} (hr : MvPolynomial.IsHomogeneous r m)
    (hmn : m ≤ n) (x : R3 k ⧸ I) :
    quotientComponent I hI n (Ideal.Quotient.mk I r * x) =
      Ideal.Quotient.mk I r * quotientComponent I hI (n - m) x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, quotientComponent_mk, quotientComponent_mk,
    homogeneousComponent_mul_left hr hmn, map_mul]

/-- A homogeneous polynomial lowers the original support degree of a Matlis
functional. -/
lemma matlisPiece_smul {I : Ideal (R3 k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    {m n : ℕ} {r : R3 k} (hr : MvPolynomial.IsHomogeneous r m)
    (hmn : m ≤ n) {phi : MatlisDual I} (hphi : phi ∈ matlisPiece I hI n) :
    r • phi ∈ matlisPiece I hI (n - m) := by
  refine ⟨r • phi, ?_⟩
  apply MatlisDual.ext
  apply LinearMap.ext
  intro x
  change phi (Ideal.Quotient.mk I r * quotientComponent I hI (n - m) x) =
    phi (Ideal.Quotient.mk I r * x)
  rw [← quotientComponent_mul_left hI hr hmn]
  exact (matlisPiece_apply_projection I hI n ⟨phi, hphi⟩ _).symm

/-- In the reversed grading, homogeneous scalar multiplication raises
degree. -/
lemma reversedMatlisPiece_smul {I : Ideal (R3 k)} {e d m : ℕ}
    (hA : IsTypeTwoLevel I e) (hdm : d + m ≤ e)
    {r : R3 k} (hr : MvPolynomial.IsHomogeneous r m)
    {phi : MatlisDual I} (hphi : phi ∈ reversedMatlisPiece hA d) :
    r • phi ∈ reversedMatlisPiece hA (d + m) := by
  have hd : d ≤ e := by omega
  rw [reversedMatlisPiece, if_pos hd] at hphi
  rw [reversedMatlisPiece, if_pos hdm]
  have hm : m ≤ e - d := by omega
  have h := matlisPiece_smul hA.homogeneous hr hm hphi
  simpa [Nat.sub_sub] using h

lemma finrank_reversedMatlisPiece_zero {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) :
    finrank k (reversedMatlisPiece hA 0) = 2 := by
  rw [finrank_reversedMatlisPiece hA (Nat.zero_le e), Nat.sub_zero,
    ← hA.socle_eq, hA.type_two]

/-- Multiplication by a homogeneous polynomial sends an actual quotient
piece to the piece in the sum degree. -/
lemma quotPiece_mul_homogeneous {I : Ideal (R3 k)} {m n : ℕ}
    {r : R3 k} (hr : MvPolynomial.IsHomogeneous r m)
    {x : R3 k ⧸ I} (hx : x ∈ quotPiece I n) :
    Ideal.Quotient.mk I r * x ∈ quotPiece I (m + n) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨r * f, ?_, ?_⟩
  · exact (MvPolynomial.mem_homogeneousSubmodule (m + n) (r * f)).mpr
      (hr.mul ((MvPolynomial.mem_homogeneousSubmodule n f).mp hf))
  · simp [Ideal.Quotient.mkₐ_eq_mk, map_mul]

/-- Distinct homogeneous pieces of a homogeneous quotient intersect only in
zero. -/
lemma quotPiece_disjoint {I : Ideal (R3 k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    {m n : ℕ} (hmn : m ≠ n) {x : R3 k ⧸ I}
    (hm : x ∈ quotPiece I m) (hn : x ∈ quotPiece I n) : x = 0 := by
  have hself := quotientComponent_eq_self_of_mem I hI m hm
  have hzero := quotientComponent_eq_zero_of_mem I hI hmn hn
  rw [hself] at hzero
  exact hzero

/-- Every nonzero homogeneous quotient element can be multiplied to a
nonzero element in the top degree.  This is the elementary graded
essential-socle argument underlying inverse-system generation. -/
theorem exists_nonzero_top_product {I : Ideal (R3 k)} {e n : ℕ}
    (hA : IsTypeTwoLevel I e) (hne : n ≤ e)
    {x : R3 k ⧸ I} (hx : x ∈ quotPiece I n) (hx0 : x ≠ 0) :
    ∃ r : R3 k, MvPolynomial.IsHomogeneous r (e - n) ∧
      Ideal.Quotient.mk I r * x ≠ 0 := by
  classical
  let P : ℕ → Prop := fun q => ∃ r : R3 k,
    MvPolynomial.IsHomogeneous r q ∧ Ideal.Quotient.mk I r * x ≠ 0
  have hP0 : P 0 := by
    refine ⟨1, MvPolynomial.isHomogeneous_one (Fin 3) k, ?_⟩
    simpa using hx0
  let t := Nat.findGreatest P (e - n)
  have htP : P t := Nat.findGreatest_spec (Nat.zero_le (e - n)) hP0
  have htle : t ≤ e - n := Nat.findGreatest_le _
  obtain ⟨r, hr, hrx⟩ := htP
  have hteq : t = e - n := by
    by_contra hne'
    have htlt : t < e - n := lt_of_le_of_ne htle hne'
    let y : R3 k ⧸ I := Ideal.Quotient.mk I r * x
    have hy_piece : y ∈ quotPiece I (n + t) := by
      simpa [y, Nat.add_comm] using quotPiece_mul_homogeneous hr hx
    have hy_socle : y ∈ socle I := by
      intro j
      by_contra hkill
      have hPsucc : P (t + 1) := by
        refine ⟨MvPolynomial.X j * r, ?_, ?_⟩
        · simpa [Nat.add_comm] using
            (MvPolynomial.isHomogeneous_X k j).mul hr
        · rw [map_mul, mul_assoc]
          exact hkill
      have hsucc_le : t + 1 ≤ e - n := by omega
      have := Nat.le_findGreatest hsucc_le hPsucc
      change t + 1 ≤ t at this
      omega
    have hy_top : y ∈ quotPiece I e := hA.socle_concentrated hy_socle
    have hdegree : n + t ≠ e := by omega
    exact hrx (quotPiece_disjoint hA.homogeneous hdegree hy_piece hy_top)
  refine ⟨r, ?_, hrx⟩
  simpa [hteq] using hr

/-- A fixed two-element basis of the top-supported dual piece. -/
noncomputable def matlisTopBasis {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) :
    Basis (Fin 2) k (reversedMatlisPiece hA 0) := by
  letI := hA.finiteDimensional
  letI : FiniteDimensional k (reversedMatlisPiece hA 0) :=
    FiniteDimensional.of_injective (reversedMatlisPiece hA 0).subtype
      (reversedMatlisPiece hA 0).injective_subtype
  exact Module.finBasisOfFinrankEq k _ (finrank_reversedMatlisPiece_zero hA)

/-- The two actual inverse-system generators in the full Matlis dual. -/
noncomputable def matlisGenerator {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (i : Fin 2) : MatlisDual I :=
  (matlisTopBasis hA i).1

lemma matlisGenerator_mem_top {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (i : Fin 2) :
    matlisGenerator hA i ∈ matlisPiece I hA.homogeneous e := by
  have hi := (matlisTopBasis hA i).2
  simpa [reversedMatlisPiece, matlisGenerator] using hi

@[simp] lemma quotient_mk_smul (I : Ideal (R3 k)) (c : k) (r : R3 k) :
    Ideal.Quotient.mk I (c • r) = c • Ideal.Quotient.mk I r := by
  change Ideal.Quotient.mkₐ k I (c • r) = c • Ideal.Quotient.mkₐ k I r
  exact map_smul (Ideal.Quotient.mkₐ k I) c r

/-- Degree-`e-n` polynomial coefficients acting on the two top-dual basis
elements, restricted to `A_n`.  This is the genuine degree-`e-n` component
of the inverse-system presentation `R² → M`. -/
noncomputable def inverseSystemPieceMap {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (n : ℕ) :
    (Fin 2 → MvPolynomial.homogeneousSubmodule (Fin 3) k (e - n)) →ₗ[k]
      Module.Dual k (quotPiece I n) where
  toFun u :=
    { toFun := fun x => ∑ i : Fin 2,
        matlisGenerator hA i (Ideal.Quotient.mk I (u i).1 * x.1)
      map_add' := by
        intro x y
        simp only [Submodule.coe_add, mul_add, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Submodule.coe_smul_of_tower, mul_smul_comm, map_smul,
          RingHom.id_apply, Finset.smul_sum] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro x
    change (∑ i : Fin 2, matlisGenerator hA i
      (Ideal.Quotient.mk I ((u + v) i).1 * x.1)) =
      (∑ i : Fin 2, matlisGenerator hA i
        (Ideal.Quotient.mk I (u i).1 * x.1)) +
      ∑ i : Fin 2, matlisGenerator hA i
        (Ideal.Quotient.mk I (v i).1 * x.1)
    simp only [Pi.add_apply, Submodule.coe_add, map_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro x
    change (∑ i : Fin 2, matlisGenerator hA i
      (Ideal.Quotient.mk I ((c • u) i).1 * x.1)) =
      c • ∑ i : Fin 2, matlisGenerator hA i
        (Ideal.Quotient.mk I (u i).1 * x.1)
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, quotient_mk_smul,
      smul_mul_assoc, map_smul, Finset.smul_sum]

@[simp] lemma inverseSystemPieceMap_apply {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (n : ℕ)
    (u : Fin 2 → MvPolynomial.homogeneousSubmodule (Fin 3) k (e - n))
    (x : quotPiece I n) :
    inverseSystemPieceMap hA n u x = ∑ i : Fin 2,
      matlisGenerator hA i (Ideal.Quotient.mk I (u i).1 * x.1) := rfl

/-- The two top-dual generators, acted on in complementary degree, separate
every nonzero element of `A_n`. -/
theorem inverseSystemPieceMap_separates {I : Ideal (R3 k)} {e n : ℕ}
    (hA : IsTypeTwoLevel I e) (hne : n ≤ e) (x : quotPiece I n) (hx : x ≠ 0) :
    ∃ u : Fin 2 → MvPolynomial.homogeneousSubmodule (Fin 3) k (e - n),
      inverseSystemPieceMap hA n u x ≠ 0 := by
  obtain ⟨r, hr, hry⟩ := exists_nonzero_top_product hA hne x.2
    (fun h => hx (Subtype.ext h))
  have hy_mem : Ideal.Quotient.mk I r * x.1 ∈ quotPiece I e := by
    simpa [Nat.sub_add_cancel hne] using quotPiece_mul_homogeneous hr x.2
  let y : quotPiece I e := ⟨Ideal.Quotient.mk I r * x.1, hy_mem⟩
  have hy : y ≠ 0 := fun h => hry (congrArg Subtype.val h)
  letI : Module.Free k (quotPiece I e) :=
    Module.Free.of_divisionRing k (quotPiece I e)
  letI : Module.Projective k (quotPiece I e) := Module.Projective.of_free
  obtain ⟨psi, hpsi⟩ := Projective.exists_dual_ne_zero k hy
  let E := reversedMatlisPieceEquiv hA (Nat.zero_le e)
  let top : reversedMatlisPiece hA 0 := E.symm psi
  let rpiece : MvPolynomial.homogeneousSubmodule (Fin 3) k (e - n) :=
    ⟨r, (MvPolynomial.mem_homogeneousSubmodule (e - n) r).mpr hr⟩
  let u : Fin 2 → MvPolynomial.homogeneousSubmodule (Fin 3) k (e - n) :=
    fun i => (matlisTopBasis hA).repr top i • rpiece
  refine ⟨u, ?_⟩
  have hsum := (matlisTopBasis hA).sum_repr top
  let ev : reversedMatlisPiece hA 0 →ₗ[k] k :=
    (matlisEval I y.1).comp (reversedMatlisPiece hA 0).subtype
  have happ := congrArg ev hsum
  have hcoords :
      (∑ i : Fin 2, (matlisTopBasis hA).repr top i *
        matlisGenerator hA i y.1) = top.1 y.1 := by
    rw [map_sum] at happ
    simp_rw [map_smul] at happ
    simpa [ev, matlisGenerator, smul_eq_mul] using happ
  have htop : E top = psi := E.apply_symm_apply psi
  have htop_apply : top.1 y.1 = psi y := by
    have := DFunLike.congr_fun htop y
    exact this
  rw [inverseSystemPieceMap_apply]
  change (∑ i : Fin 2, matlisGenerator hA i
    (Ideal.Quotient.mk I (u i).1 * x.1)) ≠ 0
  have heval :
      (∑ i : Fin 2, matlisGenerator hA i
        (Ideal.Quotient.mk I (u i).1 * x.1)) = psi y := by
    calc
      _ = ∑ i : Fin 2, (matlisTopBasis hA).repr top i *
          matlisGenerator hA i y.1 := by
        simp only [u, rpiece, Submodule.coe_smul_of_tower, quotient_mk_smul,
          smul_mul_assoc, map_smul, smul_eq_mul, y]
      _ = top.1 y.1 := hcoords
      _ = psi y := htop_apply
  rw [heval]
  exact hpsi

/-- Hence every graded dual piece is generated by the two chosen top-dual
forms. -/
theorem inverseSystemPieceMap_surjective {I : Ideal (R3 k)} {e n : ℕ}
    (hA : IsTypeTwoLevel I e) (hne : n ≤ e) :
    Function.Surjective (inverseSystemPieceMap hA n) := by
  letI := hA.finiteDimensional
  letI : FiniteDimensional k (quotPiece I n) :=
    FiniteDimensional.of_injective (quotPiece I n).subtype
      (quotPiece I n).injective_subtype
  let s : Set (Module.Dual k (quotPiece I n)) :=
    Set.range (inverseSystemPieceMap hA n)
  letI : Module.Free k (quotPiece I n) :=
    Module.Free.of_divisionRing k (quotPiece I n)
  letI : Module.Free k
      (Module.Dual k (quotPiece I n) ⧸ Submodule.span k s) :=
    Module.Free.of_divisionRing k
      (Module.Dual k (quotPiece I n) ⧸ Submodule.span k s)
  letI : Module.Projective k
      (Module.Dual k (quotPiece I n) ⧸ Submodule.span k s) :=
    Module.Projective.of_free
  have hspan : Submodule.span k s = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro x hx
    obtain ⟨u, hu⟩ := inverseSystemPieceMap_separates hA hne x hx
    exact ⟨inverseSystemPieceMap hA n u, ⟨u, rfl⟩, hu⟩
  rw [← LinearMap.range_eq_top]
  apply le_antisymm le_top
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro f ⟨u, rfl⟩
  exact ⟨u, rfl⟩

/-- The global inverse-system presentation by the two chosen generators. -/
noncomputable def inverseSystemMap {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) :
    (Fin 2 → R3 k) →ₗ[R3 k] MatlisDual I where
  toFun u := ∑ i : Fin 2, u i • matlisGenerator hA i
  map_add' := by
    intro u v
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r u
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

@[simp] lemma inverseSystemMap_apply {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) (u : Fin 2 → R3 k) :
    inverseSystemMap hA u = ∑ i : Fin 2, u i • matlisGenerator hA i := rfl

lemma inverseSystemMap_homogeneous_mem {I : Ideal (R3 k)} {e n : ℕ}
    (hA : IsTypeTwoLevel I e) (hne : n ≤ e)
    (u : Fin 2 → MvPolynomial.homogeneousSubmodule (Fin 3) k (e - n)) :
    inverseSystemMap hA (fun i => (u i).1) ∈
      matlisPiece I hA.homogeneous n := by
  rw [inverseSystemMap_apply]
  apply Submodule.sum_mem
  intro i hi
  have h := matlisPiece_smul hA.homogeneous
    ((MvPolynomial.mem_homogeneousSubmodule (e - n) (u i).1).mp (u i).2)
    (Nat.sub_le e n) (matlisGenerator_mem_top hA i)
  simpa [Nat.sub_sub_self hne] using h

lemma matlisPieceRestrict_inverseSystemMap {I : Ideal (R3 k)} {e n : ℕ}
    (hA : IsTypeTwoLevel I e) (hne : n ≤ e)
    (u : Fin 2 → MvPolynomial.homogeneousSubmodule (Fin 3) k (e - n)) :
    matlisPieceRestrict I hA.homogeneous n
        ⟨inverseSystemMap hA (fun i => (u i).1),
          inverseSystemMap_homogeneous_mem hA hne u⟩ =
      inverseSystemPieceMap hA n u := by
  apply LinearMap.ext
  intro x
  change matlisEval I x.1 (∑ i : Fin 2, (u i).1 • matlisGenerator hA i) =
    ∑ i : Fin 2, matlisGenerator hA i
      (Ideal.Quotient.mk I (u i).1 * x.1)
  rw [map_sum]
  simp only [map_smul, matlisEval_apply, matlisDual_smul_apply,
    RingHom.id_apply]

/-- The global map `R² → M` is surjective.  Thus its kernel is the actual
homogeneous first-syzygy module of the dualized presentation. -/
theorem inverseSystemMap_surjective {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : Function.Surjective (inverseSystemMap hA) := by
  intro phi
  have hpre : ∀ n : ℕ, ∃ U : Fin 2 → R3 k,
      n ≤ e → inverseSystemMap hA U = matlisComponent I hA.homogeneous n phi := by
    intro n
    by_cases hne : n ≤ e
    · let phin : matlisPiece I hA.homogeneous n :=
        ⟨matlisComponent I hA.homogeneous n phi, ⟨phi, rfl⟩⟩
      obtain ⟨u, hu⟩ := inverseSystemPieceMap_surjective hA hne
        (matlisPieceRestrict I hA.homogeneous n phin)
      refine ⟨fun i => (u i).1, fun _ => ?_⟩
      have heq :
          (⟨inverseSystemMap hA (fun i => (u i).1),
              inverseSystemMap_homogeneous_mem hA hne u⟩ :
            matlisPiece I hA.homogeneous n) = phin := by
        apply (matlisPieceRestrict_bijective I hA.homogeneous n).1
        rw [matlisPieceRestrict_inverseSystemMap hA hne u, hu]
      exact congrArg Subtype.val heq
    · exact ⟨0, fun h => (hne h).elim⟩
  choose U hU using hpre
  refine ⟨∑ n ∈ Finset.range (e + 1), U n, ?_⟩
  rw [map_sum]
  have heq :
      (∑ n ∈ Finset.range (e + 1), inverseSystemMap hA (U n)) =
        ∑ n ∈ Finset.range (e + 1), matlisComponent I hA.homogeneous n phi := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hU n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  rw [heq, sum_matlisComponent hA phi]

/-- The actual first relation module of the two-generator inverse-system
presentation. -/
noncomputable abbrev inverseSystemKernel {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) := LinearMap.ker (inverseSystemMap hA)

lemma inverseSystemKernel_fg {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : (inverseSystemKernel hA).FG := by
  letI : Module.Finite (R3 k) (MatlisDual I) :=
    Module.Finite.of_surjective (inverseSystemMap hA)
      (inverseSystemMap_surjective hA)
  letI : Module.FinitePresentation (R3 k) (MatlisDual I) :=
    Module.finitePresentation_of_finite (R3 k) (MatlisDual I)
  exact Module.FinitePresentation.fg_ker (inverseSystemMap hA)
    (inverseSystemMap_surjective hA)

/-- Coordinatewise homogeneous projection on the free module `R²`. -/
noncomputable def vectorHomogeneousComponent (d : ℕ) :
    (Fin 2 → R3 k) →ₗ[k] (Fin 2 → R3 k) where
  toFun u i := MvPolynomial.homogeneousComponent d (u i)
  map_add' := by
    intro u v
    apply funext
    intro i
    exact map_add (MvPolynomial.homogeneousComponent d) (u i) (v i)
  map_smul' := by
    intro c u
    apply funext
    intro i
    exact map_smul (MvPolynomial.homogeneousComponent d) c (u i)

@[simp] lemma vectorHomogeneousComponent_apply (d : ℕ) (u : Fin 2 → R3 k)
    (i : Fin 2) :
    vectorHomogeneousComponent d u i =
      MvPolynomial.homogeneousComponent d (u i) := rfl

lemma homogeneousComponent_mul_right {m n : ℕ} {r f : R3 k}
    (hr : MvPolynomial.IsHomogeneous r m) (hmn : m ≤ n) :
    MvPolynomial.homogeneousComponent n (f * r) =
      MvPolynomial.homogeneousComponent (n - m) f * r := by
  rw [← MvPolynomial.decomposition.decompose'_apply,
    ← MvPolynomial.decomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_le
    (MvPolynomial.homogeneousSubmodule (Fin 3) k)
    ((MvPolynomial.mem_homogeneousSubmodule m r).mpr hr) hmn

lemma homogeneousComponent_mul_left_eq_zero {m n : ℕ} {r f : R3 k}
    (hr : MvPolynomial.IsHomogeneous r m) (hnm : n < m) :
    MvPolynomial.homogeneousComponent n (r * f) = 0 := by
  rw [← MvPolynomial.decomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_left_mem_of_not_le
    (MvPolynomial.homogeneousSubmodule (Fin 3) k)
    ((MvPolynomial.mem_homogeneousSubmodule m r).mpr hr) (by omega)

lemma quotientComponent_mul_left_eq_zero {I : Ideal (R3 k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    {m n : ℕ} {r : R3 k} (hr : MvPolynomial.IsHomogeneous r m)
    (hnm : n < m) (x : R3 k ⧸ I) :
    quotientComponent I hI n (Ideal.Quotient.mk I r * x) = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, quotientComponent_mk,
    homogeneousComponent_mul_left_eq_zero hr hnm, map_zero]

lemma matlisPiece_smul_eq_zero_of_lt {I : Ideal (R3 k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    {m n : ℕ} {r : R3 k} (hr : MvPolynomial.IsHomogeneous r m)
    (hnm : n < m) {phi : MatlisDual I} (hphi : phi ∈ matlisPiece I hI n) :
    r • phi = 0 := by
  apply MatlisDual.ext
  apply LinearMap.ext
  intro x
  change phi (Ideal.Quotient.mk I r * x) = 0
  rw [matlisPiece_apply_projection I hI n ⟨phi, hphi⟩,
    quotientComponent_mul_left_eq_zero hI hr hnm, map_zero]

/-- Acting by the degree-`d` component of a coefficient vector is exactly
the degree-`e-d` projection of its image in the Matlis dual. -/
lemma inverseSystemMap_vectorComponent {I : Ideal (R3 k)} {e d : ℕ}
    (hA : IsTypeTwoLevel I e) (hde : d ≤ e) (u : Fin 2 → R3 k) :
    inverseSystemMap hA (vectorHomogeneousComponent d u) =
      matlisComponent I hA.homogeneous (e - d) (inverseSystemMap hA u) := by
  apply MatlisDual.ext
  apply LinearMap.ext
  intro x
  change matlisEval I x
      (∑ i : Fin 2, MvPolynomial.homogeneousComponent d (u i) •
        matlisGenerator hA i) =
    matlisEval I (quotientComponent I hA.homogeneous (e - d) x)
      (∑ i : Fin 2, u i • matlisGenerator hA i)
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul, matlisEval_apply, matlisDual_smul_apply,
    RingHom.id_apply]
  let topi : matlisPiece I hA.homogeneous e :=
    ⟨matlisGenerator hA i, matlisGenerator_mem_top hA i⟩
  have hleft := matlisPiece_apply_projection I hA.homogeneous e topi
    (Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent d (u i)) * x)
  have hright := matlisPiece_apply_projection I hA.homogeneous e topi
    (Ideal.Quotient.mk I (u i) *
      quotientComponent I hA.homogeneous (e - d) x)
  rw [hleft, hright]
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, quotientComponent_mk, quotientComponent_mk,
    ← map_mul, quotientComponent_mk]
  rw [homogeneousComponent_mul_left
      (MvPolynomial.homogeneousComponent_isHomogeneous d (u i)) hde,
    homogeneousComponent_mul_right
      (MvPolynomial.homogeneousComponent_isHomogeneous (e - d) f)
      (Nat.sub_le e d), Nat.sub_sub_self hde]

lemma inverseSystemMap_vectorComponent_high {I : Ideal (R3 k)} {e d : ℕ}
    (hA : IsTypeTwoLevel I e) (hed : e < d) (u : Fin 2 → R3 k) :
    inverseSystemMap hA (vectorHomogeneousComponent d u) = 0 := by
  rw [inverseSystemMap_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact matlisPiece_smul_eq_zero_of_lt hA.homogeneous
    (MvPolynomial.homogeneousComponent_isHomogeneous d (u i)) hed
    (matlisGenerator_mem_top hA i)

/-- The first relation module is homogeneous. -/
lemma inverseSystemKernel_component_mem {I : Ideal (R3 k)} {e d : ℕ}
    (hA : IsTypeTwoLevel I e) {u : Fin 2 → R3 k}
    (hu : u ∈ inverseSystemKernel hA) :
    vectorHomogeneousComponent d u ∈ inverseSystemKernel hA := by
  rw [LinearMap.mem_ker] at hu ⊢
  by_cases hde : d ≤ e
  · rw [inverseSystemMap_vectorComponent hA hde, hu, map_zero]
  · exact inverseSystemMap_vectorComponent_high hA (by omega) u

noncomputable def vectorTotalDegree (u : Fin 2 → R3 k) : ℕ :=
  max (MvPolynomial.totalDegree (u 0)) (MvPolynomial.totalDegree (u 1))

lemma sum_homogeneousComponent_to {D : ℕ} (f : R3 k)
    (hD : MvPolynomial.totalDegree f ≤ D) :
    (∑ d ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent d f) = f := by
  calc
    _ = ∑ d ∈ Finset.range (MvPolynomial.totalDegree f + 1),
        MvPolynomial.homogeneousComponent d f := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (Nat.add_le_add_right hD 1)
      · intro d hdD hdf
        simp only [Finset.mem_range] at hdD hdf
        exact MvPolynomial.homogeneousComponent_eq_zero d f (by omega)
    _ = f := MvPolynomial.sum_homogeneousComponent f

lemma sum_vectorHomogeneousComponent (u : Fin 2 → R3 k) :
    (∑ d ∈ Finset.range (vectorTotalDegree u + 1),
      vectorHomogeneousComponent d u) = u := by
  apply funext
  intro i
  simp only [Finset.sum_apply, vectorHomogeneousComponent_apply]
  apply sum_homogeneousComponent_to
  fin_cases i <;> simp [vectorTotalDegree]

/-- Finite homogeneous generators of the actual first relation module. -/
structure HomogeneousFirstRelations {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) where
  β : Type*
  fintype : Fintype β
  degree : β → ℕ
  generator : β → (Fin 2 → R3 k)
  homogeneous : ∀ b i,
    MvPolynomial.IsHomogeneous (generator b i) (degree b)
  relation : ∀ b, generator b ∈ inverseSystemKernel hA
  span_eq : Submodule.span (R3 k) (Set.range generator) = inverseSystemKernel hA

/-- The first kernel admits a finite homogeneous generating family, derived
from Noetherian finite generation by splitting a finite generating set into
its finitely many homogeneous components. -/
noncomputable def homogeneousFirstRelations {I : Ideal (R3 k)} {e : ℕ}
    (hA : IsTypeTwoLevel I e) : HomogeneousFirstRelations hA := by
  classical
  let hex := (inverseSystemKernel_fg hA).exists_span_finset_card_eq_spanFinrank
  let s := Classical.choose hex
  have hsData := Classical.choose_spec hex
  have hsCard := hsData.1
  have hs := hsData.2
  let β := Σ u : s, Fin (vectorTotalDegree u.1 + 1)
  let gen : β → (Fin 2 → R3 k) := fun b =>
    vectorHomogeneousComponent b.2.1 b.1.1
  let deg : β → ℕ := fun b => b.2.1
  letI : Fintype β := inferInstance
  refine
    { β := β
      fintype := inferInstance
      degree := deg
      generator := gen
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro b i
    exact MvPolynomial.homogeneousComponent_isHomogeneous (deg b) (b.1.1 i)
  · intro b
    apply inverseSystemKernel_component_mem hA
    rw [← hs]
    exact Submodule.subset_span b.1.2
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      apply inverseSystemKernel_component_mem hA
      rw [← hs]
      exact Submodule.subset_span b.1.2
    · rw [← hs]
      apply Submodule.span_le.mpr
      intro u hu
      rw [← sum_vectorHomogeneousComponent u]
      apply Submodule.sum_mem
      intro d hd
      have hd' : d < vectorTotalDegree u + 1 := Finset.mem_range.mp hd
      let b : β := ⟨⟨u, hu⟩, ⟨d, hd'⟩⟩
      exact Submodule.subset_span ⟨b, rfl⟩

namespace HomogeneousFirstRelations

variable {I : Ideal (R3 k)} {e : ℕ} {hA : IsTypeTwoLevel I e}

/-- The homogeneous first differential whose columns are the chosen
relations among the two inverse-system generators. -/
noncomputable def d₁ (H : HomogeneousFirstRelations hA) :
    (H.β → R3 k) →ₗ[R3 k] (Fin 2 → R3 k) := by
  letI := H.fintype
  exact
    { toFun := fun c => ∑ b, c b • H.generator b
      map_add' := by
        intro c c'
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
          RingHom.id_apply] }

@[simp] lemma d₁_apply (H : HomogeneousFirstRelations hA) (c : H.β → R3 k) :
    H.d₁ c = (@Finset.univ H.β H.fintype).sum
      (fun b => c b • H.generator b) := rfl

lemma range_d₁ (H : HomogeneousFirstRelations hA) :
    LinearMap.range H.d₁ = Submodule.span (R3 k) (Set.range H.generator) := by
  classical
  letI := H.fintype
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    rw [d₁_apply]
    apply Submodule.sum_mem
    intro b hb
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    let c : H.β → R3 k := fun j => if j = b then 1 else 0
    refine ⟨c, ?_⟩
    rw [d₁_apply]
    classical
    simp [c]

lemma range_d₁_eq_kernel (H : HomogeneousFirstRelations hA) :
    LinearMap.range H.d₁ = inverseSystemKernel hA := by
  rw [H.range_d₁, H.span_eq]

lemma inverseSystemMap_comp_d₁ (H : HomogeneousFirstRelations hA) :
    (inverseSystemMap hA).comp H.d₁ = 0 := by
  rw [LinearMap.ext_iff]
  intro c
  have hc : H.d₁ c ∈ inverseSystemKernel hA := by
    rw [← H.range_d₁_eq_kernel]
    exact LinearMap.mem_range_self H.d₁ c
  exact LinearMap.mem_ker.mp hc

lemma ker_d₁_fg (H : HomogeneousFirstRelations hA) :
    (LinearMap.ker H.d₁).FG := by
  letI := H.fintype
  exact IsNoetherian.noetherian (LinearMap.ker H.d₁)

/-- Projection to total degree `q` in the free module whose basis vector
`b` has shift `H.degree b`. -/
noncomputable def shiftedComponent (H : HomogeneousFirstRelations hA) (q : ℕ) :
    (H.β → R3 k) →ₗ[k] (H.β → R3 k) where
  toFun c b := if H.degree b ≤ q then
    MvPolynomial.homogeneousComponent (q - H.degree b) (c b) else 0
  map_add' := by
    intro c c'
    apply funext
    intro b
    by_cases h : H.degree b ≤ q
    · simp only [h, if_pos, Pi.add_apply]
      exact map_add (MvPolynomial.homogeneousComponent (q - H.degree b))
        (c b) (c' b)
    · simp [h]
  map_smul' := by
    intro r c
    apply funext
    intro b
    by_cases h : H.degree b ≤ q
    · simp only [h, if_pos, Pi.smul_apply, RingHom.id_apply]
      exact map_smul (MvPolynomial.homogeneousComponent (q - H.degree b))
        r (c b)
    · simp [h]

@[simp] lemma shiftedComponent_apply (H : HomogeneousFirstRelations hA)
    (q : ℕ) (c : H.β → R3 k) (b : H.β) :
    H.shiftedComponent q c b = if H.degree b ≤ q then
      MvPolynomial.homogeneousComponent (q - H.degree b) (c b) else 0 := rfl

lemma homogeneousComponent_mul_right_eq_zero {m n : ℕ} {r f : R3 k}
    (hr : MvPolynomial.IsHomogeneous r m) (hnm : n < m) :
    MvPolynomial.homogeneousComponent n (f * r) = 0 := by
  rw [← MvPolynomial.decomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le
    (MvPolynomial.homogeneousSubmodule (Fin 3) k)
    ((MvPolynomial.mem_homogeneousSubmodule m r).mpr hr) (by omega)

/-- The first differential preserves the shifted total grading. -/
lemma d₁_shiftedComponent (H : HomogeneousFirstRelations hA)
    (q : ℕ) (c : H.β → R3 k) :
    H.d₁ (H.shiftedComponent q c) =
      vectorHomogeneousComponent q (H.d₁ c) := by
  classical
  letI := H.fintype
  apply funext
  intro i
  rw [d₁_apply, d₁_apply]
  simp only [shiftedComponent_apply, vectorHomogeneousComponent_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ b, (if H.degree b ≤ q then
      MvPolynomial.homogeneousComponent (q - H.degree b) (c b) else 0) *
        H.generator b i) =
    MvPolynomial.homogeneousComponent q
      (∑ b, c b * H.generator b i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hle : H.degree b ≤ q
  · rw [if_pos hle]
    exact (homogeneousComponent_mul_right (H.homogeneous b i) hle).symm
  · rw [if_neg hle, zero_mul]
    exact (homogeneousComponent_mul_right_eq_zero
      (H.homogeneous b i) (by omega)).symm

/-- The second syzygy module is homogeneous in the shifted grading. -/
lemma ker_d₁_shiftedComponent_mem (H : HomogeneousFirstRelations hA)
    (q : ℕ) {c : H.β → R3 k} (hc : c ∈ LinearMap.ker H.d₁) :
    H.shiftedComponent q c ∈ LinearMap.ker H.d₁ := by
  rw [LinearMap.mem_ker] at hc ⊢
  rw [H.d₁_shiftedComponent, hc, map_zero]

noncomputable def shiftedTotalDegree (H : HomogeneousFirstRelations hA)
    (c : H.β → R3 k) : ℕ := by
  letI := H.fintype
  exact Finset.univ.sup fun b => H.degree b + MvPolynomial.totalDegree (c b)

lemma degree_add_totalDegree_le_shiftedTotalDegree
    (H : HomogeneousFirstRelations hA) (c : H.β → R3 k) (b : H.β) :
    H.degree b + MvPolynomial.totalDegree (c b) ≤ H.shiftedTotalDegree c := by
  classical
  letI := H.fintype
  unfold shiftedTotalDegree
  exact Finset.le_sup (f := fun j => H.degree j + MvPolynomial.totalDegree (c j))
    (Finset.mem_univ b)

lemma sum_shifted_homogeneousComponent_exact (s : ℕ) (f : R3 k) :
    (∑ q ∈ Finset.range (s + MvPolynomial.totalDegree f + 1),
      if s ≤ q then MvPolynomial.homogeneousComponent (q - s) f else 0) = f := by
  induction s with
  | zero =>
      simpa using MvPolynomial.sum_homogeneousComponent f
  | succ s ih =>
      rw [show s + 1 + MvPolynomial.totalDegree f + 1 =
        (s + MvPolynomial.totalDegree f + 1) + 1 by omega,
        Finset.sum_range_succ']
      simpa [Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub] using ih

lemma sum_shifted_homogeneousComponent_to {s D : ℕ} (f : R3 k)
    (hD : s + MvPolynomial.totalDegree f ≤ D) :
    (∑ q ∈ Finset.range (D + 1),
      if s ≤ q then MvPolynomial.homogeneousComponent (q - s) f else 0) = f := by
  calc
    _ = ∑ q ∈ Finset.range (s + MvPolynomial.totalDegree f + 1),
        if s ≤ q then MvPolynomial.homogeneousComponent (q - s) f else 0 := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (Nat.add_le_add_right hD 1)
      · intro q hqD hqS
        simp only [Finset.mem_range] at hqD hqS
        rw [if_pos (by omega)]
        exact MvPolynomial.homogeneousComponent_eq_zero (q - s) f (by omega)
    _ = f := sum_shifted_homogeneousComponent_exact s f

lemma sum_shiftedComponent (H : HomogeneousFirstRelations hA)
    (c : H.β → R3 k) :
    (∑ q ∈ Finset.range (H.shiftedTotalDegree c + 1),
      H.shiftedComponent q c) = c := by
  apply funext
  intro b
  simp only [Finset.sum_apply, shiftedComponent_apply]
  exact sum_shifted_homogeneousComponent_to (c b)
    (H.degree_add_totalDegree_le_shiftedTotalDegree c b)

/-- Finite homogeneous generators of the actual second syzygy module.
The degree records the common shifted degree relative to the first
relation degrees. -/
structure HomogeneousSecondRelations (H : HomogeneousFirstRelations hA) where
  γ : Type*
  fintype : Fintype γ
  degree : γ → ℕ
  generator : γ → (H.β → R3 k)
  homogeneous : ∀ g b,
    if H.degree b ≤ degree g then
      MvPolynomial.IsHomogeneous (generator g b) (degree g - H.degree b)
    else generator g b = 0
  relation : ∀ g, generator g ∈ LinearMap.ker H.d₁
  span_eq : Submodule.span (R3 k) (Set.range generator) = LinearMap.ker H.d₁

/-- The second kernel admits a finite homogeneous generating family. -/
noncomputable def homogeneousSecondRelations
    (H : HomogeneousFirstRelations hA) : HomogeneousSecondRelations H := by
  classical
  letI := H.fintype
  let hex := H.ker_d₁_fg.exists_span_finset_card_eq_spanFinrank
  let s := Classical.choose hex
  have hsData := Classical.choose_spec hex
  have hs := hsData.2
  let γ := Σ c : s, Fin (H.shiftedTotalDegree c.1 + 1)
  let gen : γ → (H.β → R3 k) := fun g =>
    H.shiftedComponent g.2.1 g.1.1
  let deg : γ → ℕ := fun g => g.2.1
  letI : Fintype γ := inferInstance
  refine
    { γ := γ
      fintype := inferInstance
      degree := deg
      generator := gen
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro g b
    by_cases hle : H.degree b ≤ deg g
    · simp only [deg] at hle ⊢
      rw [if_pos hle]
      simp only [gen, shiftedComponent_apply, hle, if_pos]
      exact MvPolynomial.homogeneousComponent_isHomogeneous
        (g.2.1 - H.degree b) (g.1.1 b)
    · simp only [deg] at hle ⊢
      rw [if_neg hle]
      simp [gen, hle]
  · intro g
    have hg : g.1.1 ∈ LinearMap.ker H.d₁ := by
      rw [← hs]
      exact Submodule.subset_span g.1.2
    exact H.ker_d₁_shiftedComponent_mem (deg g) hg
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      have hg : g.1.1 ∈ LinearMap.ker H.d₁ := by
        rw [← hs]
        exact Submodule.subset_span g.1.2
      exact H.ker_d₁_shiftedComponent_mem (deg g) hg
    · rw [← hs]
      apply Submodule.span_le.mpr
      intro c hc
      rw [← H.sum_shiftedComponent c]
      apply Submodule.sum_mem
      intro q hq
      have hq' : q < H.shiftedTotalDegree c + 1 := Finset.mem_range.mp hq
      let g : γ := ⟨⟨c, hc⟩, ⟨q, hq'⟩⟩
      exact Submodule.subset_span ⟨g, rfl⟩

namespace HomogeneousSecondRelations

variable {H : HomogeneousFirstRelations hA}

/-- The homogeneous second differential whose columns generate the kernel
of the first differential. -/
noncomputable def d₂ (S : HomogeneousSecondRelations H) :
    (S.γ → R3 k) →ₗ[R3 k] (H.β → R3 k) := by
  letI := S.fintype
  exact
    { toFun := fun c => ∑ g, c g • S.generator g
      map_add' := by
        intro c c'
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
          RingHom.id_apply] }

@[simp] lemma d₂_apply (S : HomogeneousSecondRelations H) (c : S.γ → R3 k) :
    S.d₂ c = (@Finset.univ S.γ S.fintype).sum
      (fun g => c g • S.generator g) := rfl

lemma range_d₂ (S : HomogeneousSecondRelations H) :
    LinearMap.range S.d₂ = Submodule.span (R3 k) (Set.range S.generator) := by
  classical
  letI := S.fintype
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    rw [d₂_apply]
    apply Submodule.sum_mem
    intro g hg
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    let c : S.γ → R3 k := fun j => if j = g then 1 else 0
    refine ⟨c, ?_⟩
    rw [d₂_apply]
    simp [c]

lemma range_d₂_eq_kernel (S : HomogeneousSecondRelations H) :
    LinearMap.range S.d₂ = LinearMap.ker H.d₁ := by
  rw [S.range_d₂, S.span_eq]

lemma d₁_comp_d₂ (S : HomogeneousSecondRelations H) :
    H.d₁.comp S.d₂ = 0 := by
  rw [LinearMap.ext_iff]
  intro c
  have hc : S.d₂ c ∈ LinearMap.ker H.d₁ := by
    rw [← S.range_d₂_eq_kernel]
    exact LinearMap.mem_range_self S.d₂ c
  exact LinearMap.mem_ker.mp hc

lemma ker_d₂_fg (S : HomogeneousSecondRelations H) :
    (LinearMap.ker S.d₂).FG := by
  letI := S.fintype
  exact IsNoetherian.noetherian (LinearMap.ker S.d₂)

/-- Projection to total degree `q` in the second free module, whose basis
vector `g` has shift `S.degree g`. -/
noncomputable def shiftedComponent (S : HomogeneousSecondRelations H) (q : ℕ) :
    (S.γ → R3 k) →ₗ[k] (S.γ → R3 k) where
  toFun c g := if S.degree g ≤ q then
    MvPolynomial.homogeneousComponent (q - S.degree g) (c g) else 0
  map_add' := by
    intro c c'
    apply funext
    intro g
    by_cases h : S.degree g ≤ q
    · simp only [h, if_pos, Pi.add_apply]
      exact map_add (MvPolynomial.homogeneousComponent (q - S.degree g))
        (c g) (c' g)
    · simp [h]
  map_smul' := by
    intro r c
    apply funext
    intro g
    by_cases h : S.degree g ≤ q
    · simp only [h, if_pos, Pi.smul_apply, RingHom.id_apply]
      exact map_smul (MvPolynomial.homogeneousComponent (q - S.degree g))
        r (c g)
    · simp [h]

@[simp] lemma shiftedComponent_apply (S : HomogeneousSecondRelations H)
    (q : ℕ) (c : S.γ → R3 k) (g : S.γ) :
    S.shiftedComponent q c g = if S.degree g ≤ q then
      MvPolynomial.homogeneousComponent (q - S.degree g) (c g) else 0 := rfl

/-- The second differential preserves the shifted total grading. -/
lemma d₂_shiftedComponent (S : HomogeneousSecondRelations H)
    (q : ℕ) (c : S.γ → R3 k) :
    S.d₂ (S.shiftedComponent q c) =
      H.shiftedComponent q (S.d₂ c) := by
  classical
  letI := S.fintype
  apply funext
  intro b
  rw [d₂_apply, d₂_apply]
  simp only [shiftedComponent_apply,
    HomogeneousFirstRelations.shiftedComponent_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ g, (if S.degree g ≤ q then
      MvPolynomial.homogeneousComponent (q - S.degree g) (c g) else 0) *
        S.generator g b) =
    if H.degree b ≤ q then
      MvPolynomial.homogeneousComponent (q - H.degree b)
        (∑ g, c g * S.generator g b) else 0
  by_cases hbq : H.degree b ≤ q
  · rw [if_pos hbq, map_sum]
    apply Finset.sum_congr rfl
    intro g hg
    by_cases hbg : H.degree b ≤ S.degree g
    · have hhom := S.homogeneous g b
      rw [if_pos hbg] at hhom
      by_cases hsq : S.degree g ≤ q
      · rw [if_pos hsq]
        have hsub : (q - H.degree b) - (S.degree g - H.degree b) =
            q - S.degree g := by omega
        rw [homogeneousComponent_mul_right hhom (by omega)]
        rw [hsub]
      · rw [if_neg hsq, zero_mul]
        exact (homogeneousComponent_mul_right_eq_zero hhom (by omega)).symm
    · have hzero := S.homogeneous g b
      rw [if_neg hbg] at hzero
      simp [hzero]
  · rw [if_neg hbq]
    apply Finset.sum_eq_zero
    intro g hg
    by_cases hsq : S.degree g ≤ q
    · have hbg : ¬ H.degree b ≤ S.degree g := by omega
      have hzero := S.homogeneous g b
      rw [if_neg hbg] at hzero
      simp [hsq, hzero]
    · simp [hsq]

/-- The third syzygy module is homogeneous in the shifted grading. -/
lemma ker_d₂_shiftedComponent_mem (S : HomogeneousSecondRelations H)
    (q : ℕ) {c : S.γ → R3 k} (hc : c ∈ LinearMap.ker S.d₂) :
    S.shiftedComponent q c ∈ LinearMap.ker S.d₂ := by
  rw [LinearMap.mem_ker] at hc ⊢
  rw [S.d₂_shiftedComponent, hc, map_zero]

noncomputable def shiftedTotalDegree (S : HomogeneousSecondRelations H)
    (c : S.γ → R3 k) : ℕ := by
  letI := S.fintype
  exact Finset.univ.sup fun g => S.degree g + MvPolynomial.totalDegree (c g)

lemma degree_add_totalDegree_le_shiftedTotalDegree
    (S : HomogeneousSecondRelations H) (c : S.γ → R3 k) (g : S.γ) :
    S.degree g + MvPolynomial.totalDegree (c g) ≤ S.shiftedTotalDegree c := by
  classical
  letI := S.fintype
  unfold shiftedTotalDegree
  exact Finset.le_sup (f := fun j => S.degree j + MvPolynomial.totalDegree (c j))
    (Finset.mem_univ g)

lemma sum_shiftedComponent (S : HomogeneousSecondRelations H)
    (c : S.γ → R3 k) :
    (∑ q ∈ Finset.range (S.shiftedTotalDegree c + 1),
      S.shiftedComponent q c) = c := by
  apply funext
  intro g
  simp only [Finset.sum_apply, shiftedComponent_apply]
  exact HomogeneousFirstRelations.sum_shifted_homogeneousComponent_to (c g)
    (S.degree_add_totalDegree_le_shiftedTotalDegree c g)

/-- Finite homogeneous generators of the actual third syzygy module. -/
structure HomogeneousThirdRelations (S : HomogeneousSecondRelations H) where
  δ : Type*
  fintype : Fintype δ
  degree : δ → ℕ
  generator : δ → (S.γ → R3 k)
  homogeneous : ∀ a g,
    if S.degree g ≤ degree a then
      MvPolynomial.IsHomogeneous (generator a g) (degree a - S.degree g)
    else generator a g = 0
  relation : ∀ a, generator a ∈ LinearMap.ker S.d₂
  span_eq : Submodule.span (R3 k) (Set.range generator) = LinearMap.ker S.d₂

/-- The third kernel admits a finite homogeneous generating family. -/
noncomputable def homogeneousThirdRelations
    (S : HomogeneousSecondRelations H) : HomogeneousThirdRelations S := by
  classical
  letI := S.fintype
  let hex := S.ker_d₂_fg.exists_span_finset_card_eq_spanFinrank
  let s := Classical.choose hex
  have hsData := Classical.choose_spec hex
  have hs := hsData.2
  let δ := Σ c : s, Fin (S.shiftedTotalDegree c.1 + 1)
  let gen : δ → (S.γ → R3 k) := fun a =>
    S.shiftedComponent a.2.1 a.1.1
  let deg : δ → ℕ := fun a => a.2.1
  letI : Fintype δ := inferInstance
  refine
    { δ := δ
      fintype := inferInstance
      degree := deg
      generator := gen
      homogeneous := ?_
      relation := ?_
      span_eq := ?_ }
  · intro a g
    by_cases hle : S.degree g ≤ deg a
    · simp only [deg] at hle ⊢
      rw [if_pos hle]
      simp only [gen, shiftedComponent_apply, hle, if_pos]
      exact MvPolynomial.homogeneousComponent_isHomogeneous
        (a.2.1 - S.degree g) (a.1.1 g)
    · simp only [deg] at hle ⊢
      rw [if_neg hle]
      simp [gen, hle]
  · intro a
    have ha : a.1.1 ∈ LinearMap.ker S.d₂ := by
      rw [← hs]
      exact Submodule.subset_span a.1.2
    exact S.ker_d₂_shiftedComponent_mem (deg a) ha
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      have ha : a.1.1 ∈ LinearMap.ker S.d₂ := by
        rw [← hs]
        exact Submodule.subset_span a.1.2
      exact S.ker_d₂_shiftedComponent_mem (deg a) ha
    · rw [← hs]
      apply Submodule.span_le.mpr
      intro c hc
      rw [← S.sum_shiftedComponent c]
      apply Submodule.sum_mem
      intro q hq
      have hq' : q < S.shiftedTotalDegree c + 1 := Finset.mem_range.mp hq
      let a : δ := ⟨⟨c, hc⟩, ⟨q, hq'⟩⟩
      exact Submodule.subset_span ⟨a, rfl⟩

namespace HomogeneousThirdRelations

variable {S : HomogeneousSecondRelations H}

/-- The homogeneous third differential. -/
noncomputable def d₃ (T : HomogeneousThirdRelations S) :
    (T.δ → R3 k) →ₗ[R3 k] (S.γ → R3 k) := by
  letI := T.fintype
  exact
    { toFun := fun c => ∑ a, c a • T.generator a
      map_add' := by
        intro c c'
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
          RingHom.id_apply] }

@[simp] lemma d₃_apply (T : HomogeneousThirdRelations S) (c : T.δ → R3 k) :
    T.d₃ c = (@Finset.univ T.δ T.fintype).sum
      (fun a => c a • T.generator a) := rfl

lemma range_d₃ (T : HomogeneousThirdRelations S) :
    LinearMap.range T.d₃ = Submodule.span (R3 k) (Set.range T.generator) := by
  classical
  letI := T.fintype
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    rw [d₃_apply]
    apply Submodule.sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let c : T.δ → R3 k := fun j => if j = a then 1 else 0
    refine ⟨c, ?_⟩
    rw [d₃_apply]
    simp [c]

lemma range_d₃_eq_kernel (T : HomogeneousThirdRelations S) :
    LinearMap.range T.d₃ = LinearMap.ker S.d₂ := by
  rw [T.range_d₃, T.span_eq]

lemma d₂_comp_d₃ (T : HomogeneousThirdRelations S) :
    S.d₂.comp T.d₃ = 0 := by
  rw [LinearMap.ext_iff]
  intro c
  have hc : T.d₃ c ∈ LinearMap.ker S.d₂ := by
    rw [← T.range_d₃_eq_kernel]
    exact LinearMap.mem_range_self T.d₃ c
  exact LinearMap.mem_ker.mp hc

end HomogeneousThirdRelations

end HomogeneousSecondRelations

end HomogeneousFirstRelations

end LogConcavity
