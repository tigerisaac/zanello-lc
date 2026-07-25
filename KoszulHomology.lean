import Koszul

/-!
# Koszul homology and the connecting isomorphisms

`Koszul.lean` builds the complex `0 → M → M³ → M³ → M → 0` and proves it
exact when `M` is free.  This file turns that vanishing into the dimension
shifts that compute the last Betti number of a module `M` of finite length:

```
Soc M = H₃(K ⊗ M) ≅ H₂(K ⊗ Z₁) ≅ H₁(K ⊗ Z₂) ≅ F₃ ⊗ k
```

where `0 → Z₁ → F₀ → M → 0`, `0 → Z₂ → F₁ → Z₁ → 0`, `0 → F₃ → F₂ → Z₂ → 0`
are the short exact sequences carved out of a minimal free resolution.  Each
step is the connecting map of the Koszul homology sequence for a short exact
sequence whose middle term is free, so rather than developing a general long
exact sequence we prove exactly the three isomorphisms needed, by hand.

This file has the first of them, `socle_quotient_equiv_H₂`: for a submodule
`A ≤ B` with `B` Koszul-acyclic in degrees `2` and `3`,

```
Soc (B ⧸ A) ≅ H₂ A,   b + A ↦ [(x₀ • b, x₁ • b, x₂ • b)].
```
-/

namespace LogConcavity

namespace Koszul

noncomputable section

universe u v

open MvPolynomial

/-! ## Naturality of the differentials -/

section Naturality

variable {k : Type u} [Field k] {M N : Type v}
  [AddCommGroup M] [Module (R3 k) M] [AddCommGroup N] [Module (R3 k) N]

lemma map_d₃ (f : M →ₗ[R3 k] N) (m : M) (i : Fin 3) :
    f (d₃ k M m i) = d₃ k N (f m) i := by
  simp [d₃_apply, map_smul]

lemma map_d₂ (f : M →ₗ[R3 k] N) (g : Fin 3 → M) (i : Fin 3) :
    f (d₂ k M g i) = d₂ k N (fun j => f (g j)) i := by
  simp [d₂_apply, map_sub, map_smul]

lemma map_d₁ (f : M →ₗ[R3 k] N) (g : Fin 3 → M) :
    f (d₁ k M g) = d₁ k N (fun j => f (g j)) := by
  simp [d₁_apply, map_add, map_smul]

end Naturality

/-! ## Koszul homology in degrees one and two -/

section Homology

variable (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module (R3 k) M]

/-- Degree-two cycles: the kernel of the middle differential. -/
def cycles₂ : Submodule (R3 k) (Fin 3 → M) := LinearMap.ker (d₂ k M)

/-- Degree-two boundaries, as a submodule of the cycles. -/
def boundaries₂ : Submodule (R3 k) (cycles₂ k M) :=
  (LinearMap.range (d₃ k M)).comap (cycles₂ k M).subtype

/-- Koszul homology in degree two. -/
abbrev H₂ := (cycles₂ k M) ⧸ (boundaries₂ k M)

/-- Degree-one cycles. -/
def cycles₁ : Submodule (R3 k) (Fin 3 → M) := LinearMap.ker (d₁ k M)

/-- Degree-one boundaries, as a submodule of the cycles. -/
def boundaries₁ : Submodule (R3 k) (cycles₁ k M) :=
  (LinearMap.range (d₂ k M)).comap (cycles₁ k M).subtype

/-- Koszul homology in degree one. -/
abbrev H₁ := (cycles₁ k M) ⧸ (boundaries₁ k M)

variable {k M}

lemma mem_cycles₂ {g : Fin 3 → M} : g ∈ cycles₂ k M ↔ d₂ k M g = 0 :=
  LinearMap.mem_ker

lemma mem_boundaries₂ {g : cycles₂ k M} :
    g ∈ boundaries₂ k M ↔ ∃ m : M, d₃ k M m = (g : Fin 3 → M) :=
  Iff.rfl

end Homology

/-! ## The socle of a quotient is degree-two homology of the submodule -/

section Connecting

variable {k : Type u} [Field k] {B : Type v} [AddCommGroup B] [Module (R3 k) B]
  (A : Submodule (R3 k) B)

/-- The elements of `B` all of whose variable multiples lie in `A`: the
preimage in `B` of the socle of `B ⧸ A`. -/
def socLift : Submodule (R3 k) B where
  carrier := {b : B | ∀ i : Fin 3, (X i : R3 k) • b ∈ A}
  add_mem' {b b'} hb hb' i := by
    simpa [smul_add] using A.add_mem (hb i) (hb' i)
  zero_mem' _ := by simp
  smul_mem' c b hb i := by
    have : (X i : R3 k) • c • b = c • ((X i : R3 k) • b) := smul_comm _ _ _
    rw [this]
    exact A.smul_mem c (hb i)

lemma mem_socLift {b : B} : b ∈ socLift A ↔ ∀ i : Fin 3, (X i : R3 k) • b ∈ A :=
  Iff.rfl

lemma le_socLift : A ≤ socLift A := fun _ ha _ => A.smul_mem _ ha

/-- The copy of `A` inside `socLift A`. -/
def socLiftBase : Submodule (R3 k) (socLift A) := A.comap (socLift A).subtype

/-! ### The socle side -/

/-- `b ↦ b + A`, landing in the socle of `B ⧸ A`. -/
def toSocle : socLift A →ₗ[R3 k] LinearMap.ker (d₃ k (B ⧸ A)) where
  toFun b := ⟨Submodule.Quotient.mk (b : B), by
    rw [mem_ker_d₃_iff]
    intro i
    have : (X i : R3 k) • (Submodule.Quotient.mk (b : B) : B ⧸ A) =
        Submodule.Quotient.mk ((X i : R3 k) • (b : B)) := rfl
    rw [this, Submodule.Quotient.mk_eq_zero]
    exact b.2 i⟩
  map_add' b b' := by ext; rfl
  map_smul' c b := by ext; rfl

lemma toSocle_surjective : Function.Surjective (toSocle A) := by
  rintro ⟨c, hc⟩
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective A c
  have hb : b ∈ socLift A := by
    intro i
    have hi := (mem_ker_d₃_iff _).mp hc i
    have : (X i : R3 k) • (Submodule.Quotient.mk b : B ⧸ A) =
        Submodule.Quotient.mk ((X i : R3 k) • b) := rfl
    rw [this] at hi
    exact (Submodule.Quotient.mk_eq_zero A).mp hi
  exact ⟨⟨b, hb⟩, rfl⟩

lemma ker_toSocle : LinearMap.ker (toSocle A) = socLiftBase A := by
  ext b
  constructor
  · intro hb
    have : (Submodule.Quotient.mk (b : B) : B ⧸ A) = 0 := congrArg Subtype.val hb
    exact (Submodule.Quotient.mk_eq_zero A).mp this
  · intro hb
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero A).mpr hb

/-! ### The homology side -/

/-- `b ↦ (x₀ • b, x₁ • b, x₂ • b)`, a triple of elements of `A`. -/
def toTriple : socLift A →ₗ[R3 k] (Fin 3 → A) where
  toFun b := fun i => ⟨(X i : R3 k) • (b : B), b.2 i⟩
  map_add' b b' := by
    funext i
    exact Subtype.ext (smul_add _ _ _)
  map_smul' c b := by
    funext i
    exact Subtype.ext (smul_comm _ _ _)

lemma coe_toTriple (b : socLift A) :
    (fun i => ((toTriple A b i : A) : B)) = d₃ k B (b : B) := rfl

lemma toTriple_mem_cycles (b : socLift A) : toTriple A b ∈ cycles₂ k A := by
  rw [mem_cycles₂]
  funext i
  apply Subtype.ext
  have h := map_d₂ (A.subtype) (toTriple A b) i
  simp only [Submodule.coe_subtype] at h
  rw [h, coe_toTriple]
  have := congrArg (fun f => f i) (congrArg (fun f => f (b : B)) (d₂_comp_d₃ k B))
  simpa [LinearMap.comp_apply] using this

/-- The connecting map `socLift A → H₂ A`, sending `b` to the class of the
cycle `(x₀ • b, x₁ • b, x₂ • b)`. -/
def toH₂ : socLift A →ₗ[R3 k] H₂ k A where
  toFun b := Submodule.Quotient.mk ⟨toTriple A b, toTriple_mem_cycles A b⟩
  map_add' b b' := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (map_add (toTriple A) b b')
  map_smul' c b := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (map_smul (toTriple A) c b)

lemma toH₂_apply (b : socLift A) :
    toH₂ A b = Submodule.Quotient.mk ⟨toTriple A b, toTriple_mem_cycles A b⟩ := rfl

variable (hinj : Function.Injective (d₃ k B))
  (hex : LinearMap.ker (d₂ k B) = LinearMap.range (d₃ k B))

include hex in
lemma toH₂_surjective : Function.Surjective (toH₂ A) := by
  intro y
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  -- push the cycle down to `B`, where it becomes a boundary
  have hker : (fun i => ((α : Fin 3 → A) i : B)) ∈ LinearMap.ker (d₂ k B) := by
    apply LinearMap.mem_ker.mpr
    funext i
    have h := map_d₂ (A.subtype) (α : Fin 3 → A) i
    simp only [Submodule.coe_subtype] at h
    rw [← h]
    have : d₂ k A (α : Fin 3 → A) = 0 := mem_cycles₂.mp α.2
    simp [this]
  obtain ⟨b, hb⟩ := hex ▸ hker
  have hbmem : b ∈ socLift A := by
    intro i
    have : (X i : R3 k) • b = ((α : Fin 3 → A) i : B) := congrFun hb i
    rw [this]
    exact ((α : Fin 3 → A) i).2
  refine ⟨⟨b, hbmem⟩, ?_⟩
  rw [toH₂_apply]
  congr 1
  apply Subtype.ext
  funext i
  exact Subtype.ext (congrFun hb i)

include hinj in
lemma ker_toH₂ : LinearMap.ker (toH₂ A) = socLiftBase A := by
  ext b
  constructor
  · intro hb
    have hmem : (⟨toTriple A b, toTriple_mem_cycles A b⟩ : cycles₂ k A) ∈
        boundaries₂ k A := by
      have := LinearMap.mem_ker.mp hb
      rwa [toH₂_apply, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨a, ha⟩ := mem_boundaries₂.mp hmem
    -- `d₃ a = d₃ b` in `B`, so `b = a ∈ A`
    have hBa : d₃ k B (a : B) = d₃ k B (b : B) := by
      funext i
      have hi : ((d₃ k A a i : A) : B) = ((toTriple A b i : A) : B) :=
        congrArg (fun t => ((t : A) : B)) (congrFun ha i)
      have hmap := map_d₃ (A.subtype) a i
      simp only [Submodule.coe_subtype] at hmap
      rw [← hmap, hi]
      rfl
    have : (a : B) = (b : B) := hinj hBa
    show (b : B) ∈ A
    rw [← this]
    exact a.2
  · intro hb
    have hbA : (b : B) ∈ A := hb
    apply LinearMap.mem_ker.mpr
    rw [toH₂_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨(b : B), hbA⟩, ?_⟩
    funext i
    exact Subtype.ext rfl

/-- **First connecting isomorphism.**  If `B` is Koszul-acyclic in degrees
two and three — for instance if `B` is free — then the socle of `B ⧸ A` is
the degree-two Koszul homology of `A`. -/
def socle_quotient_equiv_H₂ :
    (LinearMap.ker (d₃ k (B ⧸ A))) ≃ₗ[R3 k] H₂ k A :=
  (LinearMap.quotKerEquivOfSurjective (toSocle A) (toSocle_surjective A)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (by rw [ker_toSocle, ← ker_toH₂ A hinj])).trans
      (LinearMap.quotKerEquivOfSurjective (toH₂ A) (toH₂_surjective A hex)))

end Connecting

end

end Koszul

end LogConcavity

/-! ## Axiom audit -/

#print axioms LogConcavity.Koszul.toH₂_surjective
#print axioms LogConcavity.Koszul.ker_toH₂
#print axioms LogConcavity.Koszul.socle_quotient_equiv_H₂
