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

All three are here, each for a submodule `A ≤ B` with `B` Koszul-acyclic in
the relevant degrees (which holds when `B` is free):

* `socle_quotient_equiv_H₂` : `Soc (B ⧸ A) ≅ H₂ A`, by `b + A ↦ [(xᵢ • b)ᵢ]`;
* `H₂_quotient_equiv_H₁` : `H₂ (B ⧸ A) ≅ H₁ A`, by `[γ] ↦ [d₂ b]` for any
  lift `b` of the cycle `γ`;
* `H₁_quotient_equiv_H₀` : `H₁ (B ⧸ A) ≅ H₀ A = A ⧸ m A`, by `[γ] ↦ [d₁ b]`,
  under the minimality hypothesis `A ≤ m B` which makes the induced map
  `A ⧸ m A → B ⧸ m B` zero.

Each is built the same way: the connecting map is defined on a lift submodule
of `B`, shown surjective using acyclicity of `B`, and its kernel is computed;
the two presentations of that kernel are then glued with
`quotKerEquivOfSurjective`.

Homology transports along an isomorphism (`socleCongr`, `H₂Congr`, `H₁Congr`,
`H₀Congr`), which lets the three steps be chained along a resolution, whose
syzygies are only isomorphic to the relevant quotients.  The result is
`socleEquivH₀OfResolution`: for an exact `F₃ → F₂ → F₁ → F₀ → M → 0` with
`F₀, F₁, F₂` Koszul-acyclic (`Acyclic`, which free modules satisfy by
`acyclic_pi`), `δ₃` injective and minimal,

```
Soc M ≅ F₃ ⧸ m F₃.
```
-/

namespace LogConcavity

namespace Koszul

noncomputable section

universe u v w

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

/-- Koszul homology in degree zero: `M ⧸ m M`. -/
abbrev H₀ := M ⧸ LinearMap.range (d₁ k M)

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

/-! ## Degree-two homology of a quotient is degree-one homology of the submodule -/

section Connecting₁

variable {k : Type u} [Field k] {B : Type v} [AddCommGroup B] [Module (R3 k) B]
  (A : Submodule (R3 k) B)

/-- Triples in `B` whose image under `d₂` lies in `A`: the lift to `B` of the
degree-two cycles of `B ⧸ A`. -/
def cycleLift : Submodule (R3 k) (Fin 3 → B) where
  carrier := {b : Fin 3 → B | ∀ i : Fin 3, d₂ k B b i ∈ A}
  add_mem' {b b'} hb hb' i := by
    simpa [map_add] using A.add_mem (hb i) (hb' i)
  zero_mem' _ := by simp
  smul_mem' c b hb i := by
    simpa [map_smul] using A.smul_mem c (hb i)

lemma mem_cycleLift {b : Fin 3 → B} :
    b ∈ cycleLift A ↔ ∀ i : Fin 3, d₂ k B b i ∈ A :=
  Iff.rfl

/-! ### The `H₂` side -/

/-- The reduction of a lifted cycle modulo `A`. -/
def cycleLiftMod (b : cycleLift A) : Fin 3 → B ⧸ A :=
  fun i => Submodule.Quotient.mk ((b : Fin 3 → B) i)

lemma cycleLiftMod_mem_cycles (b : cycleLift A) : cycleLiftMod A b ∈ cycles₂ k (B ⧸ A) := by
  rw [mem_cycles₂]
  funext i
  have h : (Submodule.Quotient.mk (d₂ k B (b : Fin 3 → B) i) : B ⧸ A) =
      d₂ k (B ⧸ A) (cycleLiftMod A b) i := map_d₂ (A.mkQ) (b : Fin 3 → B) i
  show d₂ k (B ⧸ A) (cycleLiftMod A b) i = 0
  rw [← h, Submodule.Quotient.mk_eq_zero]
  exact b.2 i

/-- `H₂` of the quotient, seen from the lifted cycles. -/
def toH₂Quot : cycleLift A →ₗ[R3 k] H₂ k (B ⧸ A) where
  toFun b := Submodule.Quotient.mk ⟨cycleLiftMod A b, cycleLiftMod_mem_cycles A b⟩
  map_add' b b' := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
  map_smul' c b := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1

lemma toH₂Quot_apply (b : cycleLift A) :
    toH₂Quot A b = Submodule.Quotient.mk ⟨cycleLiftMod A b, cycleLiftMod_mem_cycles A b⟩ :=
  rfl

lemma toH₂Quot_surjective : Function.Surjective (toH₂Quot A) := by
  intro y
  obtain ⟨γ, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  choose b hb using fun i => Submodule.Quotient.mk_surjective A ((γ : Fin 3 → B ⧸ A) i)
  have hmem : b ∈ cycleLift A := by
    intro i
    have h := map_d₂ (A.mkQ) b i
    simp only [Submodule.mkQ_apply] at h
    rw [← Submodule.Quotient.mk_eq_zero, h]
    have : (fun j => Submodule.Quotient.mk (b j) : Fin 3 → B ⧸ A) = (γ : Fin 3 → B ⧸ A) :=
      funext hb
    rw [this]
    exact congrFun (mem_cycles₂.mp γ.2) i
  refine ⟨⟨b, hmem⟩, ?_⟩
  rw [toH₂Quot_apply]
  congr 1
  exact Subtype.ext (funext hb)

/-! ### The `H₁` side -/

/-- `d₂` of a lifted cycle, viewed as a triple of elements of `A`. -/
def cycleLiftBoundary (b : cycleLift A) : Fin 3 → A :=
  fun i => ⟨d₂ k B (b : Fin 3 → B) i, b.2 i⟩

lemma coe_cycleLiftBoundary (b : cycleLift A) :
    (fun i => ((cycleLiftBoundary A b i : A) : B)) = d₂ k B (b : Fin 3 → B) :=
  rfl

lemma cycleLiftBoundary_mem_cycles (b : cycleLift A) :
    cycleLiftBoundary A b ∈ cycles₁ k A := by
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  have h := map_d₁ (A.subtype) (cycleLiftBoundary A b)
  simp only [Submodule.coe_subtype] at h
  rw [h, coe_cycleLiftBoundary]
  have := congrArg (fun f => f (b : Fin 3 → B)) (d₁_comp_d₂ k B)
  simpa [LinearMap.comp_apply] using this

/-- The connecting map `cycleLift A → H₁ A`. -/
def toH₁ : cycleLift A →ₗ[R3 k] H₁ k A where
  toFun b := Submodule.Quotient.mk ⟨cycleLiftBoundary A b, cycleLiftBoundary_mem_cycles A b⟩
  map_add' b b' := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun (map_add (d₂ k B) (b : Fin 3 → B) (b' : Fin 3 → B)) i)
  map_smul' c b := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun (map_smul (d₂ k B) c (b : Fin 3 → B)) i)

lemma toH₁_apply (b : cycleLift A) :
    toH₁ A b = Submodule.Quotient.mk
      ⟨cycleLiftBoundary A b, cycleLiftBoundary_mem_cycles A b⟩ :=
  rfl

variable (hex₂ : LinearMap.ker (d₂ k B) = LinearMap.range (d₃ k B))
  (hex₁ : LinearMap.ker (d₁ k B) = LinearMap.range (d₂ k B))

include hex₁ in
lemma toH₁_surjective : Function.Surjective (toH₁ A) := by
  intro y
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  -- the cycle, read in `B`, is a boundary there
  have hker : (fun i => ((α : Fin 3 → A) i : B)) ∈ LinearMap.ker (d₁ k B) := by
    apply LinearMap.mem_ker.mpr
    have h := map_d₁ (A.subtype) (α : Fin 3 → A)
    simp only [Submodule.coe_subtype] at h
    rw [← h]
    have : d₁ k A (α : Fin 3 → A) = 0 := LinearMap.mem_ker.mp α.2
    simp [this]
  obtain ⟨b, hb⟩ := hex₁ ▸ hker
  have hmem : b ∈ cycleLift A := by
    intro i
    rw [show d₂ k B b i = ((α : Fin 3 → A) i : B) from congrFun hb i]
    exact ((α : Fin 3 → A) i).2
  refine ⟨⟨b, hmem⟩, ?_⟩
  rw [toH₁_apply]
  congr 1
  apply Subtype.ext
  funext i
  exact Subtype.ext (congrFun hb i)

include hex₂ in
lemma ker_toH₂Quot_eq_ker_toH₁ :
    LinearMap.ker (toH₂Quot A) = LinearMap.ker (toH₁ A) := by
  ext b
  simp only [LinearMap.mem_ker, toH₂Quot_apply, toH₁_apply,
    Submodule.Quotient.mk_eq_zero]
  have hz : d₂ k B (d₃ k B (0 : B)) = 0 := by simp
  constructor
  · -- the reduced cycle is a boundary in `B ⧸ A`: subtract a lifted boundary
    rintro ⟨c, hc⟩
    obtain ⟨b₀, rfl⟩ := Submodule.Quotient.mk_surjective A c
    have hd₃ : ∀ i, (Submodule.Quotient.mk (d₃ k B b₀ i) : B ⧸ A) =
        d₃ k (B ⧸ A) (Submodule.Quotient.mk b₀) i := fun i => map_d₃ (A.mkQ) b₀ i
    have hdiff : ∀ i, (b : Fin 3 → B) i - d₃ k B b₀ i ∈ A := by
      intro i
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero,
        hd₃ i, congrFun hc i]
      rfl
    -- so `d₂ b = d₂ (b - d₃ b₀)` is the boundary of a triple in `A`
    set α : Fin 3 → A := fun j => ⟨(b : Fin 3 → B) j - d₃ k B b₀ j, hdiff j⟩ with hαdef
    refine ⟨α, ?_⟩
    funext i
    apply Subtype.ext
    have h := map_d₂ (A.subtype) α i
    simp only [Submodule.coe_subtype] at h
    rw [h, show (fun j => ((α j : A) : B)) = (b : Fin 3 → B) - d₃ k B b₀ from rfl, map_sub]
    have hzero : d₂ k B (d₃ k B b₀) = 0 := by
      have := congrArg (fun f => f b₀) (d₂_comp_d₃ k B)
      simpa [LinearMap.comp_apply] using this
    rw [hzero]
    simp [cycleLiftBoundary]
  · -- conversely a boundary in `A` exhibits the reduced cycle as `d₃` of a class
    rintro ⟨α, hα⟩
    have hcomp : ∀ i, d₂ k B (fun j => ((α j : A) : B)) i = d₂ k B (b : Fin 3 → B) i := by
      intro i
      have h : ((d₂ k A α i : A) : B) = d₂ k B (fun j => ((α j : A) : B)) i :=
        map_d₂ (A.subtype) α i
      rw [← h, show d₂ k A α i = cycleLiftBoundary A b i from congrFun hα i]
      rfl
    have hdiff : d₂ k B ((b : Fin 3 → B) - fun i => ((α i : A) : B)) = 0 := by
      funext i
      rw [map_sub]
      simp [hcomp i]
    obtain ⟨b₀, hb₀⟩ := hex₂ ▸ (LinearMap.mem_ker.mpr hdiff)
    refine ⟨Submodule.Quotient.mk b₀, ?_⟩
    funext i
    have h : (Submodule.Quotient.mk (d₃ k B b₀ i) : B ⧸ A) =
        d₃ k (B ⧸ A) (Submodule.Quotient.mk b₀) i := map_d₃ (A.mkQ) b₀ i
    rw [← h, show d₃ k B b₀ i = (b : Fin 3 → B) i - ((α i : A) : B) from congrFun hb₀ i,
      Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero A).mpr ((α i : A)).2,
      sub_zero]
    rfl

/-- **Second connecting isomorphism.**  If `B` is Koszul-acyclic in degrees
one, two and three — for instance if `B` is free — then the degree-two
homology of `B ⧸ A` is the degree-one homology of `A`. -/
def H₂_quotient_equiv_H₁ : H₂ k (B ⧸ A) ≃ₗ[R3 k] H₁ k A :=
  (LinearMap.quotKerEquivOfSurjective (toH₂Quot A) (toH₂Quot_surjective A)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_toH₂Quot_eq_ker_toH₁ A hex₂)).trans
      (LinearMap.quotKerEquivOfSurjective (toH₁ A) (toH₁_surjective A hex₁)))

end Connecting₁


/-! ## Degree-one homology of a quotient is degree-zero homology of the submodule

In the generality needed here the submodule `A` sits inside `m B` — that is
minimality of the resolution — which makes the induced map `A ⧸ m A → B ⧸ m B`
zero and so identifies `H₁ (B ⧸ A)` with all of `H₀ A`. -/

section Connecting₀

variable {k : Type u} [Field k] {B : Type v} [AddCommGroup B] [Module (R3 k) B]
  (A : Submodule (R3 k) B)

/-- Triples in `B` whose image under `d₁` lies in `A`: the lift to `B` of the
degree-one cycles of `B ⧸ A`. -/
def cycleLift₁ : Submodule (R3 k) (Fin 3 → B) where
  carrier := {b : Fin 3 → B | d₁ k B b ∈ A}
  add_mem' {b b'} hb hb' := by simpa [map_add] using A.add_mem hb hb'
  zero_mem' := by simp
  smul_mem' c b hb := by simpa [map_smul] using A.smul_mem c hb

lemma mem_cycleLift₁ {b : Fin 3 → B} : b ∈ cycleLift₁ A ↔ d₁ k B b ∈ A :=
  Iff.rfl

/-! ### The `H₁` side -/

lemma cycleLift₁Mod_mem_cycles (b : cycleLift₁ A) :
    (fun i => Submodule.Quotient.mk ((b : Fin 3 → B) i) : Fin 3 → B ⧸ A) ∈
      cycles₁ k (B ⧸ A) := by
  apply LinearMap.mem_ker.mpr
  have h : (Submodule.Quotient.mk (d₁ k B (b : Fin 3 → B)) : B ⧸ A) =
      d₁ k (B ⧸ A) (fun i => Submodule.Quotient.mk ((b : Fin 3 → B) i)) :=
    map_d₁ (A.mkQ) (b : Fin 3 → B)
  rw [← h, Submodule.Quotient.mk_eq_zero]
  exact b.2

/-- `H₁` of the quotient, seen from the lifted cycles. -/
def toH₁Quot : cycleLift₁ A →ₗ[R3 k] H₁ k (B ⧸ A) where
  toFun b := Submodule.Quotient.mk
    ⟨fun i => Submodule.Quotient.mk ((b : Fin 3 → B) i), cycleLift₁Mod_mem_cycles A b⟩
  map_add' b b' := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
  map_smul' c b := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1

lemma toH₁Quot_apply (b : cycleLift₁ A) :
    toH₁Quot A b = Submodule.Quotient.mk
      ⟨fun i => Submodule.Quotient.mk ((b : Fin 3 → B) i), cycleLift₁Mod_mem_cycles A b⟩ :=
  rfl

lemma toH₁Quot_surjective : Function.Surjective (toH₁Quot A) := by
  intro y
  obtain ⟨γ, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  choose b hb using fun i => Submodule.Quotient.mk_surjective A ((γ : Fin 3 → B ⧸ A) i)
  have hmem : b ∈ cycleLift₁ A := by
    rw [mem_cycleLift₁, ← Submodule.Quotient.mk_eq_zero]
    have h : (Submodule.Quotient.mk (d₁ k B b) : B ⧸ A) =
        d₁ k (B ⧸ A) (fun i => Submodule.Quotient.mk (b i)) := map_d₁ (A.mkQ) b
    rw [h, show (fun i => Submodule.Quotient.mk (b i) : Fin 3 → B ⧸ A) =
      (γ : Fin 3 → B ⧸ A) from funext hb]
    exact LinearMap.mem_ker.mp γ.2
  refine ⟨⟨b, hmem⟩, ?_⟩
  rw [toH₁Quot_apply]
  congr 1
  exact Subtype.ext (funext hb)

/-! ### The `H₀` side -/

/-- The connecting map `cycleLift₁ A → H₀ A`, sending a lifted cycle `b` to
the class of `d₁ b`. -/
def toH₀ : cycleLift₁ A →ₗ[R3 k] H₀ k A where
  toFun b := Submodule.Quotient.mk ⟨d₁ k B (b : Fin 3 → B), b.2⟩
  map_add' b b' := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (map_add (d₁ k B) (b : Fin 3 → B) (b' : Fin 3 → B))
  map_smul' c b := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (map_smul (d₁ k B) c (b : Fin 3 → B))

lemma toH₀_apply (b : cycleLift₁ A) :
    toH₀ A b = Submodule.Quotient.mk ⟨d₁ k B (b : Fin 3 → B), b.2⟩ :=
  rfl

variable (hex₁ : LinearMap.ker (d₁ k B) = LinearMap.range (d₂ k B))
  (hmin : A ≤ LinearMap.range (d₁ k B))

include hmin in
lemma toH₀_surjective : Function.Surjective (toH₀ A) := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨b, hb⟩ := hmin a.2
  have hmem : b ∈ cycleLift₁ A := by
    rw [mem_cycleLift₁, hb]
    exact a.2
  refine ⟨⟨b, hmem⟩, ?_⟩
  rw [toH₀_apply]
  congr 1
  exact Subtype.ext hb

include hex₁ in
lemma ker_toH₁Quot_eq_ker_toH₀ :
    LinearMap.ker (toH₁Quot A) = LinearMap.ker (toH₀ A) := by
  ext b
  simp only [LinearMap.mem_ker, toH₁Quot_apply, toH₀_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨c, hc⟩
    choose b₀ hb₀ using fun i => Submodule.Quotient.mk_surjective A (c i)
    have hcfun : (fun j => Submodule.Quotient.mk (b₀ j) : Fin 3 → B ⧸ A) = c := funext hb₀
    have hd₂ : ∀ i, (Submodule.Quotient.mk (d₂ k B b₀ i) : B ⧸ A) = d₂ k (B ⧸ A) c i := by
      intro i
      rw [← hcfun]
      exact map_d₂ (A.mkQ) b₀ i
    have hdiff : ∀ i, (b : Fin 3 → B) i - d₂ k B b₀ i ∈ A := by
      intro i
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero,
        hd₂ i, congrFun hc i]
      rfl
    set α : Fin 3 → A := fun i => ⟨(b : Fin 3 → B) i - d₂ k B b₀ i, hdiff i⟩ with hαdef
    refine ⟨α, ?_⟩
    apply Subtype.ext
    have h := map_d₁ (A.subtype) α
    simp only [Submodule.coe_subtype] at h
    rw [h, show (fun j => ((α j : A) : B)) = (b : Fin 3 → B) - d₂ k B b₀ from rfl, map_sub]
    have hzero : d₁ k B (d₂ k B b₀) = 0 := by
      have := congrArg (fun f => f b₀) (d₁_comp_d₂ k B)
      simpa [LinearMap.comp_apply] using this
    rw [hzero, sub_zero]
  · rintro ⟨α, hα⟩
    have hcomp : d₁ k B (fun j => ((α j : A) : B)) = d₁ k B (b : Fin 3 → B) := by
      have h := map_d₁ (A.subtype) α
      simp only [Submodule.coe_subtype] at h
      rw [← h, show d₁ k A α = (⟨d₁ k B (b : Fin 3 → B), b.2⟩ : A) from hα]
    have hdiff : d₁ k B ((b : Fin 3 → B) - fun i => ((α i : A) : B)) = 0 := by
      rw [map_sub, hcomp, sub_self]
    obtain ⟨b₀, hb₀⟩ := hex₁ ▸ (LinearMap.mem_ker.mpr hdiff)
    refine ⟨fun i => Submodule.Quotient.mk (b₀ i), ?_⟩
    funext i
    have h : (Submodule.Quotient.mk (d₂ k B b₀ i) : B ⧸ A) =
        d₂ k (B ⧸ A) (fun j => Submodule.Quotient.mk (b₀ j)) i := map_d₂ (A.mkQ) b₀ i
    rw [← h, show d₂ k B b₀ i = (b : Fin 3 → B) i - ((α i : A) : B) from congrFun hb₀ i,
      Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero A).mpr ((α i : A)).2,
      sub_zero]
    rfl

/-- **Third connecting isomorphism.**  If `B` is Koszul-acyclic in degree one
and `A` lies inside `m B` — minimality — then the degree-one homology of
`B ⧸ A` is `A ⧸ m A`. -/
def H₁_quotient_equiv_H₀ : H₁ k (B ⧸ A) ≃ₗ[R3 k] H₀ k A :=
  (LinearMap.quotKerEquivOfSurjective (toH₁Quot A) (toH₁Quot_surjective A)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_toH₁Quot_eq_ker_toH₀ A hex₁)).trans
      (LinearMap.quotKerEquivOfSurjective (toH₀ A) (toH₀_surjective A hmin)))

end Connecting₀


/-! ## Transport along an isomorphism

The three connecting isomorphisms above relate a submodule to an explicit
quotient, whereas along a resolution the syzygies are only *isomorphic* to
those quotients.  These lemmas move Koszul homology across an isomorphism so
that the three steps can be chained. -/

section Transport

variable {k : Type u} [Field k] {M N : Type v} [AddCommGroup M] [Module (R3 k) M]
  [AddCommGroup N] [Module (R3 k) N] (e : M ≃ₗ[R3 k] N)

/-- The socle transports along an isomorphism. -/
def socleCongr : LinearMap.ker (d₃ k M) ≃ₗ[R3 k] LinearMap.ker (d₃ k N) where
  toFun m := ⟨e (m : M), by
    rw [mem_ker_d₃_iff]
    intro i
    rw [← map_smul, (mem_ker_d₃_iff _).mp m.2 i, map_zero]⟩
  invFun n := ⟨e.symm (n : N), by
    rw [mem_ker_d₃_iff]
    intro i
    rw [← map_smul, (mem_ker_d₃_iff _).mp n.2 i, map_zero]⟩
  map_add' m m' := Subtype.ext (map_add e _ _)
  map_smul' c m := Subtype.ext (map_smul e _ _)
  left_inv m := Subtype.ext (e.symm_apply_apply _)
  right_inv n := Subtype.ext (e.apply_symm_apply _)

/-! ### Degree two -/

lemma map_mem_cycles₂ {g : Fin 3 → M} (hg : g ∈ cycles₂ k M) :
    (fun i => e (g i)) ∈ cycles₂ k N := by
  rw [mem_cycles₂]
  funext i
  have h : e (d₂ k M g i) = d₂ k N (fun j => e (g j)) i := map_d₂ (e : M →ₗ[R3 k] N) g i
  rw [← h, show d₂ k M g = 0 from mem_cycles₂.mp hg]
  simp

/-- Transport of degree-two cycles into the homology of the target. -/
def toH₂Congr : cycles₂ k M →ₗ[R3 k] H₂ k N where
  toFun g := Submodule.Quotient.mk
    ⟨fun i => e ((g : Fin 3 → M) i), map_mem_cycles₂ e g.2⟩
  map_add' g g' := by
    rw [← Submodule.Quotient.mk_add]
    exact congrArg _ (Subtype.ext (funext fun i => map_add e _ _))
  map_smul' c g := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun i => map_smul e _ _))

lemma toH₂Congr_apply (g : cycles₂ k M) :
    toH₂Congr e g = Submodule.Quotient.mk
      ⟨fun i => e ((g : Fin 3 → M) i), map_mem_cycles₂ e g.2⟩ :=
  rfl

lemma toH₂Congr_surjective : Function.Surjective (toH₂Congr e) := by
  intro y
  obtain ⟨γ, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmem : (fun i => e.symm ((γ : Fin 3 → N) i)) ∈ cycles₂ k M :=
    map_mem_cycles₂ e.symm γ.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [toH₂Congr_apply]
  exact congrArg _ (Subtype.ext (funext fun i => e.apply_symm_apply _))

lemma ker_toH₂Congr : LinearMap.ker (toH₂Congr e) = boundaries₂ k M := by
  ext g
  simp only [LinearMap.mem_ker, toH₂Congr_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨e.symm n, ?_⟩
    funext i
    have h : e.symm (d₃ k N n i) = d₃ k M (e.symm n) i := map_d₃ (e.symm : N →ₗ[R3 k] M) n i
    rw [← h, show d₃ k N n i = e ((g : Fin 3 → M) i) from congrFun hn i,
      e.symm_apply_apply]
    rfl
  · rintro ⟨m, hm⟩
    refine ⟨e m, ?_⟩
    funext i
    have h : e (d₃ k M m i) = d₃ k N (e m) i := map_d₃ (e : M →ₗ[R3 k] N) m i
    rw [← h, show d₃ k M m i = (g : Fin 3 → M) i from congrFun hm i]
    rfl

/-- Degree-two Koszul homology transports along an isomorphism. -/
def H₂Congr : H₂ k M ≃ₗ[R3 k] H₂ k N :=
  (Submodule.quotEquivOfEq _ _ (ker_toH₂Congr e).symm).trans
    (LinearMap.quotKerEquivOfSurjective (toH₂Congr e) (toH₂Congr_surjective e))

/-! ### Degree one -/

lemma map_mem_cycles₁ {g : Fin 3 → M} (hg : g ∈ cycles₁ k M) :
    (fun i => e (g i)) ∈ cycles₁ k N := by
  apply LinearMap.mem_ker.mpr
  have h : e (d₁ k M g) = d₁ k N (fun j => e (g j)) := map_d₁ (e : M →ₗ[R3 k] N) g
  rw [← h, show d₁ k M g = 0 from LinearMap.mem_ker.mp hg]
  simp

/-- Transport of degree-one cycles into the homology of the target. -/
def toH₁Congr : cycles₁ k M →ₗ[R3 k] H₁ k N where
  toFun g := Submodule.Quotient.mk
    ⟨fun i => e ((g : Fin 3 → M) i), map_mem_cycles₁ e g.2⟩
  map_add' g g' := by
    rw [← Submodule.Quotient.mk_add]
    exact congrArg _ (Subtype.ext (funext fun i => map_add e _ _))
  map_smul' c g := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun i => map_smul e _ _))

lemma toH₁Congr_apply (g : cycles₁ k M) :
    toH₁Congr e g = Submodule.Quotient.mk
      ⟨fun i => e ((g : Fin 3 → M) i), map_mem_cycles₁ e g.2⟩ :=
  rfl

lemma toH₁Congr_surjective : Function.Surjective (toH₁Congr e) := by
  intro y
  obtain ⟨γ, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmem : (fun i => e.symm ((γ : Fin 3 → N) i)) ∈ cycles₁ k M :=
    map_mem_cycles₁ e.symm γ.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [toH₁Congr_apply]
  exact congrArg _ (Subtype.ext (funext fun i => e.apply_symm_apply _))

lemma ker_toH₁Congr : LinearMap.ker (toH₁Congr e) = boundaries₁ k M := by
  ext g
  simp only [LinearMap.mem_ker, toH₁Congr_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨fun i => e.symm (n i), ?_⟩
    funext i
    have h : e.symm (d₂ k N n i) = d₂ k M (fun j => e.symm (n j)) i :=
      map_d₂ (e.symm : N →ₗ[R3 k] M) n i
    rw [← h, show d₂ k N n i = e ((g : Fin 3 → M) i) from congrFun hn i,
      e.symm_apply_apply]
    rfl
  · rintro ⟨m, hm⟩
    refine ⟨fun i => e (m i), ?_⟩
    funext i
    have h : e (d₂ k M m i) = d₂ k N (fun j => e (m j)) i :=
      map_d₂ (e : M →ₗ[R3 k] N) m i
    rw [← h, show d₂ k M m i = (g : Fin 3 → M) i from congrFun hm i]
    rfl

/-- Degree-one Koszul homology transports along an isomorphism. -/
def H₁Congr : H₁ k M ≃ₗ[R3 k] H₁ k N :=
  (Submodule.quotEquivOfEq _ _ (ker_toH₁Congr e).symm).trans
    (LinearMap.quotKerEquivOfSurjective (toH₁Congr e) (toH₁Congr_surjective e))

/-! ### Degree zero -/

/-- Transport into degree-zero homology of the target. -/
def toH₀Congr : M →ₗ[R3 k] H₀ k N where
  toFun m := Submodule.Quotient.mk (e m)
  map_add' m m' := by rw [← Submodule.Quotient.mk_add]; exact congrArg _ (map_add e _ _)
  map_smul' c m := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (map_smul e _ _)

lemma toH₀Congr_apply (m : M) : toH₀Congr e m = Submodule.Quotient.mk (e m) := rfl

lemma toH₀Congr_surjective : Function.Surjective (toH₀Congr e) := by
  intro y
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨e.symm n, congrArg _ (e.apply_symm_apply n)⟩

lemma ker_toH₀Congr : LinearMap.ker (toH₀Congr e) = LinearMap.range (d₁ k M) := by
  ext m
  simp only [LinearMap.mem_ker, toH₀Congr_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun i => e.symm (g i), ?_⟩
    have h : e.symm (d₁ k N g) = d₁ k M (fun j => e.symm (g j)) :=
      map_d₁ (e.symm : N →ₗ[R3 k] M) g
    rw [← h, hg, e.symm_apply_apply]
  · rintro ⟨g, hg⟩
    refine ⟨fun i => e (g i), ?_⟩
    have h : e (d₁ k M g) = d₁ k N (fun j => e (g j)) := map_d₁ (e : M →ₗ[R3 k] N) g
    rw [← h, hg]

/-- Degree-zero Koszul homology transports along an isomorphism. -/
def H₀Congr : H₀ k M ≃ₗ[R3 k] H₀ k N :=
  (Submodule.quotEquivOfEq _ _ (ker_toH₀Congr e).symm).trans
    (LinearMap.quotKerEquivOfSurjective (toH₀Congr e) (toH₀Congr_surjective e))

end Transport


/-! ## The chain along a minimal free resolution

Putting the three connecting isomorphisms and the transports together: for a
length-three resolution of `M` by Koszul-acyclic modules whose last
differential is minimal, the socle of `M` is `F₃ ⧸ m F₃`. -/

section Resolution

/-- Koszul-acyclicity in positive degrees.  Free modules have it, by
`Koszul.d₃_pi_injective`, `Koszul.ker_d₂_eq_range_d₃_pi` and
`Koszul.ker_d₁_eq_range_d₂_pi`. -/
structure Acyclic (k : Type u) [Field k] (F : Type v) [AddCommGroup F]
    [Module (R3 k) F] : Prop where
  d₃_injective : Function.Injective (d₃ k F)
  exact₂ : LinearMap.ker (d₂ k F) = LinearMap.range (d₃ k F)
  exact₁ : LinearMap.ker (d₁ k F) = LinearMap.range (d₂ k F)

lemma acyclic_pi {k : Type u} [Field k] {ι : Type w} : Acyclic k (ι → R3 k) :=
  { d₃_injective := d₃_pi_injective
    exact₂ := ker_d₂_eq_range_d₃_pi
    exact₁ := ker_d₁_eq_range_d₂_pi }

variable {k : Type u} [Field k] {F₀ F₁ F₂ F₃ M : Type v}
  [AddCommGroup F₀] [Module (R3 k) F₀] [AddCommGroup F₁] [Module (R3 k) F₁]
  [AddCommGroup F₂] [Module (R3 k) F₂] [AddCommGroup F₃] [Module (R3 k) F₃]
  [AddCommGroup M] [Module (R3 k) M]

/-- **The socle of a resolved module is the top of its resolution.**  Given an
exact sequence `F₃ → F₂ → F₁ → F₀ → M → 0` with `F₀`, `F₁`, `F₂`
Koszul-acyclic (e.g. free), `δ₃` injective, and the last differential minimal
in the sense that its image lies in `m F₂`, the socle of `M` is `F₃ ⧸ m F₃`.

For a minimal free resolution the right-hand side is `k^{β₃}`, so this is the
statement that the last Betti number is the type of `M`. -/
def socleEquivH₀OfResolution
    (δ₁ : F₁ →ₗ[R3 k] F₀) (δ₂ : F₂ →ₗ[R3 k] F₁) (δ₃ : F₃ →ₗ[R3 k] F₂)
    (p : F₀ →ₗ[R3 k] M) (hp : Function.Surjective p)
    (hZ₁ : LinearMap.ker p = LinearMap.range δ₁)
    (hZ₂ : LinearMap.ker δ₁ = LinearMap.range δ₂)
    (hZ₃ : LinearMap.ker δ₂ = LinearMap.range δ₃)
    (hδ₃ : Function.Injective δ₃)
    (hmin : LinearMap.range δ₃ ≤ LinearMap.range (d₁ k F₂))
    (hF₀ : Acyclic k F₀) (hF₁ : Acyclic k F₁) (hF₂ : Acyclic k F₂) :
    LinearMap.ker (d₃ k M) ≃ₗ[R3 k] H₀ k F₃ := by
  -- `M ≅ F₀ ⧸ im δ₁`, so the socle of `M` is `H₂` of the first syzygy
  have e₀ : M ≃ₗ[R3 k] F₀ ⧸ LinearMap.range δ₁ :=
    (LinearMap.quotKerEquivOfSurjective p hp).symm.trans
      (Submodule.quotEquivOfEq _ _ hZ₁)
  have s₁ : LinearMap.ker (d₃ k M) ≃ₗ[R3 k]
      LinearMap.ker (d₃ k (F₀ ⧸ LinearMap.range δ₁)) := socleCongr e₀
  have s₂ : LinearMap.ker (d₃ k (F₀ ⧸ LinearMap.range δ₁)) ≃ₗ[R3 k]
      H₂ k (LinearMap.range δ₁) :=
    socle_quotient_equiv_H₂ (LinearMap.range δ₁) hF₀.d₃_injective hF₀.exact₂
  -- `im δ₁ ≅ F₁ ⧸ im δ₂`, so that `H₂` becomes `H₁` of the second syzygy
  have e₁ : (LinearMap.range δ₁) ≃ₗ[R3 k] F₁ ⧸ LinearMap.range δ₂ :=
    (LinearMap.quotKerEquivRange δ₁).symm.trans (Submodule.quotEquivOfEq _ _ hZ₂)
  have s₃ : H₂ k (LinearMap.range δ₁) ≃ₗ[R3 k] H₂ k (F₁ ⧸ LinearMap.range δ₂) :=
    H₂Congr e₁
  have s₄ : H₂ k (F₁ ⧸ LinearMap.range δ₂) ≃ₗ[R3 k] H₁ k (LinearMap.range δ₂) :=
    H₂_quotient_equiv_H₁ (LinearMap.range δ₂) hF₁.exact₂ hF₁.exact₁
  -- `im δ₂ ≅ F₂ ⧸ im δ₃`, so that `H₁` becomes `H₀` of the last syzygy
  have e₂ : (LinearMap.range δ₂) ≃ₗ[R3 k] F₂ ⧸ LinearMap.range δ₃ :=
    (LinearMap.quotKerEquivRange δ₂).symm.trans (Submodule.quotEquivOfEq _ _ hZ₃)
  have s₅ : H₁ k (LinearMap.range δ₂) ≃ₗ[R3 k] H₁ k (F₂ ⧸ LinearMap.range δ₃) :=
    H₁Congr e₂
  have s₆ : H₁ k (F₂ ⧸ LinearMap.range δ₃) ≃ₗ[R3 k] H₀ k (LinearMap.range δ₃) :=
    H₁_quotient_equiv_H₀ (LinearMap.range δ₃) hF₂.exact₁ hmin
  -- and `im δ₃ ≅ F₃`
  have s₇ : H₀ k (LinearMap.range δ₃) ≃ₗ[R3 k] H₀ k F₃ :=
    H₀Congr (LinearEquiv.ofInjective δ₃ hδ₃).symm
  exact s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans s₇)))))

end Resolution


end

end Koszul

end LogConcavity

/-! ## Axiom audit -/

#print axioms LogConcavity.Koszul.toH₂_surjective
#print axioms LogConcavity.Koszul.ker_toH₂
#print axioms LogConcavity.Koszul.socle_quotient_equiv_H₂
#print axioms LogConcavity.Koszul.toH₁_surjective
#print axioms LogConcavity.Koszul.ker_toH₂Quot_eq_ker_toH₁
#print axioms LogConcavity.Koszul.H₂_quotient_equiv_H₁
#print axioms LogConcavity.Koszul.toH₀_surjective
#print axioms LogConcavity.Koszul.ker_toH₁Quot_eq_ker_toH₀
#print axioms LogConcavity.Koszul.H₁_quotient_equiv_H₀
#print axioms LogConcavity.Koszul.socleCongr
#print axioms LogConcavity.Koszul.H₂Congr
#print axioms LogConcavity.Koszul.H₁Congr
#print axioms LogConcavity.Koszul.H₀Congr
#print axioms LogConcavity.Koszul.acyclic_pi
#print axioms LogConcavity.Koszul.socleEquivH₀OfResolution
