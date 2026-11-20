import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
open scoped Pointwise

namespace GlobalTheory.UnitLemma.StabIndex

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

/- English proof (translation)
Use extensionality with `y`. Simplify using `[mulLat, Submodule.mem_smul_pointwise_iff_exists, Units.smul_def]`.
-/
theorem smul_eq_mulLat (t : Aˣ) (L : Submodule O A) : t • L = mulLat O (t : A) L := by
  ext y
  simp [mulLat, Submodule.mem_smul_pointwise_iff_exists, Units.smul_def]

/- English proof (translation)
Establish `key : ∀ y, y ∈ t • L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L`. Introduce `y`. Rewrite using `[smul_eq_mulLat]`. Simplify using `only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨b, hb, rfl⟩`. Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]`. Conclude with `hb`. Introduce `h`. Conclude with `⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `ht`. Use extensionality with `y`. Rewrite using `[key, ht (((t⁻¹ : Aˣ) : A) * y), ← mul_assoc, Units.mul_inv, one_mul]`. Introduce `ht y`.

Use `key ((t : A) * y)` as an intermediate fact. Rewrite `this` using `[ht, ← mul_assoc, Units.inv_mul, one_mul]`. Conclude with `this.symm`.
-/
theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) : t ∈ stabLat O L ↔ t • L = L := by
  have key : ∀ y, y ∈ t • L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
    intro y
    rw [smul_eq_mulLat]
    simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [← mul_assoc, Units.inv_mul, one_mul]; exact hb
    · intro h
      exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
  constructor
  · intro ht
    ext y
    rw [key, ht (((t⁻¹ : Aˣ) : A) * y), ← mul_assoc, Units.mul_inv, one_mul]
  · intro ht y
    have := key ((t : A) * y)
    rw [ht, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this.symm

end GlobalTheory.UnitLemma.StabIndex

namespace GlobalTheory.UnitLemma.StabIndex

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A]`. Use `(isUnit_iff_ne_zero.mpr ?_).map (algebraMap K.E B.A)` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).mpr hc`.
-/
theorem isUnit_algebraMap (K : UQ) (B : InvAlg K) (c : K.O) (hc : c ≠ 0) :
    IsUnit (algebraMap K.O B.A c) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine (isUnit_iff_ne_zero.mpr ?_).map (algebraMap K.E B.A)
  exact (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).mpr hc

/- English proof (translation)
Use `set G := intUnits K.O B.A ⊓ B.T`. Use `set γ : B.Aˣ := (isUnit_algebraMap K B c hc).unit`. Establish `hγ : (γ : B.A) = algebraMap K.O B.A c` using `rfl`. Establish `hsub : (stabLat K.O L ⊓ B.T).subgroupOf G = MulAction.stabilizer G L`. Use extensionality with `u`.

Rewrite using `[Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Subgroup.smul_def, ← mem_stabLat_iff]`. Conclude with `⟨fun hu => hu.1, fun hu => ⟨hu, (Subgroup.mem_inf.mp u.2).2⟩⟩`. Establish `horb : (MulAction.orbit G L).Finite`. Use `(hfin.preimage (MulAction.injective γ).injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`.

Establish `hu` using `(Subgroup.mem_inf.mp u.2).1`. Establish `hM : γ • ((u : B.Aˣ) • L) = mulLat K.O (algebraMap K.O B.A c * ((u : B.Aˣ) : B.A)) L`. Rewrite using `[smul_smul, smul_eq_mulLat, Units.val_mul, hγ]`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, hM]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `⟨algebraMap K.O B.A c * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * y, h _ hu.2 y hy, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.mulLeft_apply, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Simplify using `only [LinearMap.mulLeft_apply]`. Conclude with `h _ hu.1 y hy`. Rewrite using `[Subgroup.relIndex, hsub]`. Use `haveI : Finite (MulAction.orbit G L) := horb.to_subtype`. Use `haveI : Finite (G ⧸ MulAction.stabilizer G L) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G L)`.

Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_between (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (c : K.O) (hc : c ≠ 0)
    (hfin : {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (c * c)) L ≤ M ∧ M ≤ L}.Finite)
    (h : ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) :
    (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  set G := intUnits K.O B.A ⊓ B.T
  set γ : B.Aˣ := (isUnit_algebraMap K B c hc).unit
  have hγ : (γ : B.A) = algebraMap K.O B.A c := rfl
  have hsub : (stabLat K.O L ⊓ B.T).subgroupOf G = MulAction.stabilizer G L := by
    ext u
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Subgroup.smul_def,
      ← mem_stabLat_iff]
    exact ⟨fun hu => hu.1, fun hu => ⟨hu, (Subgroup.mem_inf.mp u.2).2⟩⟩
  have horb : (MulAction.orbit G L).Finite := by
    refine (hfin.preimage (MulAction.injective γ).injOn).subset ?_
    rintro _ ⟨u, rfl⟩
    have hu := (Subgroup.mem_inf.mp u.2).1
    have hM : γ • ((u : B.Aˣ) • L) = mulLat K.O (algebraMap K.O B.A c * ((u : B.Aˣ) : B.A)) L := by
      rw [smul_smul, smul_eq_mulLat, Units.val_mul, hγ]
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, hM]
    constructor
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨algebraMap K.O B.A c * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * y, h _ hu.2 y hy, ?_⟩
      simp only [LinearMap.mulLeft_apply, map_mul]
      calc algebraMap K.O B.A c * ((u : B.Aˣ) : B.A) * (algebraMap K.O B.A c * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * y)
          = algebraMap K.O B.A c * algebraMap K.O B.A c * (((u : B.Aˣ) : B.A) * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A)) * y := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    · rintro _ ⟨y, hy, rfl⟩
      simp only [LinearMap.mulLeft_apply]
      exact h _ hu.1 y hy
  rw [Subgroup.relIndex, hsub]
  haveI : Finite (MulAction.orbit G L) := horb.to_subtype
  haveI : Finite (G ⧸ MulAction.stabilizer G L) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G L)
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.UnitLemma.StabIndex
