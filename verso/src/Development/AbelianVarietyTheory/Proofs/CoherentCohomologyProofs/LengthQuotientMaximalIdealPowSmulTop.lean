import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

open Pointwise

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Set `g : M →ₗ[R] (ι → R ⧸ Ideal.span {a})` to `LinearMap.pi fun i => (Ideal.span {a} : Ideal R).mkQ ∘ₗ b.coord i`. Establish `hg : ∀ x i, g x i = Ideal.Quotient.mk (Ideal.span {a}) (b.repr x i)` using `fun _ _ => rfl`. Establish `hs : Function.Surjective g`. Introduce `y`. Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)`.

Use `⟨b.equivFun.symm c, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hg, ← hc i, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]`. Establish `hk : (a • ⊤ : Submodule R M) = LinearMap.ker g`. Use extensionality with `x`. Rewrite using `[Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, funext_iff]`.

Simplify using `only [hg, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, rfl⟩ i`. Conclude with `⟨b.repr y i, by simp [mul_comm]⟩`. Introduce `h choose c hc using h`.

Use `⟨b.equivFun.symm c, trivial, b.equivFun.injective (funext fun i => ?_)⟩` and prove the remaining obligations. Rewrite using `[map_smul, LinearEquiv.apply_symm_apply, b.equivFun_apply, ← hc i, Pi.smul_apply, smul_eq_mul, mul_comm]`. Conclude with `⟨Submodule.quotEquivOfEq _ _ hk ≪≫ₗ g.quotKerEquivOfSurjective hs⟩`.
-/
theorem nonempty_quotient_smul_top_equiv_pi {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (a : R) :
    Nonempty ((M ⧸ (a • ⊤ : Submodule R M)) ≃ₗ[R] (ι → R ⧸ Ideal.span {a})) := by
  let g : M →ₗ[R] (ι → R ⧸ Ideal.span {a}) :=
    LinearMap.pi fun i => (Ideal.span {a} : Ideal R).mkQ ∘ₗ b.coord i
  have hg : ∀ x i, g x i = Ideal.Quotient.mk (Ideal.span {a}) (b.repr x i) := fun _ _ => rfl
  have hs : Function.Surjective g := by
    intro y
    choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm c, funext fun i => ?_⟩
    rw [hg, ← hc i, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hk : (a • ⊤ : Submodule R M) = LinearMap.ker g := by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, funext_iff]
    simp only [hg, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, -, rfl⟩ i
      exact ⟨b.repr y i, by simp [mul_comm]⟩
    · intro h
      choose c hc using h
      refine ⟨b.equivFun.symm c, trivial, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_smul, LinearEquiv.apply_symm_apply, b.equivFun_apply, ← hc i, Pi.smul_apply,
        smul_eq_mul, mul_comm]
  exact ⟨Submodule.quotEquivOfEq _ _ hk ≪≫ₗ g.quotKerEquivOfSurjective hs⟩

/- English proof (translation)
Rewrite using `[(nonempty_quotient_smul_top_equiv_pi (Module.finBasis R M) a).some.length_eq, Module.length_pi, mul_comm]`. Simplify using the standard rewrite rules.
-/
theorem length_quotient_smul_top_of_free [Nontrivial R] [Module.Free R M] [Module.Finite R M]
    (a : R) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) =
      Module.length R (R ⧸ Ideal.span {a}) * (Module.finrank R M : ℕ∞) := by
  rw [(nonempty_quotient_smul_top_equiv_pi (Module.finBasis R M) a).some.length_eq,
    Module.length_pi, mul_comm]
  simp

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Submodule.submoduleOf, Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Conclude with `⟨⟨y, hy⟩, trivial, Subtype.ext h⟩`.

Introduce and unpack `⟨y, -, rfl⟩`. Conclude with `⟨y, y.2, rfl⟩`.
-/
theorem submoduleOf_smul_self (A : Submodule R M) (a : R) :
    (a • A).submoduleOf A = (a • ⊤ : Submodule R A) := by
  ext x
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, y.2, rfl⟩

/- English proof (translation)
Rewrite using `[relLength_def, submoduleOf_smul_self]`.
-/
theorem relLength_smul_self_eq_length (A : Submodule R M) (a : R) :
    relLength A (a • A) = Module.length R (A ⧸ (a • ⊤ : Submodule R A)) := by
  rw [relLength_def, submoduleOf_smul_self]

end General

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
The claim follows from `Ring.ord_eq_addVal a`.
-/
theorem length_quotient_span_singleton_dvr (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a :=
  Ring.ord_eq_addVal a

/- English proof (translation)
Rewrite using `[addVal_pow, addVal_uniformizer hϖ, nsmul_one]`.
-/
theorem addVal_irreducible_pow {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) :
    addVal R (ϖ ^ e) = e := by
  rw [addVal_pow, addVal_uniformizer hϖ, nsmul_one]

section Free

variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/- English proof (translation)
Rewrite using `[length_quotient_smul_top_of_free, length_quotient_span_singleton_dvr]`.
-/
theorem length_quotient_smul_top_dvr (a : R) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) = addVal R a * (Module.finrank R M : ℕ∞) := by
  rw [length_quotient_smul_top_of_free, length_quotient_span_singleton_dvr]

end Free

variable {V : Type*} [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
  {A : Submodule R V}

/- English proof (translation)
Establish `: Module.Finite R A` using `Module.Finite.iff_fg.mpr hA`. Rewrite using `[relLength_smul_self_eq_length, length_quotient_smul_top_dvr]`.
-/
theorem relLength_smul_self (hA : A.FG) (a : R) :
    relLength A (a • A) = addVal R a * (Module.finrank R A : ℕ∞) := by
  have : Module.Finite R A := Module.Finite.iff_fg.mpr hA
  rw [relLength_smul_self_eq_length, length_quotient_smul_top_dvr]

/- English proof (translation)
Rewrite using `[relLength_smul_self hA, hn, Nat.cast_mul]`.
-/
theorem relLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    relLength A (a • A) = ((n * Module.finrank R A : ℕ) : ℕ∞) := by
  rw [relLength_smul_self hA, hn, Nat.cast_mul]

/- English proof (translation)
The claim follows from `relLength_smul_self_of_addVal_eq hA (addVal_irreducible_pow hϖ e)`.
-/
theorem relLength_irreducible_pow_smul_self (hA : A.FG) {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) :
    relLength A (ϖ ^ e • A) = ((e * Module.finrank R A : ℕ) : ℕ∞) :=
  relLength_smul_self_of_addVal_eq hA (addVal_irreducible_pow hϖ e)

/- English proof (translation)
Rewrite using `[relLength_smul_self hA]`. Conclude with `WithTop.mul_ne_top (addVal_eq_top_iff.not.mpr ha) (ENat.coe_ne_top _)`.
-/
theorem relLength_smul_self_ne_top (hA : A.FG) {a : R} (ha : a ≠ 0) :
    relLength A (a • A) ≠ ⊤ := by
  rw [relLength_smul_self hA]
  exact WithTop.mul_ne_top (addVal_eq_top_iff.not.mpr ha) (ENat.coe_ne_top _)

/- English proof (translation)
The claim follows from `(lengthCommensurable_iff_of_ge (Submodule.smul_le_self_of_tower a A)).mpr (relLength_smul_self_ne_top hA ha)`.
-/
theorem lengthCommensurable_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    LengthCommensurable A (a • A) :=
  (lengthCommensurable_iff_of_ge (Submodule.smul_le_self_of_tower a A)).mpr
    (relLength_smul_self_ne_top hA ha)

/- English proof (translation)
Establish `ha : a ≠ 0` using `addVal_eq_top_iff.not.mp (hn ▸ ENat.coe_ne_top n)`. Rewrite using `[← Nat.cast_mul, (lengthCommensurable_smul_self hA ha).signedLength_eq_natCast_iff_of_ge (Submodule.smul_le_self_of_tower a A), relLength_smul_self_of_addVal_eq hA hn]`.
-/
theorem signedLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    signedLength A (a • A) = (n : ℤ) * (Module.finrank R A : ℤ) := by
  have ha : a ≠ 0 := addVal_eq_top_iff.not.mp (hn ▸ ENat.coe_ne_top n)
  rw [← Nat.cast_mul, (lengthCommensurable_smul_self hA ha).signedLength_eq_natCast_iff_of_ge
    (Submodule.smul_le_self_of_tower a A), relLength_smul_self_of_addVal_eq hA hn]

/- English proof (translation)
The claim follows from `signedLength_smul_self_of_addVal_eq hA (ENat.coe_toNat (addVal_eq_top_iff.not.mpr ha)).symm`.
-/
theorem signedLength_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    signedLength A (a • A) = ((addVal R a).toNat : ℤ) * (Module.finrank R A : ℤ) :=
  signedLength_smul_self_of_addVal_eq hA (ENat.coe_toNat (addVal_eq_top_iff.not.mpr ha)).symm

end DVR

/- English proof (translation)
Rewrite using `[relLength_irreducible_pow_smul_self Module.Finite.fg_top PadicInt.irreducible_p]`. Simplify using the standard rewrite rules.
-/
example (p : ℕ) [Fact p.Prime] :
    relLength (⊤ : Submodule ℤ_[p] (Fin 2 → ℤ_[p])) ((p : ℤ_[p]) ^ 3 • ⊤) = 6 := by
  rw [relLength_irreducible_pow_smul_self Module.Finite.fg_top PadicInt.irreducible_p]
  simp

end GlobalTheory
