import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

namespace GlobalTheory

/- English proof (translation)
Take `⟨c, hc, h⟩` from `FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) hN`. Conclude with `⟨c, nonZeroDivisors.ne_zero hc, fun y hy => h y hy⟩`.
-/
theorem exists_common_denominator_of_fg {R L : Type*} [CommRing R] [IsDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (N : Submodule R L) (hN : N.FG) :
    ∃ c : R, c ≠ 0 ∧ ∀ y ∈ N, ∃ s : R, algebraMap R L s = c • y := by
  obtain ⟨c, hc, h⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) hN
  exact ⟨c, nonZeroDivisors.ne_zero hc, fun y hy => h y hy⟩

/- English proof (translation)
Set `L` to `FractionRing R`. Set `M` to `FractionRing B`. Use `haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Use `haveI hfin : Module.Finite R (integralClosure R L) := finite_integralClosure_dedekind K R L L`. Establish `hfg : (Subalgebra.toSubmodule (integralClosure R L)).FG` using `Module.Finite.iff_fg.mp hfin`.

Take `⟨c, hc, h⟩` from `exists_common_denominator_of_fg _ hfg`. Use `⟨c, hc, fun x hx ⟨r, s, hr, hrs⟩ => ?_⟩` and prove the remaining obligations. Use `letI : Algebra L M := FractionRing.liftAlgebra R M`. Set `φ : L →ₐ[R] M` to `IsScalarTower.toAlgHom R L M`. Establish `hφ : Function.Injective φ` using `φ.toRingHom.injective`.

Establish `hB : Function.Injective (algebraMap B M)` using `IsFractionRing.injective B M`. Establish `hrM : algebraMap R M r ≠ 0`. Rewrite using `[IsScalarTower.algebraMap_apply R B M]`. Conclude with `(map_ne_zero_iff _ hB).mpr ((map_ne_zero_iff _ hinj).mpr hr)`. Establish `hy : φ (algebraMap R L s / algebraMap R L r) = algebraMap B M x`.

Rewrite using `[map_div₀, AlgHom.commutes, AlgHom.commutes, div_eq_iff hrM, IsScalarTower.algebraMap_apply R B M, IsScalarTower.algebraMap_apply R B M, ← hrs, map_mul, mul_comm]`. Establish `hint : IsIntegral R (algebraMap R L s / algebraMap R L r)`. Rewrite using `[← isIntegral_algHom_iff φ hφ, hy]`. Conclude with `hx.map (IsScalarTower.toAlgHom R B M)`. Take `⟨t, ht⟩` from `h _ hint`.

Use `⟨t, hB ?_⟩` and prove the remaining obligations. Use `congrArg φ ht` as an intermediate fact. Rewrite `this` using `[map_smul, hy, AlgHom.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R B M, IsScalarTower.algebraMap_apply R B M]`. Rewrite using `[map_mul, this]`.
-/
theorem exists_ne_zero_mul_mem_of_isIntegral_of_fraction (K R B : Type) [Field K] [CharZero K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [CommRing B] [IsDomain B]
    [Algebra R B] (hinj : Function.Injective (algebraMap R B)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x : B, IsIntegral R x →
      (∃ r s : R, r ≠ 0 ∧ algebraMap R B r * x = algebraMap R B s) →
      ∃ s : R, algebraMap R B c * x = algebraMap R B s := by
  let L := FractionRing R
  let M := FractionRing B
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI hfin : Module.Finite R (integralClosure R L) := finite_integralClosure_dedekind K R L L
  have hfg : (Subalgebra.toSubmodule (integralClosure R L)).FG :=
    Module.Finite.iff_fg.mp hfin
  obtain ⟨c, hc, h⟩ := exists_common_denominator_of_fg _ hfg
  refine ⟨c, hc, fun x hx ⟨r, s, hr, hrs⟩ => ?_⟩
  letI : Algebra L M := FractionRing.liftAlgebra R M
  let φ : L →ₐ[R] M := IsScalarTower.toAlgHom R L M
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hB : Function.Injective (algebraMap B M) := IsFractionRing.injective B M
  have hrM : algebraMap R M r ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R B M]
    exact (map_ne_zero_iff _ hB).mpr ((map_ne_zero_iff _ hinj).mpr hr)
  have hy : φ (algebraMap R L s / algebraMap R L r) = algebraMap B M x := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes, div_eq_iff hrM,
      IsScalarTower.algebraMap_apply R B M, IsScalarTower.algebraMap_apply R B M, ← hrs, map_mul,
      mul_comm]
  have hint : IsIntegral R (algebraMap R L s / algebraMap R L r) := by
    rw [← isIntegral_algHom_iff φ hφ, hy]
    exact hx.map (IsScalarTower.toAlgHom R B M)
  obtain ⟨t, ht⟩ := h _ hint
  refine ⟨t, hB ?_⟩
  have := congrArg φ ht
  rw [map_smul, hy, AlgHom.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R B M,
    IsScalarTower.algebraMap_apply R B M] at this
  rw [map_mul, this]

end GlobalTheory
