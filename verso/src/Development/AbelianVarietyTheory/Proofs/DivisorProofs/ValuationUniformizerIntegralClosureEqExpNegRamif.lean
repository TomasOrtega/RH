import Mathlib
open IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Set `v : HeightOneSpectrum R` to `IsDiscreteValuationRing.maximalIdeal R`. Establish `hinj : Function.Injective (algebraMap R (integralClosure R L))`. Establish `h : Function.Injective (algebraMap R L)`. Rewrite using `[IsScalarTower.algebraMap_eq R K L]`. Conclude with `(algebraMap K L).injective.comp (IsFractionRing.injective R K)`.

Rewrite `h` using `[IsScalarTower.algebraMap_eq R (integralClosure R L) L]`. Rewrite `h` using `[RingHom.coe_comp]`. Conclude with `Function.Injective.of_comp h`. Establish `: FaithfulSMul R (integralClosure R L)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `: Module.IsTorsionFree R (integralClosure R L)` using `inferInstance`.

Establish `hlo : P.asIdeal.LiesOver v.asIdeal`. Prove the components needed by the constructor for the conclusion. Establish `hP` using `P.isPrime`. Establish `hne : P.asIdeal.under R ≠ ⊥` using `Ideal.under_ne_bot R P.ne_bot`. Conclude with `((IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne))).symm`.

Establish `h1` using `HeightOneSpectrum.valuation_liesOver L v P (algebraMap R K π)`. Rewrite using `[← h1, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton v hπ.ne_zero hπ.maximalIdeal_eq, ← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem valuation_uniformizer_integralClosure (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra R L] [IsScalarTower R K L] [IsDedekindDomain (integralClosure R L)]
    [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L))
    (π : R) (hπ : Irreducible π) :
    P.valuation L (algebraMap K L (algebraMap R K π)) = WithZero.exp (-(P.asIdeal.ramificationIdx R : ℤ)) := by
  let v : HeightOneSpectrum R := IsDiscreteValuationRing.maximalIdeal R
  have hinj : Function.Injective (algebraMap R (integralClosure R L)) := by
    have h : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    rw [IsScalarTower.algebraMap_eq R (integralClosure R L) L] at h
    rw [RingHom.coe_comp] at h
    exact Function.Injective.of_comp h
  have : FaithfulSMul R (integralClosure R L) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.IsTorsionFree R (integralClosure R L) := inferInstance
  have hlo : P.asIdeal.LiesOver v.asIdeal := by
    constructor
    have hP := P.isPrime
    have hne : P.asIdeal.under R ≠ ⊥ := Ideal.under_ne_bot R P.ne_bot
    exact ((IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne))).symm
  have h1 := HeightOneSpectrum.valuation_liesOver L v P (algebraMap R K π)
  rw [← h1, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton v hπ.ne_zero hπ.maximalIdeal_eq, ← WithZero.exp_nsmul]
  congr 1
  simp

end GlobalTheory
