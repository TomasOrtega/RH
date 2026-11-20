import Mathlib
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `R _ _ _ _ _ h1`. Establish `hnf : ¬ IsField R` using `(ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp h1).1`. Establish `hdim : Ring.KrullDimLE 1 R` using `Ring.krullDimLE_iff.mpr (by simp [h1])`. Establish `h4 : IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime`. Use `⟨inferInstance, IsLocalRing.maximalIdeal R, ⟨fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h), inferInstance⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `P ⟨hP, hPp⟩`. Conclude with `IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim P hP hPp)`. Conclude with `((IsDiscreteValuationRing.TFAE R hnf).out 0 3).mpr h4`.
-/
theorem normal_noeth_local_dim_one_isDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ringKrullDim R = 1 → IsDiscreteValuationRing R := by
  intro R _ _ _ _ _ h1
  have hnf : ¬ IsField R := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp h1).1
  have hdim : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [h1])
  have h4 : IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨inferInstance, IsLocalRing.maximalIdeal R,
      ⟨fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h), inferInstance⟩, ?_⟩
    rintro P ⟨hP, hPp⟩
    exact IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim P hP hPp)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 0 3).mpr h4

end GlobalTheory.CompanionTheory.Ar.Flat
