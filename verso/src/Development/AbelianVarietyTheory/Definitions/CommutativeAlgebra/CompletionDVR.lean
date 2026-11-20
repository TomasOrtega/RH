import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

namespace ReciprocityTheory.CA.Pt

open IsLocalRing

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨inferInstance, inferInstance⟩, inferInstance, GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W, inferInstance, AdicCompletion.maximalIdeal_eq_map⟩`.
-/
theorem completionDVR (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    (∃ _ : IsDomain (AdicCompletion (maximalIdeal W) W),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal W) W)) ∧
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal W) W)) (AdicCompletion (maximalIdeal W) W) ∧
    Function.Injective (algebraMap W (AdicCompletion (maximalIdeal W) W)) ∧
    IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W)) ∧
    maximalIdeal (AdicCompletion (maximalIdeal W) W) =
      (maximalIdeal W).map (algebraMap W (AdicCompletion (maximalIdeal W) W)) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W, inferInstance,
    AdicCompletion.maximalIdeal_eq_map⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(completionDVR ℤ_[2]).2.1, (completionDVR ℤ_[2]).2.2.1⟩`.
-/
example : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal ℤ_[2]) ℤ_[2]))
      (AdicCompletion (maximalIdeal ℤ_[2]) ℤ_[2]) ∧
    Function.Injective (algebraMap ℤ_[2] (AdicCompletion (maximalIdeal ℤ_[2]) ℤ_[2])) :=
  ⟨(completionDVR ℤ_[2]).2.1, (completionDVR ℤ_[2]).2.2.1⟩

/- English proof (translation)
Introduce `h` and use `PowerSeries.X_irreducible.not_isUnit ((completionDVR (PowerSeries ℚ)).2.2.2.1.map_nonunit _ h)`.
-/
example : ¬ IsUnit (algebraMap (PowerSeries ℚ)
    (AdicCompletion (maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ)) PowerSeries.X) := fun h =>
  PowerSeries.X_irreducible.not_isUnit ((completionDVR (PowerSeries ℚ)).2.2.2.1.map_nonunit _ h)

end ReciprocityTheory.CA.Pt
