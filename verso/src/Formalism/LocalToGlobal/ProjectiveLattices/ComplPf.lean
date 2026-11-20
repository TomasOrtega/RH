import Formalism.LocalToGlobal.ProjectiveLattices.ComplSt
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR

namespace Formalism.L2.Pj

open IsLocalRing

/- English proof (translation)
Introduce `W _ _ _ _`. Use `haveI : CharZero (AdicCompletion (maximalIdeal W) W) := charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Establish `hl : IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W))` using `inferInstance`. Conclude with `⟨⟨AdicCompletion (maximalIdeal W) W⟩, algebraMap W (AdicCompletion (maximalIdeal W) W), hl, ϖ, hϖ, GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr hϖ⟩`.
-/
theorem complSt_holds : ComplSt := by
  intro W _ _ _ _
  haveI : CharZero (AdicCompletion (maximalIdeal W) W) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hl : IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W)) := inferInstance
  exact ⟨⟨AdicCompletion (maximalIdeal W) W⟩, algebraMap W (AdicCompletion (maximalIdeal W) W), hl, ϖ, hϖ,
    GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr hϖ⟩

end Formalism.L2.Pj
