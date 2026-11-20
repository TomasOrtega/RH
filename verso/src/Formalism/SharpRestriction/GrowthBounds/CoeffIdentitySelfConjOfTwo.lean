import Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjOfFourOpen
import Formalism.SharpRestriction.GrowthBounds.PsOfIntS
import Formalism.SharpRestriction.GrowthBounds.RescaleInV

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
Introduce `C _ _ V d I _ κ _ X _ hBi ζ hζ n hn γ δ c hγ hδ hc hN` and use `SelfConjGauge.hInt_core V X hBi ζ hζ n hn γ δ c hγ hδ hc hN`.
-/
theorem r1sHInt_holds : IntegralUnitFamilies :=
  fun C _ _ V d I _ κ _ X _ hBi ζ hζ n hn γ δ c hγ hδ hc hN => SelfConjGauge.hInt_core V X hBi ζ hζ n hn γ δ c hγ hδ hc hN

/- English proof (translation)
The claim follows from `r1sHResc`.
-/
theorem r1sHResc_holds : GaugeRescalingSymmetry := r1sHResc

/- English proof (translation)
The claim follows from `coeffIdentity_selfConj_of_four_open hHL r1sHResc_holds r1sHInt_holds hGe`.
-/
theorem coeffIdentity_selfConj_of_two (hHL : GaugeLeadingTermLinear) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four_open hHL r1sHResc_holds r1sHInt_holds hGe

end Formalism.L2.FormalSeriesBounds
