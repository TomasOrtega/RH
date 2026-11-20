import Formalism.SharpRestriction.GrowthBounds.SumRescaleTySTwo
import Formalism.SharpRestriction.GrowthBounds.ConstantCoeffUnshiftLogarithm
import Formalism.SharpRestriction.GrowthBounds.R1sExpLowHolds
import Formalism.LocalToGlobal.CharacterGerms.FrobPowSmul
import Formalism.LocalToGlobal.CharacterGerms.MmMulSeries

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
The claim follows from `frobPow_smul`.
-/
theorem r1sFrob_holds : PowerSeriesFrobeniusCongruence := frobPow_smul

/- English proof (translation)
Introduce `C _ V ζ hζ j f hf μ` and use `rootsProd C V ζ hζ j f hf μ`.
-/
theorem r1sRoots_holds : RootsOfUnityProductCongruence := fun C _ V ζ hζ j f hf μ => rootsProd C V ζ hζ j f hf μ

/- English proof (translation)
The claim follows from `coeffIdentity_selfConj_of_four good_curve_closed r1sRestB_holds (r1sRestC_of r1sFrob_holds r1sRoots_holds r1sExpLow_holds hHL hHR hHI hGe) biadditive_on_columns`.
-/
theorem coeffIdentity_selfConj_of_four_open (hHL : GaugeLeadingTermLinear) (hHR : GaugeRescalingSymmetry) (hHI : IntegralUnitFamilies) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four good_curve_closed r1sRestB_holds
    (r1sRestC_of r1sFrob_holds r1sRoots_holds r1sExpLow_holds hHL hHR hHI hGe) biadditive_on_columns

end Formalism.L2.FormalSeriesBounds
