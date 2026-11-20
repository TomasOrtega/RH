import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndKFinDecayOfGapOfDecAll

namespace GlobalTheory.DecTransport

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem decLow_main : Formalism.FourierDecayAlt.ThreeDimData.DecLow := decLow_holds

instance instFactDecLow : Fact (Formalism.FourierDecayAlt.ThreeDimData.DecLow) := ⟨decLow_main⟩

end GlobalTheory.DecTransport
