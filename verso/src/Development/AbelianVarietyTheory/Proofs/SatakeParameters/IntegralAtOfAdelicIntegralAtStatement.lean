import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIntegralAtOfAdelicIntegralAt.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.integralAt_of_adelic_integralAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  first | exact @GlobalTheory.RatInt.intAt_of_intAtA | exact GlobalTheory.RatInt.intAt_of_intAtA | (intros; apply GlobalTheory.RatInt.intAt_of_intAtA <;> assumption)
