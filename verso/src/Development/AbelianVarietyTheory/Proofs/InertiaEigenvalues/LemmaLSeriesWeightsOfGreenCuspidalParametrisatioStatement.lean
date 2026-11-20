import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LemmaLSeriesWeightsOfGreenCuspidalParametrisatio
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLemmaLSeriesWeightsOfGreenCuspidalParametrisatio.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.admLq_of_green_of_eSerTie : Green → ∀ D : Formalism.BasicNotions.D7, ESerTie D → admLq D := by
  first | exact @GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation | exact GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation | (intros; apply GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation <;> assumption)
