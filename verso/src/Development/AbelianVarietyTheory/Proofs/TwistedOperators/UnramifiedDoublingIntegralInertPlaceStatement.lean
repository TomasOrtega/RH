import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_inert_place : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert := by
  first | exact @GlobalTheory.InertZeta.unramDoublingInert | exact GlobalTheory.InertZeta.unramDoublingInert | (intros; apply GlobalTheory.InertZeta.unramDoublingInert <;> assumption)
