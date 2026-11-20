import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Dec.phiPos | exact GlobalTheory.Dec.phiPos | (intros; apply GlobalTheory.Dec.phiPos <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.phi_positive_definite_cholesky_formula : PhiPos := by
  first | exact @GlobalTheory.Dec.phiPos | exact GlobalTheory.Dec.phiPos | (intros; apply GlobalTheory.Dec.phiPos <;> assumption)
