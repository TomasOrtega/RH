import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.ThTot.zeroTotal | exact GlobalTheory.CompanionTheory.ThTot.zeroTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.zeroTotal <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.zero_coefficient_total : ZeroTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.zeroTotal | exact GlobalTheory.CompanionTheory.ThTot.zeroTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.zeroTotal <;> assumption)
