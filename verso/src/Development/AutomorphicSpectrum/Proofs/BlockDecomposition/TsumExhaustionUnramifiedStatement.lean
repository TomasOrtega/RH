import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramified
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | exact GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | (intros; apply GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.tsum_exhaustion_unramified : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  first | exact @GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | exact GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | (intros; apply GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop <;> assumption)
