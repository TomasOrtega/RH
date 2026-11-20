import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityStatement
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.DivMult.div_multiplier | exact GlobalTheory.CompanionTheory.DivMult.div_multiplier | (intros; apply GlobalTheory.CompanionTheory.DivMult.div_multiplier <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.divisibility_statement : Div := by
  first | exact @GlobalTheory.CompanionTheory.DivMult.div_multiplier | exact GlobalTheory.CompanionTheory.DivMult.div_multiplier | (intros; apply GlobalTheory.CompanionTheory.DivMult.div_multiplier <;> assumption)
