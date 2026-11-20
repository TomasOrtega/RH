import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDictionaryPartB
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Unram.unramifiedDictionary_part_b | exact GlobalTheory.CompanionTheory.Unram.unramifiedDictionary_part_b | (intros; apply GlobalTheory.CompanionTheory.Unram.unramifiedDictionary_part_b <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.integralBasisUnramified_of_d0a : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.IntegralBasisUnramified := by
  first | exact @GlobalTheory.CompanionTheory.Unram.unramifiedDictionary_part_b | exact GlobalTheory.CompanionTheory.Unram.unramifiedDictionary_part_b | (intros; apply GlobalTheory.CompanionTheory.Unram.unramifiedDictionary_part_b <;> assumption)
