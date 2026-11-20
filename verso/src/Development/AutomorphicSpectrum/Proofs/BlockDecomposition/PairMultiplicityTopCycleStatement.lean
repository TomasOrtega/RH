import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycle
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
open GlobalTheory.CompanionTheory.PairMult
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | exact GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | (intros; apply GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.pair_multiplicity_top_cycle : GlobalTheory.CompanionTheory.PairMult.TopCyc := by
  first | exact @GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | exact GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | (intros; apply GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc <;> assumption)
