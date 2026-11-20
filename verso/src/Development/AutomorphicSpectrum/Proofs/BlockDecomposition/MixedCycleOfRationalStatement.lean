import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRational
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.mixed_cycle_of_rational : GlobalTheory.CompanionTheory.MixZ.CycleOfRat := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.CycleRat.cycleOfRat | exact GlobalTheory.CompanionTheory.MixZ.CycleRat.cycleOfRat | (intros; apply GlobalTheory.CompanionTheory.MixZ.CycleRat.cycleOfRat <;> assumption)
