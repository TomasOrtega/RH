import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.MixZ.existsRead | exact GlobalTheory.CompanionTheory.MixZ.existsRead | (intros; apply GlobalTheory.CompanionTheory.MixZ.existsRead <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.mixed_cycle_read_exists : GlobalTheory.CompanionTheory.MixZ.ExistsRead := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.existsRead | exact GlobalTheory.CompanionTheory.MixZ.existsRead | (intros; apply GlobalTheory.CompanionTheory.MixZ.existsRead <;> assumption)
