import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.mixed_cycle_point_dictionary : GlobalTheory.CompanionTheory.MixZ.PtDict := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ptDict | exact GlobalTheory.CompanionTheory.MixZ.ptDict | (intros; apply GlobalTheory.CompanionTheory.MixZ.ptDict <;> assumption)
