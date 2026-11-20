import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HullGeneration
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.EGlue.hullGen | exact GlobalTheory.CompanionTheory.EGlue.hullGen | (intros; apply GlobalTheory.CompanionTheory.EGlue.hullGen <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.hull_generation : GlobalTheory.CompanionTheory.EGlue.HullGen := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.hullGen | exact GlobalTheory.CompanionTheory.EGlue.hullGen | (intros; apply GlobalTheory.CompanionTheory.EGlue.hullGen <;> assumption)
