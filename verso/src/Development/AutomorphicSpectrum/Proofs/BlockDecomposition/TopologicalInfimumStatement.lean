import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimum
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | exact GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.Gl0.topInf <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.topological_infimum : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | exact GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.Gl0.topInf <;> assumption)
