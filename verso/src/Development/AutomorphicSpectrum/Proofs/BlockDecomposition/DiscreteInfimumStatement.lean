import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimum
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.discrete_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.discInf | exact GlobalTheory.CompanionTheory.EGlue.discInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.discInf <;> assumption)
