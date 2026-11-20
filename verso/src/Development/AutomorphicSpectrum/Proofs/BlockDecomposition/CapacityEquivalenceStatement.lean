import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalence
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.EGlue.capEquiv | exact GlobalTheory.CompanionTheory.EGlue.capEquiv | (intros; apply GlobalTheory.CompanionTheory.EGlue.capEquiv <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.capacity_equivalence : GlobalTheory.CompanionTheory.EGlue.CapEquiv := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.capEquiv | exact GlobalTheory.CompanionTheory.EGlue.capEquiv | (intros; apply GlobalTheory.CompanionTheory.EGlue.capEquiv <;> assumption)
