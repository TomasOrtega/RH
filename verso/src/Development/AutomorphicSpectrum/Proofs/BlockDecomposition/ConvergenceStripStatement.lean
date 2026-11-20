import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStrip
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | exact GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.convergence_strip : GlobalTheory.CompanionTheory.EGlue.ConvStrip := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | exact GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip <;> assumption)
