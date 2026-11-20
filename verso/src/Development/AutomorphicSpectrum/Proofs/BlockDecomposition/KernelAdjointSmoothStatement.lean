import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.KerFc.adjSmooth | exact GlobalTheory.CompanionTheory.KerFc.adjSmooth | (intros; apply GlobalTheory.CompanionTheory.KerFc.adjSmooth <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.kernel_adjoint_smooth : GlobalTheory.CompanionTheory.KerFc.AdjSmooth := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.adjSmooth | exact GlobalTheory.CompanionTheory.KerFc.adjSmooth | (intros; apply GlobalTheory.CompanionTheory.KerFc.adjSmooth <;> assumption)
