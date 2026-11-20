import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegralEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.archimedean_integral_eq : GlobalTheory.CompanionTheory.MixZ.ArchIntegrableOn → GlobalTheory.CompanionTheory.MixZ.ArchIntEq := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable | exact GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable | (intros; apply GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable <;> assumption)
