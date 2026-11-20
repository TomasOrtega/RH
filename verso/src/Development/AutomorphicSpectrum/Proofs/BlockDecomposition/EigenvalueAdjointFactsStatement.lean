import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.eigenvalue_adjoint_facts : GlobalTheory.CompanionTheory.KerFc.EvAdj := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.evAdj | exact GlobalTheory.CompanionTheory.KerFc.evAdj | (intros; apply GlobalTheory.CompanionTheory.KerFc.evAdj <;> assumption)
