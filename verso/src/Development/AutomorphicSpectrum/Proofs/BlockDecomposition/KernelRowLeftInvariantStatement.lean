import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.KerFc.rowLeft | exact GlobalTheory.CompanionTheory.KerFc.rowLeft | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowLeft <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.kernel_row_left_invariant : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.RowLeft := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowLeft | exact GlobalTheory.CompanionTheory.KerFc.rowLeft | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowLeft <;> assumption)
