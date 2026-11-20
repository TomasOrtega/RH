import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.finiteAlgebraAdelicLattice_proof : GlobalTheory.RegSS.TensorLattice := by
  first | exact @GlobalTheory.RegSSLattice.tensorLattice | exact GlobalTheory.RegSSLattice.tensorLattice | (intros; apply GlobalTheory.RegSSLattice.tensorLattice <;> assumption)
