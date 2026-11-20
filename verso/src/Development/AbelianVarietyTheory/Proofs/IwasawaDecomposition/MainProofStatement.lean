import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProof
import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.WeylLatDualProof.mainProof | exact GlobalTheory.WeylLatDualProof.mainProof | (intros; apply GlobalTheory.WeylLatDualProof.mainProof <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.weyl_lattice_duality : WeylLatticeDuality.Stmt := by
  first | exact @GlobalTheory.WeylLatDualProof.mainProof | exact GlobalTheory.WeylLatDualProof.mainProof | (intros; apply GlobalTheory.WeylLatDualProof.mainProof <;> assumption)
