import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProof
import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeylLatDualProof.mainProof` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMainProof.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.weyl_lattice_duality : WeylLatticeDuality.Stmt := by
  first | exact @GlobalTheory.WeylLatDualProof.mainProof | exact GlobalTheory.WeylLatDualProof.mainProof | (intros; apply GlobalTheory.WeylLatDualProof.mainProof <;> assumption)
