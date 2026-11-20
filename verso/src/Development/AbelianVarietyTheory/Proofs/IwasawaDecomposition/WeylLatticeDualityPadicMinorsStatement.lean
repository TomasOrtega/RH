import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualityPadicMinors
import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWeylLatticeDualityPadicMinors.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.weyl_lattice_duality_padic_minors : WeylLatticeDuality.Stmt := by
  first | exact @GlobalTheory.WeylLatDualPf.stmt_holds | exact GlobalTheory.WeylLatDualPf.stmt_holds | (intros; apply GlobalTheory.WeylLatDualPf.stmt_holds <;> assumption)
