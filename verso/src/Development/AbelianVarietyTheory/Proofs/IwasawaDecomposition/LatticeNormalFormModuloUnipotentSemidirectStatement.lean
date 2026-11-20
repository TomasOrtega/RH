import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormModuloUnipotentSemidirect
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLatticeNormalFormModuloUnipotentSemidirect.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.latticeNormalForm_modulo_unipotentSemidirect : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm := by
  first | exact @GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm | exact GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm | (intros; apply GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm <;> assumption)
