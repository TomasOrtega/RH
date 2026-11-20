import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormModuloUnipotentSemidirect
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm | exact GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm | (intros; apply GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNorma …`.
-/
theorem _root_.GlobalTheory.T.latticeNormalForm_modulo_unipotentSemidirect : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm := by
  first | exact @GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm | exact GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm | (intros; apply GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm <;> assumption)
