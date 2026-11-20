import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.matThm_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPAdicMonodromyTheoremMatrixForm.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.pAdicMonodromyTheorem_matrixForm : MatThm := by
  first | exact @GlobalTheory.PMon.matThm_holds | exact GlobalTheory.PMon.matThm_holds | (intros; apply GlobalTheory.PMon.matThm_holds <;> assumption)
