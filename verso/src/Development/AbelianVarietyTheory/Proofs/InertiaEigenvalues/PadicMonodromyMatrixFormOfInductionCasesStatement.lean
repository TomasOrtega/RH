import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCases
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPadicMonodromyMatrixFormOfInductionCases.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  first | exact @GlobalTheory.PMon.matThm_of_steps | exact GlobalTheory.PMon.matThm_of_steps | (intros; apply GlobalTheory.PMon.matThm_of_steps <;> assumption)
