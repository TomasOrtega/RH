import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentFrobSolutionsCrisProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.exI_main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIndependentFrobSolutionsCrisProof.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.existsIndependentFrobSolutionsCris_proof : ExI := by
  first | exact @GlobalTheory.PMon.exI_main | exact GlobalTheory.PMon.exI_main | (intros; apply GlobalTheory.PMon.exI_main <;> assumption)
