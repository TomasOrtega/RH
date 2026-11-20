import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInertiaImpliesPotSemistableProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteInertiaImpliesPotSemistableProof.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.finiteInertiaImpliesPotSemistable_proof : UnrStep := by
  first | exact @GlobalTheory.PMon.unrStep_holds | exact GlobalTheory.PMon.unrStep_holds | (intros; apply GlobalTheory.PMon.unrStep_holds <;> assumption)
