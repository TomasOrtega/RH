import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDeRhamExtensionPotentiallySemistable.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.deRhamExtension_potentiallySemistable : ExtStep := by
  first | exact @GlobalTheory.PMon.extStep_holds | exact GlobalTheory.PMon.extStep_holds | (intros; apply GlobalTheory.PMon.extStep_holds <;> assumption)
