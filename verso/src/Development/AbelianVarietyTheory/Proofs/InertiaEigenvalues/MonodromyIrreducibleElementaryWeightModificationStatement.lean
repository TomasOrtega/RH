import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModification
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMonodromyIrreducibleElementaryWeightModification.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.monodromy_irreducible_elementary_weightModification : ModStep := by
  first | exact @GlobalTheory.PMon.modStep_holds | exact GlobalTheory.PMon.modStep_holds | (intros; apply GlobalTheory.PMon.modStep_holds <;> assumption)
