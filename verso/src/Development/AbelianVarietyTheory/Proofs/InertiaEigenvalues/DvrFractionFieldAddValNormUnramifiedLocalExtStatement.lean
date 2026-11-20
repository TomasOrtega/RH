import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFractionFieldAddValNormUnramifiedLocalExt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Unr.NormValU.val_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDvrFractionFieldAddValNormUnramifiedLocalExt.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormValU.val_norm | exact GlobalTheory.UnitLemma.Unr.NormValU.val_norm | (intros; apply GlobalTheory.UnitLemma.Unr.NormValU.val_norm <;> assumption)
