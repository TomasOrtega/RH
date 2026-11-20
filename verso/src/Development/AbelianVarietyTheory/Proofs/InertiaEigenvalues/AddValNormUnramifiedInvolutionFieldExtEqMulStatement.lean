import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValNormUnramifiedInvolutionFieldExtEqMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAddValNormUnramifiedInvolutionFieldExtEqMul.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = d * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormVal.normval | exact GlobalTheory.UnitLemma.Unr.NormVal.normval | (intros; apply GlobalTheory.UnitLemma.Unr.NormVal.normval <;> assumption)
