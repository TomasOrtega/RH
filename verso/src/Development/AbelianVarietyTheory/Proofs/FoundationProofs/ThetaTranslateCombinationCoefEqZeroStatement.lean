import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateCombinationCoefEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FThetaTranslateCombinationCoefEqZero.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.thetaTranslate_combination_coef_eq_zero : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), Nice D T A → ∀ e ∈ ThSp D T A, e ≠ 0 → ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (z : ι → VC D N N'), (∀ v, ∑ i, a i * Wd D T (z i) e v = 0) → ∑ i, (if z i ∈ A then a i else 0) = 0 := by
  first | exact @GlobalTheory.ThetaTranslateCoef.coef_eq_zero | exact GlobalTheory.ThetaTranslateCoef.coef_eq_zero | (intros; apply GlobalTheory.ThetaTranslateCoef.coef_eq_zero <;> assumption)
