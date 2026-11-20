import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStandardLatticeAlternatingFormBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryStd.form_bijective_of_unimodular` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryStandardLatticeAlternatingFormBijective.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.unitaryStandardLatticeAlternatingForm_bijective : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by
  first | exact @GlobalTheory.UnitaryStd.form_bijective_of_unimodular | exact GlobalTheory.UnitaryStd.form_bijective_of_unimodular | (intros; apply GlobalTheory.UnitaryStd.form_bijective_of_unimodular <;> assumption)
