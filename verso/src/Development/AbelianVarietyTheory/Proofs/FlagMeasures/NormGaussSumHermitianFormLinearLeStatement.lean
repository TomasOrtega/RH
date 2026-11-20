import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumHermitianFormLinearLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNormGaussSumHermitianFormLinearLe.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (n : ℕ) (a : B), IsUnit (a + c a) → ∀ (v : Fin n → B), ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.norm_gauss_sum_ip_le | exact GlobalTheory.GramCount.norm_gauss_sum_ip_le | (intros; apply GlobalTheory.GramCount.norm_gauss_sum_ip_le <;> assumption)
