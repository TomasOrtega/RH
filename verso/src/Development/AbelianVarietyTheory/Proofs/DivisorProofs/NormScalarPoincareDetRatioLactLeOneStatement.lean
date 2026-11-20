import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormScalarPoincareDetRatioLactLeOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ScalarPoin.norm_qS_lact_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormScalarPoincareDetRatioLactLeOne.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, ‖qS X x0 1 (lact γ x0)‖ ≤ 1 ∧ (‖qS X x0 1 (lact γ x0)‖ = 1 → ∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) := by
  first | exact @GlobalTheory.ScalarPoin.norm_qS_lact_le | exact GlobalTheory.ScalarPoin.norm_qS_lact_le | (intros; apply GlobalTheory.ScalarPoin.norm_qS_lact_le <;> assumption)
