import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Glue.ev_cong_iff_and_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEvalSeriesCongIffCoeffAndIsUnit.lean&line=125#L125)
-/
theorem _root_.GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (k : ℕ) (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' → ((Cong p k x 0 ↔ ∀ r, Cong p k (c r) 0) ∧ ((∃ r, c r ≠ 0 ∧ IsInt p (c r)⁻¹) → x ≠ 0 ∧ IsInt p x⁻¹)) := by
  first | exact @GlobalTheory.Glue.ev_cong_iff_and_unit | exact GlobalTheory.Glue.ev_cong_iff_and_unit | (intros; apply GlobalTheory.Glue.ev_cong_iff_and_unit <;> assumption)
