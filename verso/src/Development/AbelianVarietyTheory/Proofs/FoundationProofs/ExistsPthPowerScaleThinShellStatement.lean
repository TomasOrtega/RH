import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShell
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlmostEt.klc_scale` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsPthPowerScaleThinShell.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_pth_power_scale_thin_shell : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ r : ℝ≥0, r < 1 → ∀ x : L, x ≠ 0 → ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 := by
  first | exact @GlobalTheory.AlmostEt.klc_scale | exact GlobalTheory.AlmostEt.klc_scale | (intros; apply GlobalTheory.AlmostEt.klc_scale <;> assumption)
