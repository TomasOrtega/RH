import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionContDiffOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSuperconnectionContDiffOn.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.superconnection_contDiffOn : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ContDiffOn ℝ ∞ s (cov B g) → ContDiffOn ℝ ∞ (superconn τ h β u s) (cov B g) := by
  first | exact @GlobalTheory.TorsionForm.SuperconnSmooth.superconn_contDiffOn | exact GlobalTheory.TorsionForm.SuperconnSmooth.superconn_contDiffOn | (intros; apply GlobalTheory.TorsionForm.SuperconnSmooth.superconn_contDiffOn <;> assumption)
