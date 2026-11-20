import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnSuperconn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContDiffOnSuperconn.lean&line=163#L163)
-/
theorem _root_.GlobalTheory.T.contDiffOn_superconn' : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ {h : Pt E g → ℝ}, ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ∀ (β : Fin n → E) (u : ℝ) {σ : Pt E g → Ext (n + n + g)}, ContDiffOn ℝ ∞ σ (cov B g) → ContDiffOn ℝ ∞ (superconn τ h β u σ) (cov B g) := by
  first | exact @GlobalTheory.SuperconnSmooth.main | exact GlobalTheory.SuperconnSmooth.main | (intros; apply GlobalTheory.SuperconnSmooth.main <;> assumption)
