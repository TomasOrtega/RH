import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothDifferencePeriodDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothDifferencePeriodDecomposition.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.smooth_difference_period_decomposition : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} [FiniteDimensional ℂ E] {B : Set E}, IsOpen B → ∀ {ψ : E → Fin g → ℂ}, ContDiffOn ℝ ∞ ψ B → ∀ {b : E}, b ∈ B → ∀ {m : ℕ} {f : (Fin g → ℂ) → Ext m}, ContDiff ℝ ∞ f → ∃ (φ : Fin g ⊕ Fin g → E → ℂ) (σ : Fin g ⊕ Fin g → Pt E g → Ext m), (∀ k, ContDiffOn ℝ ∞ (φ k) B ∧ φ k b = 0 ∧ ContDiffOn ℝ ∞ (σ k) (cov B g)) ∧ ∀ P ∈ cov B g, f (P.2 + ψ P.1) - f (P.2 + ψ b) = ∑ k, φ k P.1 • σ k P := by
  first | exact @GlobalTheory.TorsionForm.Hadamard.hadamard | exact GlobalTheory.TorsionForm.Hadamard.hadamard | (intros; apply GlobalTheory.TorsionForm.Hadamard.hadamard <;> assumption)
