import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlane
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.H3.uhp_root` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsHolomorphicRootUpperHalfPlane.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.exists_holomorphic_root_upperHalfPlane : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs → (∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) → ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Hs ∧ ∀ z ∈ Hs, r z ^ m = h z := by
  first | exact @GlobalTheory.KZ.H3.uhp_root | exact GlobalTheory.KZ.H3.uhp_root | (intros; apply GlobalTheory.KZ.H3.uhp_root <;> assumption)
