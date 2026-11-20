import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVanishingLocalProductDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge GlobalTheory.TorsionForm.Fibrewise
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothVanishingLocalProductDecomposition.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.smooth_vanishing_local_product_decomposition : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g m : ℕ} (B : Set E) (r : Pt E g → Ext m), IsOpen B → ContDiffOn ℝ ∞ r (cov B g) → ∀ b ∈ B, (∀ z, r (b, z) = 0) → ∀ z : Fin g → ℂ, ∃ (N : ℕ) (ψ : Fin N → E → ℂ) (q : Fin N → Pt E g → Ext m), (∀ k, ContDiff ℝ ∞ (ψ k)) ∧ (∀ k, ψ k b = 0) ∧ (∀ k, ContDiff ℝ ∞ (q k)) ∧ r =ᶠ[𝓝 (b, z)] fun Q => ∑ k, ψ k Q.1 • q k Q := by
  first | exact @GlobalTheory.FibreHadamard.fibre_hadamard | exact GlobalTheory.FibreHadamard.fibre_hadamard | (intros; apply GlobalTheory.FibreHadamard.fibre_hadamard <;> assumption)
