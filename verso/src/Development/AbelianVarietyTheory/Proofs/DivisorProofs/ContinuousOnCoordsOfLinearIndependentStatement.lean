import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCoordsOfLinearIndependent
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousOnCoordsOfLinearIndependent.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.continuousOn_coords_of_linearIndependent' : ∀ (g m : ℕ) (U : Set ℂ) (μ : ℂ → Fin m → Fin g → ℂ) (v : ℂ → Fin g → ℂ) (c : ℂ → Fin m → ℝ), ContinuousOn μ U → ContinuousOn v U → (∀ s ∈ U, LinearIndependent ℝ (μ s)) → (∀ s ∈ U, v s = ∑ i, c s i • μ s i) → ContinuousOn c U := by
  first | exact @GlobalTheory.continuousOn_coords_of_linearIndependent | exact GlobalTheory.continuousOn_coords_of_linearIndependent | (intros; apply GlobalTheory.continuousOn_coords_of_linearIndependent <;> assumption)
