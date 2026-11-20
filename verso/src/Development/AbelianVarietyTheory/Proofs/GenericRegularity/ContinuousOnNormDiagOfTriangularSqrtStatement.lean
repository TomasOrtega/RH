import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContinuousOnNormDiagOfTriangularSqrt
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGenericRegularity%2FContinuousOnNormDiagOfTriangularSqrt.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by
  first | exact @GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt | exact GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt | (intros; apply GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt <;> assumption)
