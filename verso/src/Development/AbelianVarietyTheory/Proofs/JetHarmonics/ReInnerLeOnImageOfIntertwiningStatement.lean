import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ReInnerLeOnImageOfIntertwining
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FReInnerLeOnImageOfIntertwining.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.re_inner_le_on_image_of_intertwining' : ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T] [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T) (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) → (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) → ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  first | exact @GlobalTheory.re_inner_le_on_image_of_intertwining | exact GlobalTheory.re_inner_le_on_image_of_intertwining | (intros; apply GlobalTheory.re_inner_le_on_image_of_intertwining <;> assumption)
