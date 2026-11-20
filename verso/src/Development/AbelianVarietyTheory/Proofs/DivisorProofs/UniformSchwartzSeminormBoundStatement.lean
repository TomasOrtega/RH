import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBound
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUniformSchwartzSeminormBound.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.uniform_schwartz_seminorm_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (I : Type)
    (lam : I → SchwartzMap V ℂ →L[ℂ] ℂ) (w : I → ℝ), (∀ i, 0 ≤ w i) →
    (∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖lam i f‖ ≤ C * w i ^ N) →
    ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)), ∀ i f, ‖lam i f‖ ≤ C * (T.sup (schwartzSeminormFamily ℂ V ℂ)) f * w i ^ N := by
  first | exact @GlobalTheory.schwartz_family_uniform_bound | exact GlobalTheory.schwartz_family_uniform_bound | (intros; apply GlobalTheory.schwartz_family_uniform_bound <;> assumption)
