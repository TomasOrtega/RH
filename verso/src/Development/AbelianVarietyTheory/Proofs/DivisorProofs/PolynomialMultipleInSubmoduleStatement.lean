import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialMultipleInSubmodule
import Mathlib
open SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolynomialMultipleInSubmodule.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.polynomial_multiple_in_submodule : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (N : Submodule ℂ (SchwartzMap V ℂ)) (g : SchwartzMap V ℂ), g ∈ N →
    (∀ f ∈ N, ∀ ℓ : V →ₗ[ℝ] ℝ, ∃ f₁ ∈ N, ∀ x, f₁ x = (ℓ x : ℂ) * f x) →
    ∀ (j : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => V) ℂ),
      ∃ f ∈ N, ∀ x, f x = M (fun _ => x) * g x := by
  first | exact @GlobalTheory.schwartz_submodule_multilinear_mem | exact GlobalTheory.schwartz_submodule_multilinear_mem | (intros; apply GlobalTheory.schwartz_submodule_multilinear_mem <;> assumption)
