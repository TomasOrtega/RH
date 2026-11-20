import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfPadicAlgClUniformApprox
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UniformCoboundary.coboundary_of_padic_approx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCoboundaryOfPadicAlgClUniformApprox.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.coboundary_of_padicAlgCl_uniform_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  first | exact @GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | exact GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | (intros; apply GlobalTheory.UniformCoboundary.coboundary_of_padic_approx <;> assumption)
