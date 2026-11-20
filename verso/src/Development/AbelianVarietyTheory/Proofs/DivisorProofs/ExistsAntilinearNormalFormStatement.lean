import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAntilinearNormalForm
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAntilinearNormalForm.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_antilinear_normal_form : ∀ (g : ℕ) (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j))) →
    ∀ (α β : Fin g → ℂ), (∀ j, ‖β j‖ < ‖α j‖) →
    (∀ j (y : ℂ), T (Pi.single j y) j = α j * y + β j * starRingEnd ℂ y) →
    ∃ D : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, D (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j)) ∧
      ∀ (c : Fin g → ℝ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T (fun m ↦ (c m : ℂ) * v m) = M (T v)) →
        ∀ w, D (M w) = fun j ↦ (c j : ℂ) * D w j := by
  first | exact @GlobalTheory.coordsDiag | exact GlobalTheory.coordsDiag | (intros; apply GlobalTheory.coordsDiag <;> assumption)
