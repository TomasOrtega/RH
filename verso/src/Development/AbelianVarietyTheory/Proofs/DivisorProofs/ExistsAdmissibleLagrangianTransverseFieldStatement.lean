import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleLagrangianTransverseField
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.lagrangian_transverse_field` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAdmissibleLagrangianTransverseField.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.exists_admissible_lagrangian_transverse_field : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.lagrangian_transverse_field | exact GlobalTheory.lagrangian_transverse_field | (intros; apply GlobalTheory.lagrangian_transverse_field <;> assumption)
