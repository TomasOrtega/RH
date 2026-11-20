import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroField
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsotropicGraphDetLowerRowNeZeroField.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_isotropic_graph_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧ (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  first | exact @GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | exact GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | (intros; apply GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field <;> assumption)
