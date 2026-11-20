import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordsEqPairingsRationalSymplecticBasis
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCoordsEqPairingsRationalSymplecticBasis.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.coords_eq_pairings_rational_symplectic_basis : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε φ : Fin g → Fin r → ℚ), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) → (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∀ x : Fin r → ℚ, x = ∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j := by
  first | exact @GlobalTheory.coords_in_rational_symplectic_basis | exact GlobalTheory.coords_in_rational_symplectic_basis | (intros; apply GlobalTheory.coords_in_rational_symplectic_basis <;> assumption)
