import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution
import Mathlib
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsBasisAdaptedToCartanInvolution.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.exists_basis_adapted_to_cartan_involution' : ∀ (n : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ), s * s = 1 → sᴴ * G * s = G → (G * s).PosDef → ∃ (p q : ℕ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 ∧ B' * B = 1 ∧ Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) ∧ s * B = B * Matrix.fromBlocks 1 0 0 (-1) := by
  first | exact @GlobalTheory.exists_basis_adapted_to_cartan_involution | exact GlobalTheory.exists_basis_adapted_to_cartan_involution | (intros; apply GlobalTheory.exists_basis_adapted_to_cartan_involution <;> assumption)
