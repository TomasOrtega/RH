import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantRightInverseOfRightInverse
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInvariantRightInverseOfRightInverse.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_invariant_right_inverse : ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) → ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first | exact @GlobalTheory.invariant_right_inverse_of_right_inverse | exact GlobalTheory.invariant_right_inverse_of_right_inverse | (intros; apply GlobalTheory.invariant_right_inverse_of_right_inverse <;> assumption)
