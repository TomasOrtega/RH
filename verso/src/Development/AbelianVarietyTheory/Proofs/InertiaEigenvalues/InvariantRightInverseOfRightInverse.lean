import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantRightInverseField

open Matrix

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse`. Consider the case `exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse`. Consider the case `(apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse ..)`.
-/
theorem invariant_right_inverse_of_right_inverse :
    ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type)
      [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L)
      (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) →
      ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first
  | exact @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | (apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse ..)

end GlobalTheory
