import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasQ_vadd : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (b : ℝ), HasQ N f a →
    HasQ N (fun τ => f (b +ᵥ τ))
      (fun n => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N)) := by
  intro N f a b h τ
  have h1 := h (b +ᵥ τ)
  have he : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) =
      fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((b +ᵥ τ : ℍ) : ℂ) / N) := by
    funext n
    rw [UpperHalfPlane.coe_vadd, mul_assoc (a n), ← Complex.exp_add]
    congr 2
    ring
  show HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f (b +ᵥ τ))
  rw [he]
  exact h1

end GlobalTheory.QFam
