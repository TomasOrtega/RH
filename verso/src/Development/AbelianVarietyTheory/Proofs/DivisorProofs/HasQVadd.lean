import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

/- English proof (translation)
Introduce `N f a b h τ`. Establish `h1` using `h (b +ᵥ τ)`. Establish `he : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) = fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((b +ᵥ τ : ℍ) : ℂ) / N)`. Use function extensionality and compare the values at `n`. Rewrite using `[UpperHalfPlane.coe_vadd, mul_assoc (a n), ← Complex.exp_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Use `show HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f (b +ᵥ τ))`. Rewrite using `[he]`. Conclude with `h1`.
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
