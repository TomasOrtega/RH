import Mathlib

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.PsiShift

/- English proof (translation)
Establish `h` using `integral_add_right_eq_self (μ := μ) (fun y => f y * (ψ (-(y - x)) : ℂ)) x`. Establish `h1 : ∀ y, f (y + x) * (ψ (-(y + x - x)) : ℂ) = f (y + x) * (ψ (-y) : ℂ)` using `fun y => by`. Simplify using the standard rewrite rules. Establish `h2 : ∀ y, f y * (ψ (-(y - x)) : ℂ) = (ψ x : ℂ) * (f y * (ψ (-y) : ℂ))` using `fun y => by`. Establish `: -(y - x) = x + -y` using `by abel`.

Rewrite using `[this, AddChar.map_add_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1, h2] at h`. Rewrite using `[h, integral_const_mul]`.
-/
theorem integral_add_right_mul_char {K : Type*} [AddCommGroup K] [MeasurableSpace K]
    [MeasurableAdd K] (μ : Measure K) [μ.IsAddRightInvariant] (ψ : AddChar K Circle)
    (f : K → ℂ) (x : K) :
    ∫ y, f (y + x) * (ψ (-y) : ℂ) ∂μ = (ψ x : ℂ) * ∫ y, f y * (ψ (-y) : ℂ) ∂μ := by
  have h := integral_add_right_eq_self (μ := μ) (fun y => f y * (ψ (-(y - x)) : ℂ)) x
  have h1 : ∀ y, f (y + x) * (ψ (-(y + x - x)) : ℂ) = f (y + x) * (ψ (-y) : ℂ) := fun y => by
    simp
  have h2 : ∀ y, f y * (ψ (-(y - x)) : ℂ) = (ψ x : ℂ) * (f y * (ψ (-y) : ℂ)) := fun y => by
    have : -(y - x) = x + -y := by abel
    rw [this, AddChar.map_add_eq_mul]
    push_cast
    ring
  simp only [h1, h2] at h
  rw [h, integral_const_mul]

/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring`.
-/
theorem vecMul_unipotent {R : Type*} [CommRing R] (h y x : R) :
    ![h, h * y] ᵥ* !![1, x; 0, 1] = ![h, h * (y + x)] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

end GlobalTheory.CompanionTheory.PsiShift
