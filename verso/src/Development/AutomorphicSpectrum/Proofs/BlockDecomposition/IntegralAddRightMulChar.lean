import Mathlib

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.PsiShift

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
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
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem vecMul_unipotent {R : Type*} [CommRing R] (h y x : R) :
    ![h, h * y] ᵥ* !![1, x; 0, 1] = ![h, h * (y + x)] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

end GlobalTheory.CompanionTheory.PsiShift
