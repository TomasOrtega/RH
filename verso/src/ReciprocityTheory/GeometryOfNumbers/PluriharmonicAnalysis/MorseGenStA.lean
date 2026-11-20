import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix MeasureTheory Complex

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
theorem morseGen_ident (fz qz : ℂ) (φz φ0 νz ν0 : ℝ) (n : ℕ) :
    ‖fz * cexp (-(n : ℂ) * qz / 2)‖ ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re))) * (νz / ν0) =
      ‖fz‖ ^ 2 * Real.exp (-((n : ℝ) * φz)) * νz * (Real.exp ((n : ℝ) * φ0) / ν0) := by
  have hre : (-(n : ℂ) * qz / 2).re = -((n : ℝ) * qz.re) / 2 := by simp
  have e1 : Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re))) =
      Real.exp (-((n : ℝ) * φz)) * Real.exp ((n : ℝ) * φ0) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, Complex.norm_exp, hre, mul_pow]
  calc ‖fz‖ ^ 2 * Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re)))
        * (νz / ν0)
      = ‖fz‖ ^ 2 * (Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 *
          Real.exp (-((n : ℝ) * (φz - φ0 - qz.re)))) * (νz / ν0) := by ring
    _ = _ := by rw [e1]; ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
-/
theorem morseGen_sq_le_sum {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by
  have hs : 0 ≤ ∑ j, ‖z j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have h : ‖z‖ ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hs

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem morseGen_levi_le {D : ℕ} (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (B z z + B (I • z) (I • z)) / 4 ≤ ‖B‖ / 2 * ‖z‖ ^ 2 := by
  have h1 : B z z ≤ ‖B‖ * ‖z‖ * ‖z‖ := (le_abs_self _).trans (B.le_opNorm₂ z z)
  have h2 : B (I • z) (I • z) ≤ ‖B‖ * ‖I • z‖ * ‖I • z‖ :=
    (le_abs_self _).trans (B.le_opNorm₂ _ _)
  have hI : ‖I • z‖ = ‖z‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hI] at h2
  nlinarith

end ReciprocityTheory.GeometryOfNumbersTheory
