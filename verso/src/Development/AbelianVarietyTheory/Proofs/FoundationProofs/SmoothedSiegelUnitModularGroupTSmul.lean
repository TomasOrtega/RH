import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

/- English proof (translation)
Rewrite using `[UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coe_T_smul (τ : ℍ) : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  push_cast; ring

/- English proof (translation)
Unfold `ee`. Rewrite using `[show 2 * (Real.pi : ℂ) * Complex.I * (z + 1) = 2 * Real.pi * Complex.I * z + 2 * Real.pi * Complex.I by ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]`.
-/
theorem ee_add_one (z : ℂ) : ee (z + 1) = ee z := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (z + 1) = 2 * Real.pi * Complex.I * z + 2 * Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/- English proof (translation)
Simplify using `[act, ModularGroup.T, Fin.sum_univ_two]`.
-/
theorem rowVectorMulIntMatrixSL2_modularGroupT_apply (x : Fin 2 → ℚ) : act x ModularGroup.T 0 = x 0 ∧ act x ModularGroup.T 1 = x 0 + x 1 := by
  simp [act, ModularGroup.T, Fin.sum_univ_two]

/- English proof (translation)
Take `⟨h0, h1⟩` from `rowVectorMulIntMatrixSL2_modularGroupT_apply x`. Simplify using `only [pt, coe_T_smul, h0, h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pt_T_smul (x : Fin 2 → ℚ) (τ : ℍ) : pt x (ModularGroup.T • τ) = pt (act x ModularGroup.T) τ := by
  obtain ⟨h0, h1⟩ := rowVectorMulIntMatrixSL2_modularGroupT_apply x
  simp only [pt, coe_T_smul, h0, h1]
  push_cast; ring

/- English proof (translation)
Introduce `c x τ`. Simplify using `only [sg]`. Rewrite using `[pt_T_smul, coe_T_smul, ee_add_one]`.
-/
theorem sg_T_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), sg c x (ModularGroup.T • τ) = sg c (act x ModularGroup.T) τ := by
  intro c x τ
  simp only [sg]
  rw [pt_T_smul, coe_T_smul, ee_add_one]

end GlobalTheory.Sieg
