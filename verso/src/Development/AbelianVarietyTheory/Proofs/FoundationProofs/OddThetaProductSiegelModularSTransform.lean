import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableTheta
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasDerivAtOddJacobiThetaZeroEtaCube

open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

noncomputable section

namespace GlobalTheory.Sieg.ThInv

open GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv

/- English proof (translation)
Rewrite using `[show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]`.
-/
theorem exp_pi_I_half : cexp (π * I / 2) = I := by
  rw [show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]

/- English proof (translation)
Establish `hB` using `hasProd_tailProd τ (cexp (2 * π * I * z))`. Establish `hC` using `hasProd_tailProd τ (cexp (-(2 * π * I * z)))`. Establish `hP : ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) = tailProd τ (cexp (2 * π * I * z)) * tailProd τ (cexp (-(2 * π * I * z)))`. Rewrite using `[← (hB.mul hC).tprod_eq]`. Use `tprod_congr fun n => ?_` and prove the remaining obligations.

Rewrite using `[ModularForm.eta_q_eq_pow, Complex.exp_neg]`. Both sides reduce to the same expression. Establish `hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))`. Simplify using `[tailProd]`. Establish `h1 : cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) = I * Function.Periodic.qParam 24 (τ : ℂ) * ee ((τ : ℂ) / 12) * ee (z / 2)`.

Rewrite using `[Function.Periodic.qParam, ee, ee]`. Use `conv_rhs => rw [← exp_pi_I_half]`. Rewrite using `[exp_pi_I_half]`. Use `nth_rewrite 3 [← exp_pi_I_half]`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ee (-z / 2) = ee (z / 2) * cexp (-(2 * π * I * z))`. Rewrite using `[ee, ee, ← Complex.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[oddTheta, jacobiTheta₂_shift GlobalTheory.JacobiTriple.tripleProduct, th, hP, ModularForm.eta, ← hT1, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem oddTheta_eq (τ : ℍ) (z : ℂ) : oddTheta τ z = I * ModularForm.eta (τ : ℂ) * th z τ := by
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have hC := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have hP : ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) =
      tailProd τ (cexp (2 * π * I * z)) * tailProd τ (cexp (-(2 * π * I * z))) := by
    rw [← (hB.mul hC).tprod_eq]
    refine tprod_congr fun n => ?_
    rw [ModularForm.eta_q_eq_pow, Complex.exp_neg]
    rfl
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have h1 : cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) =
      I * Function.Periodic.qParam 24 (τ : ℂ) * ee ((τ : ℂ) / 12) * ee (z / 2) := by
    rw [Function.Periodic.qParam, ee, ee]
    conv_rhs => rw [← exp_pi_I_half]
    rw [exp_pi_I_half]
    nth_rewrite 3 [← exp_pi_I_half]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h2 : ee (-z / 2) = ee (z / 2) * cexp (-(2 * π * I * z)) := by
    rw [ee, ee, ← Complex.exp_add]
    congr 1; ring
  rw [oddTheta, jacobiTheta₂_shift GlobalTheory.JacobiTriple.tripleProduct, th, hP, ModularForm.eta, ← hT1, h1, h2]
  ring

/- English proof (translation)
Establish `hτ : (τ : ℂ) ≠ 0` using `τ.ne_zero`. Establish `h0 : -I * (τ : ℂ) ≠ 0` using `mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ`. Establish `hre : 0 < (-I * (τ : ℂ)).re` using `by simpa using τ.im_pos`. Establish `ha` using `abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))`. Establish `hl : log (I * (-I * (τ : ℂ))) = log I + log (-I * (τ : ℂ))`.

Rewrite using `[Complex.log_mul_eq_add_log_iff I_ne_zero h0, Complex.arg_I]`. Apply the tactic sequence `constructor <;> linarith [ha.1, ha.2, Real.pi_pos]`. Rewrite `hl` using `[show I * (-I * (τ : ℂ)) = τ by linear_combination (-(τ : ℂ)) * I_sq]`. Rewrite using `[Complex.sqrt, Complex.sqrt, Complex.cpow_def_of_ne_zero I_ne_zero, Complex.cpow_def_of_ne_zero hτ, Complex.cpow_def_of_ne_zero h0, hl, ← Complex.exp_neg, ← Complex.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqrt_eq (τ : ℍ) : (Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : -I * (τ : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ
  have hre : 0 < (-I * (τ : ℂ)).re := by simpa using τ.im_pos
  have ha := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))
  have hl : log (I * (-I * (τ : ℂ))) = log I + log (-I * (τ : ℂ)) := by
    rw [Complex.log_mul_eq_add_log_iff I_ne_zero h0, Complex.arg_I]
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [show I * (-I * (τ : ℂ)) = τ by linear_combination (-(τ : ℂ)) * I_sq] at hl
  rw [Complex.sqrt, Complex.sqrt, Complex.cpow_def_of_ne_zero I_ne_zero, Complex.cpow_def_of_ne_zero hτ,
    Complex.cpow_def_of_ne_zero h0, hl,
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1; ring

/- English proof (translation)
Establish `h` using `ModularForm.eta_comp_eq_csqrt_I_inv τ.2`. Rewrite using `[← sqrt_eq, mul_assoc]`. Simplify using `using h`.
-/
theorem eta_S (τ : ℍ) :
    ModularForm.eta (-1 / (τ : ℂ)) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ModularForm.eta (τ : ℂ) := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  rw [← sqrt_eq, mul_assoc]
  simpa using h

/- English proof (translation)
Rewrite using `[UpperHalfPlane.modular_S_smul]`. Simplify using `[neg_div]`.
-/
theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [neg_div]

/- English proof (translation)
Establish `hτ : (τ : ℂ) ≠ 0` using `τ.ne_zero`. Establish `h0 : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0`. Rewrite using `[Ne, Complex.cpow_eq_zero_iff]`. Conclude with `fun h => mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ h.1`. Establish `hI : -I = cexp (-(π * I / 2))`.

Rewrite using `[Complex.exp_neg, exp_pi_I_half, Complex.inv_I]`. Rewrite using `[oddTheta, oddTheta, coe_S_smul, jacobiTheta₂_functional_equation (z + ((τ : ℂ) + 1) / 2) τ, show z / (τ : ℂ) + (-1 / (τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) / τ + -1 / (τ : ℂ) by field_simp; ring, jacobiTheta₂_add_left']`. Generalize the expression as in `jacobiTheta₂ ((z + ((τ : ℂ) + 1) / 2) / τ) (-1 / (τ : ℂ)) = J`. Generalize the expression as in `(-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = s at h0 ⊢`. Establish `hE : ∀ A B C D : ℂ, cexp A * s * cexp B * (cexp C * (1 / s * cexp D * J)) = cexp (A + B + C + D) * J`.

Introduce `A B C D`. Simplify using `only [Complex.exp_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[ee]`. Use `conv_rhs => rw [hI]`.

Rewrite using `[hE, ← mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem oddTheta_S (τ : ℍ) (z : ℂ) :
    oddTheta (ModularGroup.S • τ) (z / (τ : ℂ)) =
      -I * (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ee (z ^ 2 / (2 * (τ : ℂ))) * oddTheta τ z := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ h.1
  have hI : -I = cexp (-(π * I / 2)) := by
    rw [Complex.exp_neg, exp_pi_I_half, Complex.inv_I]
  rw [oddTheta, oddTheta, coe_S_smul, jacobiTheta₂_functional_equation (z + ((τ : ℂ) + 1) / 2) τ,
    show z / (τ : ℂ) + (-1 / (τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) / τ + -1 / (τ : ℂ) by
      field_simp; ring, jacobiTheta₂_add_left']
  generalize jacobiTheta₂ ((z + ((τ : ℂ) + 1) / 2) / τ) (-1 / (τ : ℂ)) = J
  generalize (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = s at h0 ⊢
  have hE : ∀ A B C D : ℂ, cexp A * s * cexp B * (cexp C * (1 / s * cexp D * J)) =
      cexp (A + B + C + D) * J := by
    intro A B C D
    simp only [Complex.exp_add]
    field_simp
  rw [ee]
  conv_rhs => rw [hI]
  rw [hE, ← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

/- English proof (translation)
Introduce `τ z`. Establish `h` using `oddTheta_S τ z`. Rewrite `h` using `[oddTheta_eq, oddTheta_eq]`. Establish `hne : I * ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ) ≠ 0` using `mul_ne_zero I_ne_zero (ModularForm.eta_ne_zero (ModularGroup.S • τ).2)`. Use `mul_left_cancel₀ hne ?_` and prove the remaining obligations.

Rewrite using `[h, coe_S_smul, eta_S]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem th_S : ∀ (τ : ℍ) (z : ℂ), th (z / (τ : ℂ)) (ModularGroup.S • τ) =
    -Complex.I * ee (z ^ 2 / (2 * (τ : ℂ))) * th z τ := by
  intro τ z
  have h := oddTheta_S τ z
  rw [oddTheta_eq, oddTheta_eq] at h
  have hne : I * ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (ModularForm.eta_ne_zero (ModularGroup.S • τ).2)
  refine mul_left_cancel₀ hne ?_
  rw [h, coe_S_smul, eta_S]
  ring

end GlobalTheory.Sieg.ThInv
