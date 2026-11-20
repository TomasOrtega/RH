import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

namespace GlobalTheory

/- English proof (translation)
Establish `hJ : ∀ (x : l ⊕ l → ℝ) (b : l ⊕ l), sympl x (Matrix.J l ℝ *ᵥ Pi.single b 1) = x b`. Introduce `x b`. Apply the tactic sequence `rcases b with b | b <;>`. Simplify using `[sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]`. Establish `hcol : ∀ b, ∑ i, v i b • u i = Matrix.J l ℝ *ᵥ Pi.single b 1`.

Introduce `b`. Use `h (Matrix.J l ℝ *ᵥ Pi.single b 1)` as an intermediate fact. Simplify using `only [hJ] at this`. Conclude with `this`. Establish `hcoef : ∀ a b, ∑ i, (X *ᵥ u i) a * v i b = (X * Matrix.J l ℝ) a b`.

Introduce `a b`. Use `congrArg (fun w => (X *ᵥ w) a) (hcol b)` as an intermediate fact. Simplify using `only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_mulVec] at this`. Establish `e : ((X * Matrix.J l ℝ) *ᵥ Pi.single b 1) a = (X * Matrix.J l ℝ) a b`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Rewrite using `[← e, ← this]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hT : ∀ i, dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i) = ∑ a, ∑ b, (((X *ᵥ u i) a * v i b : ℝ) : ℂ) • (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1))`. Introduce `i`. Rewrite using `[dRho_eq_sum (X *ᵥ u i), dRho_eq_sum (v i)]`.

Simplify using `only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]`. Use `conv_lhs => arg 1`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `push_cast`. Use `module`. Rewrite using `[quad]`.

Use `congr 1`. Repeatedly rewrite using `[hT, ← hcoef, Finset.sum_div, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_eq_sum_symplDual (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ))
    (h : ∀ w, ∑ i, sympl (v i) w • u i = w) :
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by
  have hJ : ∀ (x : l ⊕ l → ℝ) (b : l ⊕ l), sympl x (Matrix.J l ℝ *ᵥ Pi.single b 1) = x b := by
    intro x b
    rcases b with b | b <;>
      simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Pi.single_apply,
        Matrix.one_apply]
  have hcol : ∀ b, ∑ i, v i b • u i = Matrix.J l ℝ *ᵥ Pi.single b 1 := by
    intro b
    have := h (Matrix.J l ℝ *ᵥ Pi.single b 1)
    simp only [hJ] at this
    exact this
  have hcoef : ∀ a b, ∑ i, (X *ᵥ u i) a * v i b = (X * Matrix.J l ℝ) a b := by
    intro a b
    have := congrArg (fun w => (X *ᵥ w) a) (hcol b)
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_mulVec] at this
    have e : ((X * Matrix.J l ℝ) *ᵥ Pi.single b 1) a = (X * Matrix.J l ℝ) a b := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← e, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hT : ∀ i, dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i) =
      ∑ a, ∑ b, (((X *ᵥ u i) a * v i b : ℝ) : ℂ) •
        (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1)) := by
    intro i
    rw [dRho_eq_sum (X *ᵥ u i), dRho_eq_sum (v i)]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    conv_lhs => arg 1; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    module
  rw [quad]
  congr 1
  simp_rw [hT, ← hcoef, Finset.sum_div, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

end GlobalTheory
