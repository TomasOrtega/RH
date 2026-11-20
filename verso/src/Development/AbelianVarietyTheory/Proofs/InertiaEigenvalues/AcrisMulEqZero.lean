import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

/- English proof (translation)
Introduce `l _ x y hxy`. Establish `hl : (1 : ℝ) < (l : ℝ)` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (0 : ℝ) < (l : ℝ)` using `by linarith`. Establish `hρ1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl`. Establish `hρ0 : (0 : ℝ) < (l : ℝ)⁻¹` using `inv_pos.mpr hl0`.

Establish `hG` using `isGauss_gC_target l (l : ℝ)⁻¹ le_rfl hρ1`. Establish `hc : gC l (l : ℝ)⁻¹ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l)) = (l : ℝ)⁻¹`. Rewrite using `[hG.2.2.2.2]`. Conclude with `GlobalTheory.GaussSlope.gauss_l l hρ0.le`. Establish `h0 : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) = 0`.

Establish `h` using `hG.2.2.2.1 0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l))`. Rewrite `h` using `[zero_mul, hc]`. Establish `: gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) * (1 - (l : ℝ)⁻¹) = 0` using `by linarith`. Break down `mul_eq_zero.mp this with h' | h'` into its components or cases. Conclude with `h'`.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hx` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x h.1 (l : ℝ)⁻¹ le_rfl hρ1`. Establish `hy` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y h.2 (l : ℝ)⁻¹ le_rfl hρ1`.

Establish `hm` using `hG.2.2.2.1 x y`. Rewrite `hm` using `[hxy, h0]`. Use `mul_pos hx hy` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem acris_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  intro l _ x y hxy
  have hl : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hρ0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr hl0
  have hG := isGauss_gC_target l (l : ℝ)⁻¹ le_rfl hρ1
  have hc : gC l (l : ℝ)⁻¹ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l)) = (l : ℝ)⁻¹ := by
    rw [hG.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ0.le
  have h0 : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) = 0 := by
    have h := hG.2.2.2.1 0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l))
    rw [zero_mul, hc] at h
    have : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) * (1 - (l : ℝ)⁻¹) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · linarith
  by_contra h
  push_neg at h
  have hx := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x h.1 (l : ℝ)⁻¹ le_rfl hρ1
  have hy := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y h.2 (l : ℝ)⁻¹ le_rfl hρ1
  have hm := hG.2.2.2.1 x y
  rw [hxy, h0] at hm
  have := mul_pos hx hy
  linarith

end GlobalTheory.PMon.Gauss
