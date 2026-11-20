import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound

noncomputable section

open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.PerUInt

def phi (x : ℝ) : ℝ := ((1 + |x|) ^ 2)⁻¹

def gk (k : ℕ) (σ Y : ℝ) : ℝ :=
  if 0 < Y then Y ^ ((k : ℝ) - 1 - σ) * Real.exp (-(2 * Real.pi * Y)) else 0

/- English proof (translation)
Unfold `phi`. Use `fun_prop`.
-/
theorem measurable_phi : Measurable phi := by
  unfold phi
  fun_prop

/- English proof (translation)
Unfold `phi`. Check the signs of the components of the expression.
-/
theorem phi_nonneg (x : ℝ) : 0 ≤ phi x := by
  unfold phi
  positivity

/- English proof (translation)
Unfold `phi`. Establish `h0` using `abs_nonneg x`. Apply `inv_le_one_of_one_le₀` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem phi_le_one (x : ℝ) : phi x ≤ 1 := by
  unfold phi
  have h0 := abs_nonneg x
  apply inv_le_one_of_one_le₀
  nlinarith

/- English proof (translation)
Establish `h` using `integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)`. Use `h.congr (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [phi, Real.norm_eq_abs]`. Rewrite using `[Real.rpow_neg (by positivity)]`. Use `norm_cast`.
-/
theorem integrable_phi : Integrable phi := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [phi, Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity)]
  norm_cast

/- English proof (translation)
Unfold `gk`. Use `Measurable.ite measurableSet_Ioi ?_ measurable_const` and prove the remaining obligations. Use `fun_prop`.
-/
theorem measurable_gk (k : ℕ) (σ : ℝ) : Measurable (gk k σ) := by
  unfold gk
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/- English proof (translation)
Unfold `gk`. Use `split_ifs with h`. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
theorem gk_nonneg (k : ℕ) (σ Y : ℝ) : 0 ≤ gk k σ Y := by
  unfold gk
  split_ifs with h
  · positivity
  · exact le_rfl

/- English proof (translation)
Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hb` using `GlobalTheory.CompanionTheory.WmFE.integrableOn_rpow_exp (σ := (k : ℝ) - 1 - σ) (by linarith) (show 0 < 2 * Real.pi by positivity)`. Establish `hs : Function.support (gk k σ) ⊆ Ioi 0`. Introduce `x hx`. Assume the negation of the conclusion as `hn`.

Conclude with `hx (by simp [gk, show ¬ 0 < x from hn])`. Rewrite using `[← integrableOn_iff_integrable_of_support_subset hs]`. Use `IntegrableOn.congr_fun hb (fun x hx => ?_) measurableSet_Ioi` and prove the remaining obligations. Simplify using `[gk, mem_Ioi.1 hx]`.
-/
theorem integrable_gk (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : σ < 1) : Integrable (gk k σ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb := GlobalTheory.CompanionTheory.WmFE.integrableOn_rpow_exp (σ := (k : ℝ) - 1 - σ) (by linarith)
    (show 0 < 2 * Real.pi by positivity)
  have hs : Function.support (gk k σ) ⊆ Ioi 0 := by
    intro x hx
    by_contra hn
    exact hx (by simp [gk, show ¬ 0 < x from hn])
  rw [← integrableOn_iff_integrable_of_support_subset hs]
  refine IntegrableOn.congr_fun hb (fun x hx => ?_) measurableSet_Ioi
  simp [gk, mem_Ioi.1 hx]

end GlobalTheory.CompanionTheory.PerUInt
