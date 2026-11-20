import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.L2DbarEstimates
open scoped Matrix

namespace GlobalTheory.FubiniStudyPos

/- English proof (translation)
Introduce `n N G z hG hz w hw`. Set `L : V n ≃L[ℂ] (Fin n → ℂ)` to `PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)`. Set `g : Fin N → V n → ℂ` to `fun i v => G (L v) i`. Set `x : V n` to `GlobalTheory.FinChart.toV n z`. Establish `hLx : L x = z` using `rfl`.

Establish `hgC : ∀ i, ContDiffAt ℂ 2 (g i) x` using `fun i => ContDiffAt.comp (g := fun y => G y i) x (hG i).contDiffAt L.contDiff.contDiffAt`. Establish `hne : (fun i => g i x) ≠ 0` using `fun h0 => hz (funext fun i => congrFun h0 i)`. Set `h : V n → ℝ` to `fun v => Real.log (sqNorm (fun i => g i v))`. Establish `hh : ContDiffAt ℝ 2 h x`. Establish `hs : ContDiffAt ℝ 2 (fun v => ∑ i, Complex.normSq (g i v)) x` using `ContDiffAt.sum fun i _ => contDiffAt_normSq_comp (hgC i)`.

Conclude with `hs.log (sqNorm_pos hne).ne'`. Establish `e : (fun y => (1 / 2 : ℝ) * Real.log (∑ i, ‖G y i‖ ^ 2)) = fun y => (h ∘ GlobalTheory.FinChart.toV n) y / 2`. Use function extensionality and compare the values at `y`. Simplify using `only [Function.comp_apply, h, g, sqNorm, Complex.normSq_eq_norm_sq]`. Use `show _ = Real.log (∑ i, ‖G y i‖ ^ 2) / 2`.

Expand and normalize the polynomial expressions, which then agree. Establish `hJ : wJac n N g x *ᵥ w = fderiv ℂ G z w`. Use extensionality with `a`. Establish `hfa : HasFDerivAt (g a) ((fderiv ℂ (fun y => G y a) z).comp (L : V n →L[ℂ] (Fin n → ℂ))) x` using `(show HasFDerivAt (fun y => G y a) (fderiv ℂ (fun y => G y a) z) (L x) from (hG a).differentiableAt.hasFDerivAt).comp x L.hasFDerivAt`. Establish `hw' : w = ∑ k, w k • (Pi.single k 1 : Fin n → ℂ)`.

Use extensionality with `j`. Simplify using `[Pi.single_apply]`. Rewrite using `[fderiv_pi (fun i => (hG i).differentiableAt)]`. Simplify using `only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt hfa.differentiableAt, hfa.fderiv, ContinuousLinearMap.pi_apply]`. Use `conv_rhs => rw [hw']`.

Simplify using `[map_sum, map_smul, bas, L, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[e, GlobalTheory.FinChart.levi_half, ← GlobalTheory.FinChart.leviV_re_eq_levi hh w]`. Rewrite using `[show (fun v => ((h v : ℝ) : ℂ)) = fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ) from rfl, leviLogNormSq n N g x w hgC hne, Complex.ofReal_re]`. Use `div_pos (div_pos (sqNorm_pos fun h0 => hw ?_) (sqNorm_pos hne)) two_pos` and prove the remaining obligations.

Rewrite `h0` using `[hJ, projPerp_mulVec, sub_eq_zero]`. Rewrite using `[h0]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`.
-/
theorem levi_half_log_normSq_pos : ∀ (n N : ℕ) (G : (Fin n → ℂ) → Fin N → ℂ) (z : Fin n → ℂ),
    (∀ i, AnalyticAt ℂ (fun y => G y i) z) → G z ≠ 0 → ∀ w : Fin n → ℂ,
    fderiv ℂ G z w ∉ Submodule.span ℂ {G z} →
    0 < levi (fun y => (1 / 2 : ℝ) * Real.log (∑ i, ‖G y i‖ ^ 2)) z w := by
  intro n N G z hG hz w hw
  let L : V n ≃L[ℂ] (Fin n → ℂ) := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)
  let g : Fin N → V n → ℂ := fun i v => G (L v) i
  let x : V n := GlobalTheory.FinChart.toV n z
  have hLx : L x = z := rfl
  have hgC : ∀ i, ContDiffAt ℂ 2 (g i) x := fun i =>
    ContDiffAt.comp (g := fun y => G y i) x (hG i).contDiffAt L.contDiff.contDiffAt
  have hne : (fun i => g i x) ≠ 0 := fun h0 => hz (funext fun i => congrFun h0 i)
  let h : V n → ℝ := fun v => Real.log (sqNorm (fun i => g i v))
  have hh : ContDiffAt ℝ 2 h x := by
    have hs : ContDiffAt ℝ 2 (fun v => ∑ i, Complex.normSq (g i v)) x :=
      ContDiffAt.sum fun i _ => contDiffAt_normSq_comp (hgC i)
    exact hs.log (sqNorm_pos hne).ne'
  have e : (fun y => (1 / 2 : ℝ) * Real.log (∑ i, ‖G y i‖ ^ 2)) =
      fun y => (h ∘ GlobalTheory.FinChart.toV n) y / 2 := by
    funext y
    simp only [Function.comp_apply, h, g, sqNorm, Complex.normSq_eq_norm_sq]
    show _ = Real.log (∑ i, ‖G y i‖ ^ 2) / 2
    ring
  have hJ : wJac n N g x *ᵥ w = fderiv ℂ G z w := by
    ext a
    have hfa : HasFDerivAt (g a) ((fderiv ℂ (fun y => G y a) z).comp
        (L : V n →L[ℂ] (Fin n → ℂ))) x :=
      (show HasFDerivAt (fun y => G y a) (fderiv ℂ (fun y => G y a) z) (L x) from
        (hG a).differentiableAt.hasFDerivAt).comp x L.hasFDerivAt
    have hw' : w = ∑ k, w k • (Pi.single k 1 : Fin n → ℂ) := by
      ext j; simp [Pi.single_apply]
    rw [fderiv_pi (fun i => (hG i).differentiableAt)]
    simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt hfa.differentiableAt, hfa.fderiv,
      ContinuousLinearMap.pi_apply]
    conv_rhs => rw [hw']
    simp [map_sum, map_smul, bas, L, mul_comm]
    rfl
  rw [e, GlobalTheory.FinChart.levi_half, ← GlobalTheory.FinChart.leviV_re_eq_levi hh w]
  rw [show (fun v => ((h v : ℝ) : ℂ)) = fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ) from rfl,
    leviLogNormSq n N g x w hgC hne, Complex.ofReal_re]
  refine div_pos (div_pos (sqNorm_pos fun h0 => hw ?_) (sqNorm_pos hne)) two_pos
  rw [hJ, projPerp_mulVec, sub_eq_zero] at h0
  rw [h0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end GlobalTheory.FubiniStudyPos
