import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Substitute `hK` using the available equality. Establish `hgs : MeasurableSet (g '' s)` using `measurable_image_of_fderivWithin hs hf' hinj`. Establish `hL : ∫ x, φ (g x) * F x = ∫ x in s, φ (g x) * F x`. Rewrite using `[setIntegral_eq_integral_of_forall_compl_eq_zero]`. Introduce `x hx`.

Simplify using `[hF x hx]`. Establish `hR : ∫ w, φ w * (g '' s).indicator (fun w => F (h w) * |(g' (h w)).det|⁻¹) w = ∫ w in g '' s, φ w * (F (h w) * |(g' (h w)).det|⁻¹)`. Rewrite using `[← integral_indicator hgs]`. Use `congr 1`. Use function extensionality and compare the values at `w`.

Apply the tactic sequence `by_cases hw : w ∈ g '' s <;> simp [Set.indicator, hw]`. Rewrite using `[hL, hR, integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' hinj]`. Use `setIntegral_congr_fun hs ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [smul_eq_mul, hhg x hx]`.

Establish `h0 : |(g' x).det| ≠ 0` using `abs_ne_zero.mpr (hdet x hx)`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_comp_mul_eq_integral_mul_indicator_jacobian
    (d : ℕ) (g h : (Fin d → ℂ) → Fin d → ℂ) (g' : (Fin d → ℂ) → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ))
    (s : Set (Fin d → ℂ)) (F φ K : (Fin d → ℂ) → ℝ)
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x) (hinj : Set.InjOn g s)
    (hhg : ∀ x ∈ s, h (g x) = x) (hdet : ∀ x ∈ s, (g' x).det ≠ 0) (hF : ∀ x, x ∉ s → F x = 0)
    (hK : K = (g '' s).indicator (fun w => F (h w) * |(g' (h w)).det|⁻¹)) :
    ∫ x, φ (g x) * F x = ∫ w, φ w * K w := by
  subst hK
  have hgs : MeasurableSet (g '' s) := measurable_image_of_fderivWithin hs hf' hinj
  have hL : ∫ x, φ (g x) * F x = ∫ x in s, φ (g x) * F x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp [hF x hx]
  have hR : ∫ w, φ w * (g '' s).indicator (fun w => F (h w) * |(g' (h w)).det|⁻¹) w
      = ∫ w in g '' s, φ w * (F (h w) * |(g' (h w)).det|⁻¹) := by
    rw [← integral_indicator hgs]
    congr 1
    funext w
    by_cases hw : w ∈ g '' s <;> simp [Set.indicator, hw]
  rw [hL, hR, integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' hinj]
  refine setIntegral_congr_fun hs ?_
  intro x hx
  simp only [smul_eq_mul, hhg x hx]
  have h0 : |(g' x).det| ≠ 0 := abs_ne_zero.mpr (hdet x hx)
  field_simp

end GlobalTheory
