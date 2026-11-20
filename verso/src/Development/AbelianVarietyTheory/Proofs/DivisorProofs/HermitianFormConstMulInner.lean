import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory

/- English proof (translation)
Use `⟨∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]`. Establish `: 0 < Real.pi / (2 * Real.pi)` using `by positivity`. Check the signs of the components of the expression. Rewrite using `[← integral_complex_ofReal]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]`. Rewrite using `[← Complex.ofReal_mul, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussian_selfPairing_pos (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ (∫ x, GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x *
      starRingEnd ℂ (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x)) = (r : ℂ) := by
  refine ⟨∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2), ?_, ?_⟩
  · rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
    have : 0 < Real.pi / (2 * Real.pi) := by positivity
    positivity
  · rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

/- English proof (translation)
Introduce `n B hherm hpos hid`. Use `set h₀ : Sch (Fin n) := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) with hh₀`. Take `⟨r, hr, hs⟩` from `gaussian_selfPairing_pos n`. Establish `hb : B h₀ h₀ = ((B h₀ h₀).re : ℂ)`. Use `hherm h₀ h₀` as an intermediate fact.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `h2 : (B h₀ h₀).im = -(B h₀ h₀).im` using `by conv_lhs => rw [this]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨(B h₀ h₀).re / r, div_nonneg (hpos h₀) hr.le, fun h h' => ?_⟩` and prove the remaining obligations. Establish `key` using `hid h₀ h' h₀ h`. Rewrite `key` using `[hs, hb]`. Establish `hr0 : (r : ℂ) ≠ 0` using `by exact_mod_cast hr.ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `key`.
-/
theorem hermitian_form_eq_smul_l2 : ∀ (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ), (∀ h h', B h' h = starRingEnd ℂ (B h h')) →
    (∀ h, 0 ≤ (B h h).re) →
    (∀ f f' g g' : Sch (Fin n), (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' = (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hherm hpos hid
  set h₀ : Sch (Fin n) := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) with hh₀
  obtain ⟨r, hr, hs⟩ := gaussian_selfPairing_pos n
  have hb : B h₀ h₀ = ((B h₀ h₀).re : ℂ) := by
    have := hherm h₀ h₀
    apply Complex.ext
    · simp
    · have h2 : (B h₀ h₀).im = -(B h₀ h₀).im := by
        conv_lhs => rw [this]
        simp
      simp; linarith
  refine ⟨(B h₀ h₀).re / r, div_nonneg (hpos h₀) hr.le, fun h h' => ?_⟩
  have key := hid h₀ h' h₀ h
  rw [hs, hb] at key
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  linear_combination key

end GlobalTheory
