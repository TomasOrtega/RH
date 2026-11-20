import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImageSqIoi
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SquareImageInterval.main`. Consider the case `exact _root_.GlobalTheory.SquareImageInterval.main`. Consider the case `(apply _root_.GlobalTheory.SquareImageInterval.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SquareImageInterval.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SquareImageInterval.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SquareImageInterval.main ..)`.
-/
theorem lintegral_Ioi_mul_eq_lintegral_Ioi_sqrt (G : ℝ → ENNReal) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r
      = ∫⁻ u in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G (Real.sqrt u) := by
  first
  | exact @_root_.GlobalTheory.SquareImageInterval.main
  | exact _root_.GlobalTheory.SquareImageInterval.main
  | (apply _root_.GlobalTheory.SquareImageInterval.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareImageInterval.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareImageInterval.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareImageInterval.main ..)

/- English proof (translation)
Use `set G : ℝ → ENNReal := fun r => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hG`. Establish `h1 : ∫⁻ z, g z = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r`. Rewrite using `[← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod]`. Establish `hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 * g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))`. Use `(ENNReal.measurable_ofReal.comp measurable_fst).mul (hg.comp ?_)` and prove the remaining obligations.

Conclude with `(by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)).measurable`. Establish `he : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • g (Complex.polarCoord.symm p)) = fun p : ℝ × ℝ => ENNReal.ofReal p.1 * g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))`. Use function extensionality and compare the values at `p`. Simplify using `[Complex.polarCoord_symm_apply, Complex.exp_mul_I]`. Rewrite using `[he, setLIntegral_prod _ hm.aemeasurable]`.

Use `lintegral_congr fun r => ?_` and prove the remaining obligations. Simplify using `only [hG]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Establish `h2 : ∫⁻ u in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G (Real.sqrt u) = ∫⁻ u, (2 : ENNReal)⁻¹ * G (Real.sqrt u)`. Rewrite using `[← lintegral_indicator measurableSet_Ioi]`.

Use `lintegral_congr fun u => ?_` and prove the remaining obligations. Distinguish the cases in `hu : u ∈ Set.Ioi (0 : ℝ)`. Rewrite using `[Set.indicator_of_mem hu]`. Rewrite using `[Set.indicator_of_notMem hu, Real.sqrt_eq_zero_of_nonpos (not_lt.1 hu)]`. Simplify using `[hG, h0]`.

Establish `h3 : ∀ F : ℝ → ENNReal, ∫⁻ u, F u = ∫⁻ t, F (ε * (t - c))`. Introduce `F`. Rewrite using `[lintegral_sub_right_eq_self (fun u => F (ε * u)) c]`. Break down `hε with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules.

Simplify using `only [neg_mul, one_mul]`. Conclude with `(lintegral_neg_eq_self F).symm`. Rewrite using `[h1, lintegral_Ioi_mul_eq_lintegral_Ioi_sqrt, h2, h3]`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Simplify using `only [hG]`.

Rewrite using `[lintegral_const_mul' _ _ (by norm_num)]`.
-/
theorem lintegral_complex_eq_lintegral_sqrt_mul_exp (ε c : ℝ) (hε : ε = 1 ∨ ε = -1)
    (g : ℂ → ENNReal) (hg : Measurable g) (h0 : g 0 = 0) :
    ∫⁻ z, g z = ∫⁻ t : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
      (2 : ENNReal)⁻¹ *
        g ((Real.sqrt (ε * (t - c)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  set G : ℝ → ENNReal := fun r => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
    g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hG
  have h1 : ∫⁻ z, g z = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod]
    have hm : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal p.1 * g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
      refine (ENNReal.measurable_ofReal.comp measurable_fst).mul (hg.comp ?_)
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)).measurable
    have he : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • g (Complex.polarCoord.symm p))
        = fun p : ℝ × ℝ =>
          ENNReal.ofReal p.1 * g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
      funext p
      simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
    rw [he, setLIntegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun r => ?_
    simp only [hG]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ u in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G (Real.sqrt u)
      = ∫⁻ u, (2 : ENNReal)⁻¹ * G (Real.sqrt u) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Real.sqrt_eq_zero_of_nonpos (not_lt.1 hu)]
      simp [hG, h0]
  have h3 : ∀ F : ℝ → ENNReal, ∫⁻ u, F u = ∫⁻ t, F (ε * (t - c)) := by
    intro F
    rw [lintegral_sub_right_eq_self (fun u => F (ε * u)) c]
    rcases hε with rfl | rfl
    · simp
    · simp only [neg_mul, one_mul]
      exact (lintegral_neg_eq_self F).symm
  rw [h1, lintegral_Ioi_mul_eq_lintegral_Ioi_sqrt, h2, h3]
  refine lintegral_congr fun t => ?_
  simp only [hG]
  rw [lintegral_const_mul' _ _ (by norm_num)]

end GlobalTheory
