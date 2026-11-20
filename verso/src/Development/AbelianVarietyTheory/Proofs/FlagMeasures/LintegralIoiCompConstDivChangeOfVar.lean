import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory

/- English proof (translation)
Introduce `κ hκ w _hw`. Establish `hκ0 : κ ≠ 0` using `ne_of_gt hκ`. Establish `himg : (fun u : ℝ => κ / u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ)`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `div_pos hκ hu`. Introduce `ht`. Establish `ht0 : t ≠ 0` using `ne_of_gt (Set.mem_Ioi.mp ht)`. Use `⟨κ / t, div_pos hκ ht, ?_⟩` and prove the remaining obligations.

Use `show κ / (κ / t) = t`. Clear the denominators using the available nonvanishing facts. Establish `hderiv : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => κ / u) (-(κ / u ^ 2)) (Set.Ioi (0 : ℝ)) u`. Introduce `u hu`. Establish `hu0 : u ≠ 0` using `ne_of_gt (Set.mem_Ioi.mp hu)`.

Establish `h` using `((hasDerivAt_inv hu0).const_mul κ).hasDerivWithinAt (s := Set.Ioi (0 : ℝ))`. Establish `hfun : (fun u : ℝ => κ / u) = fun y => κ * y⁻¹`. Use function extensionality and compare the values at `y`. Rewrite using `[div_eq_mul_inv]`. Rewrite using `[hfun]`.

Conclude with `h.congr_deriv (by ring)`. Establish `hinj : Set.InjOn (fun u : ℝ => κ / u) (Set.Ioi (0 : ℝ))`. Introduce `a ha b hb hab`. Establish `ha0 : a ≠ 0` using `ne_of_gt (Set.mem_Ioi.mp ha)`. Establish `hb0 : b ≠ 0` using `ne_of_gt (Set.mem_Ioi.mp hb)`.

Establish `hab' : κ / a = κ / b` using `hab`. Clear denominators, using `at hab'` for the nonvanishing conditions. Conclude with `hab'.symm`. Rewrite using `[← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj, himg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_))` and prove the remaining obligations.

Establish `hu : 0 < u` using `Set.mem_Ioi.mp hu`. Establish `hu0 : u ≠ 0` using `ne_of_gt hu`. Establish `hκu : 0 < κ / u` using `div_pos hκ hu`. Establish `hsq : 0 < u ^ 2` using `by positivity`. Establish `hinv : κ / (κ / u) = u` using `by field_simp`.

Establish `habs : |(-(κ / u ^ 2))| = κ / u ^ 2`. Rewrite using `[abs_neg, abs_of_pos (div_pos hκ hsq)]`. Establish `hne : ENNReal.ofReal (κ / u) ≠ 0`. Rewrite using `[Ne, ENNReal.ofReal_eq_zero, not_le]`. Conclude with `hκu`.

Simplify using `only [hinv, habs]`. Rewrite using `[ENNReal.mul_div_cancel_right hne ENNReal.ofReal_ne_top, ENNReal.ofReal_div_of_pos hsq]`. Simplify using `only [div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_Ioi_comp_const_div_mul_div :
    ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w →
      ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t =
        ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro κ hκ w _hw
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have himg : (fun u : ℝ => κ / u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hκ hu
    · intro ht
      have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
      refine ⟨κ / t, div_pos hκ ht, ?_⟩
      show κ / (κ / t) = t
      field_simp
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => κ / u) (-(κ / u ^ 2)) (Set.Ioi (0 : ℝ)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hu)
    have h := ((hasDerivAt_inv hu0).const_mul κ).hasDerivWithinAt (s := Set.Ioi (0 : ℝ))
    have hfun : (fun u : ℝ => κ / u) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [hfun]
    exact h.congr_deriv (by ring)
  have hinj : Set.InjOn (fun u : ℝ => κ / u) (Set.Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hab' : κ / a = κ / b := hab
    field_simp at hab'
    exact hab'.symm
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj,
    himg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun u hu => ?_))
  have hu : 0 < u := Set.mem_Ioi.mp hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hκu : 0 < κ / u := div_pos hκ hu
  have hsq : 0 < u ^ 2 := by positivity
  have hinv : κ / (κ / u) = u := by field_simp
  have habs : |(-(κ / u ^ 2))| = κ / u ^ 2 := by
    rw [abs_neg, abs_of_pos (div_pos hκ hsq)]
  have hne : ENNReal.ofReal (κ / u) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hκu
  simp only [hinv, habs]
  rw [ENNReal.mul_div_cancel_right hne ENNReal.ofReal_ne_top, ENNReal.ofReal_div_of_pos hsq]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory
