import Mathlib

namespace GlobalTheory.SquareImageInterval

open MeasureTheory

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩`. Conclude with `pow_pos (Set.mem_Ioi.1 hr) 2`. Introduce `hy`.

Conclude with `⟨√y, Real.sqrt_pos.2 hy, Real.sq_sqrt (le_of_lt hy)⟩`.
-/
theorem image_sq_Ioi : (fun r : ℝ => r ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact pow_pos (Set.mem_Ioi.1 hr) 2
  · intro hy
    exact ⟨√y, Real.sqrt_pos.2 hy, Real.sq_sqrt (le_of_lt hy)⟩

/- English proof (translation)
Introduce `G`. Establish `hinj : Set.InjOn (fun r : ℝ => r ^ 2) (Set.Ioi 0)`. Introduce `a ha b hb hab`. Establish `ha' : 0 < a` using `ha`. Establish `hb' : 0 < b` using `hb`.

Establish `h2 : a ^ 2 = b ^ 2` using `hab`. Use polynomial arithmetic with `[h2]`. Establish `hder : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * x) (Set.Ioi 0) x`. Introduce `x _`. Simplify using `using (hasDerivAt_pow 2 x).hasDerivWithinAt`.

Establish `h` using `lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj (fun u => (2 : ENNReal)⁻¹ * G √u)`. Rewrite `h` using `[image_sq_Ioi]`. Rewrite using `[h]`. Use `setLIntegral_congr_fun measurableSet_Ioi ?_` and prove the remaining obligations. Introduce `x hx`.

Establish `hx' : 0 < x` using `hx`. Simplify using `only`. Rewrite using `[abs_of_pos (by positivity : (0 : ℝ) < 2 * x), Real.sqrt_sq (le_of_lt hx'), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]`.

Use `_ = 2 * ENNReal.ofReal x * (2⁻¹ * G x) := by ring`.
-/
theorem main : ∀ (G : ℝ → ENNReal), ∫⁻ (r : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r
    = ∫⁻ (u : ℝ) in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G √u := by
  intro G
  have hinj : Set.InjOn (fun r : ℝ => r ^ 2) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    have h2 : a ^ 2 = b ^ 2 := hab
    nlinarith [h2]
  have hder : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * x) (Set.Ioi 0) x := by
    intro x _
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (fun u => (2 : ENNReal)⁻¹ * G √u)
  rw [image_sq_Ioi] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  have hx' : 0 < x := hx
  simp only
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * x), Real.sqrt_sq (le_of_lt hx'),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal x * G x = (2 * 2⁻¹) * (ENNReal.ofReal x * G x) := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ = 2 * ENNReal.ofReal x * (2⁻¹ * G x) := by ring

end GlobalTheory.SquareImageInterval
