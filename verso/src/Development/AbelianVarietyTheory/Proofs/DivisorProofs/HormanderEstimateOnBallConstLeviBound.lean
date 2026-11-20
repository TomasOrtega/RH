import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BallExistsEtaleSteinExhaustionStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.HormanderBall

open ReciprocityTheory.ChartRestriction.G.AR.Up.HE

/- English proof (translation)
Unfold `wdb`. Conclude with `(((measurable_fderiv_apply_const ℝ g _).add ((measurable_fderiv_apply_const ℝ g _).const_mul _)).div_const _)`.
-/
theorem measurable_wdb (n : ℕ) (j : Fin n) (g : V n → ℂ) : Measurable (wdb n j g) := by
  unfold wdb
  exact (((measurable_fderiv_apply_const ℝ g _).add
    ((measurable_fderiv_apply_const ℝ g _).const_mul _)).div_const _)

/- English proof (translation)
Establish `h1 : ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ≤ ∑ j, ‖a j‖ * ‖ξ j‖`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_conj]`. Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖ξ j‖)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sum_mul_conj_sq_le {n : ℕ} (a ξ : Fin n → ℂ) :
    ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ≤ ∑ j, ‖a j‖ * ‖ξ j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖ξ j‖)
  calc ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖ξ j‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2

/- English proof (translation)
Introduce `n c r t φ F0 ht hφ hF0 hlevi`. Establish `hU : IsOpen (ball c r)` using `isOpen_ball`. Take `⟨X, hX⟩` from `GlobalTheory.T.ball_exists_etaleStein_exhaustion n c r`. Use `set h : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (t⁻¹ * ∑ j, ‖wdb n j F0 v‖ ^ 2) with hhdef`. Establish `hh : Measurable h`.

Use `ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)` and prove the remaining obligations. Conclude with `Finset.measurable_sum _ fun j _ => ((measurable_wdb n j F0).norm.pow_const 2)`. Establish `hb : ∀ y ∈ ball c r, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re`. Introduce `y hy ξ`. Rewrite using `[hhdef, ← ENNReal.ofReal_mul (by positivity)]`.

Use `ENNReal.ofReal_le_ofReal ((norm_sum_mul_conj_sq_le _ _).trans ?_)` and prove the remaining obligations. Establish `h1` using `hlevi y hy ξ`. Establish `h2 : ∑ j, ‖ξ j‖ ^ 2 ≤ t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re`. Rewrite using `[le_inv_mul_iff₀ ht]`. Conclude with `h1`.

Establish `h3 : 0 ≤ ∑ j, ‖wdb n j F0 y‖ ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Take `⟨F, hF, hest⟩` from `hormander n (ball c r) X (fun x => φ x.1) (fun x => F0 x.1) (fun x => h x.1) (by rw [hX]; exact smoothR_val hφ) (fun x ξ => by`. Rewrite using `[hX, levi_val hU]`. Conclude with `le_trans (by positivity) (hlevi x.1 x.2 ξ))`.

Use the proof step `(by rw [hX]; exact smooth_val hF0)`. Use the proof step `(hh.comp measurable_subtype_coe) (fun x ξ => by`. Use `hb x.1 x.2 ξ` as an intermediate fact. Rewrite using `[hX]`. Use `show ENNReal.ofReal (‖dbarDot n Subtype.val (fun x : ball c r => F0 x.1) x ξ‖ ^ 2) ≤ h x.1 * ENNReal.ofReal (Levi n Subtype.val (fun x : ball c r => φ x.1) x ξ).re`.

Simplify using `only [dbarDot, db_val hU]`. Rewrite using `[levi_val hU]`. Conclude with `this)`. Use `⟨ext0 F, differentiableOn_extendByZero hU (hX ▸ hF), ?_⟩` and prove the remaining obligations. Establish `hest' : wint n Subtype.val (fun x : ball c r => F0 x.1 - F x) (fun x : ball c r => φ x.1) ≤ ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : ball c r → V n)`.

Rewrite `hest` using `[hX]`. Conclude with `hest`. Establish `h4 : ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - ext0 F v‖ ^ 2 * Real.exp (-φ v)) ≤ ∫⁻ v in ball c r, h v * ENNReal.ofReal (Real.exp (-φ v))`. Rewrite using `[← lintegral_val hU, ← lintegral_val hU]`. Simplify `hest'` using `[wint, extendByZeroOnSubset_apply_coe]`.

Use `h4.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `setLIntegral_congr_fun hU.measurableSet fun v _ => ?_` and prove the remaining obligations. Rewrite using `[hhdef, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Put the polynomial expressions in normal form.
-/
theorem hormander_ball : ∀ (n : ℕ) (c : V n) (r t : ℝ) (φ : V n → ℝ) (F0 : V n → ℂ), 0 < t → ContDiffOn ℝ ∞ φ (ball c r) → ContDiffOn ℝ ∞ F0 (ball c r) → (∀ v ∈ ball c r, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (φ w : ℂ)) v ξ).re) → ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball c r) ∧ ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - F v‖ ^ 2 * Real.exp (-φ v)) ≤ ENNReal.ofReal t⁻¹ * ∫⁻ v in ball c r, ENNReal.ofReal ((∑ j, ‖wdb n j F0 v‖ ^ 2) * Real.exp (-φ v)) := by
  intro n c r t φ F0 ht hφ hF0 hlevi
  have hU : IsOpen (ball c r) := isOpen_ball
  obtain ⟨X, hX⟩ := GlobalTheory.T.ball_exists_etaleStein_exhaustion n c r
  set h : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (t⁻¹ * ∑ j, ‖wdb n j F0 v‖ ^ 2) with hhdef
  have hh : Measurable h := by
    refine ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun j _ => ((measurable_wdb n j F0).norm.pow_const 2)
  have hb : ∀ y ∈ ball c r, ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
    intro y hy ξ
    rw [hhdef, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((norm_sum_mul_conj_sq_le _ _).trans ?_)
    have h1 := hlevi y hy ξ
    have h2 : ∑ j, ‖ξ j‖ ^ 2 ≤ t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
      rw [le_inv_mul_iff₀ ht]; exact h1
    have h3 : 0 ≤ ∑ j, ‖wdb n j F0 y‖ ^ 2 := by positivity
    calc (∑ j, ‖wdb n j F0 y‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2
        ≤ (∑ j, ‖wdb n j F0 y‖ ^ 2) * (t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re) := by
          gcongr
      _ = _ := by ring
  obtain ⟨F, hF, hest⟩ := hormander n (ball c r) X (fun x => φ x.1) (fun x => F0 x.1)
    (fun x => h x.1)
    (by rw [hX]; exact smoothR_val hφ)
    (fun x ξ => by
      rw [hX, levi_val hU]
      exact le_trans (by positivity) (hlevi x.1 x.2 ξ))
    (by rw [hX]; exact smooth_val hF0)
    (hh.comp measurable_subtype_coe) (fun x ξ => by
      have := hb x.1 x.2 ξ
      rw [hX]
      show ENNReal.ofReal (‖dbarDot n Subtype.val (fun x : ball c r => F0 x.1) x ξ‖ ^ 2) ≤
        h x.1 * ENNReal.ofReal (Levi n Subtype.val (fun x : ball c r => φ x.1) x ξ).re
      simp only [dbarDot, db_val hU]
      rw [levi_val hU]
      exact this)
  refine ⟨ext0 F, differentiableOn_extendByZero hU (hX ▸ hF), ?_⟩
  have hest' : wint n Subtype.val (fun x : ball c r => F0 x.1 - F x) (fun x : ball c r => φ x.1) ≤
      ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : ball c r → V n) := by
    rw [hX] at hest; exact hest
  have h4 : ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - ext0 F v‖ ^ 2 * Real.exp (-φ v)) ≤
      ∫⁻ v in ball c r, h v * ENNReal.ofReal (Real.exp (-φ v)) := by
    rw [← lintegral_val hU, ← lintegral_val hU]
    simpa [wint, extendByZeroOnSubset_apply_coe] using hest'
  refine h4.trans (le_of_eq ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hU.measurableSet fun v _ => ?_
  rw [hhdef, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end GlobalTheory.HormanderBall
