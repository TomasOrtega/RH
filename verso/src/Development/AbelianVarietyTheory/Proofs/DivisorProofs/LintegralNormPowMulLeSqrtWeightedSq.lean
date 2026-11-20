import Mathlib

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `E F _ _ _ _ _ μ _ _`. Use `set s : ℕ := finrank ℝ E + 1 with hs`. Establish `hfin : ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ < ∞`. Apply `finite_integral_one_add_norm` to reduce the goal to its premises. Rewrite using `[hs]`.

Use `push_cast`. Establish `: (0 : ℝ) ≤ finrank ℝ E` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set A := ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ with hA`. Use `set B : ℝ≥0∞ := ENNReal.ofReal (2 ^ (2 * s - 1)) with hB`.

Use `⟨A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne) (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)`. Introduce `H hH k`. Set `f : E → ℝ≥0∞` to `fun z => ENNReal.ofReal (((1 + ‖z‖) ^ s)⁻¹)`. Set `g : E → ℝ≥0∞` to `fun z => ENNReal.ofReal ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖))`.

Establish `hf : AEMeasurable f μ`. Apply `Measurable.aemeasurable` to reduce the goal to its premises. Apply `ENNReal.measurable_ofReal.comp` to reduce the goal to its premises. Conclude with `((measurable_const.add measurable_norm).pow_const s).inv`. Establish `hg : AEMeasurable g μ`.

Apply `Measurable.aemeasurable` to reduce the goal to its premises. Apply `ENNReal.measurable_ofReal.comp` to reduce the goal to its premises. Apply `Continuous.measurable` to reduce the goal to its premises. Use `fun_prop`. Establish `key` using `ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg`.

Establish `h1 : ∀ z, (f * g) z = ENNReal.ofReal (‖z‖ ^ k * ‖H z‖)`. Introduce `z`. Establish `hp : 0 < (1 + ‖z‖) ^ s` using `by positivity`. Simplify using `only [Pi.mul_apply, f, g]`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]`.

Establish `h2 : ∀ z, f z ^ (2 : ℝ) = ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ)))`. Introduce `z`. Simplify using `only [f]`. Rewrite using `[ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]`. Use `congr 1`.

Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, inv_pow, ← pow_mul, mul_comm]`. Establish `h3 : ∀ z, g z ^ (2 : ℝ) ≤ B * (ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) + ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2))`. Introduce `z`. Simplify using `only [g, hB]`. Rewrite using `[ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `h` using `add_pow_le (zero_le_one) (norm_nonneg z) (2 * s)`. Rewrite using `[Real.rpow_two, add_assoc, ← hs]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [h1, h2] at key`.

Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[← hA, mul_assoc, ← ENNReal.mul_rpow_of_nonneg B _ (by norm_num)]`. Use `mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num))` and prove the remaining obligations. Establish `hm : Measurable fun z : E => ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2)`. Apply `ENNReal.measurable_ofReal.comp` to reduce the goal to its premises.

Apply `Continuous.measurable` to reduce the goal to its premises. Use `fun_prop`. Rewrite using `[← lintegral_add_left hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Conclude with `lintegral_mono h3`.
-/
theorem lintegral_norm_pow_mul_le_sqrt_weighted_sq :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  intro E F _ _ _ _ _ μ _ _
  set s : ℕ := finrank ℝ E + 1 with hs
  have hfin : ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ < ∞ := by
    apply finite_integral_one_add_norm
    rw [hs]; push_cast
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    linarith
  set A := ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ with hA
  set B : ℝ≥0∞ := ENNReal.ofReal (2 ^ (2 * s - 1)) with hB
  refine ⟨A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  intro H hH k
  let f : E → ℝ≥0∞ := fun z => ENNReal.ofReal (((1 + ‖z‖) ^ s)⁻¹)
  let g : E → ℝ≥0∞ := fun z => ENNReal.ofReal ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖))
  have hf : AEMeasurable f μ := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    exact ((measurable_const.add measurable_norm).pow_const s).inv
  have hg : AEMeasurable g μ := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have h1 : ∀ z, (f * g) z = ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) := by
    intro z
    have hp : 0 < (1 + ‖z‖) ^ s := by positivity
    simp only [Pi.mul_apply, f, g]
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  have h2 : ∀ z, f z ^ (2 : ℝ) = ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) := by
    intro z
    simp only [f]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, inv_pow, ← pow_mul,
      mul_comm]
  have h3 : ∀ z, g z ^ (2 : ℝ) ≤ B * (ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) +
      ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2)) := by
    intro z
    simp only [g, hB]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h := add_pow_le (zero_le_one) (norm_nonneg z) (2 * s)
    rw [Real.rpow_two, add_assoc, ← hs]
    calc ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖)) ^ 2
        = (1 + ‖z‖) ^ (2 * s) * (‖z‖ ^ k * ‖H z‖) ^ 2 := by ring
      _ ≤ (2 ^ (2 * s - 1) * (1 ^ (2 * s) + ‖z‖ ^ (2 * s))) * (‖z‖ ^ k * ‖H z‖) ^ 2 := by
        gcongr
      _ = _ := by rw [one_pow]; ring
  simp only [h1, h2] at key
  refine key.trans ?_
  rw [← hA, mul_assoc, ← ENNReal.mul_rpow_of_nonneg B _ (by norm_num)]
  refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num))
  have hm : Measurable fun z : E => ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  rw [← lintegral_add_left hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono h3

end GlobalTheory
