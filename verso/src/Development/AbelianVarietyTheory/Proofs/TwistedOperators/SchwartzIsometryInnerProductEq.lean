import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Complex.sq_norm]`. Apply the tactic sequence `apply Complex.ext <;>`. Apply the tactic sequence `simp [Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring`.
-/
theorem complex_mul_conj_eq_polarization (a b : ℂ) :
    a * starRingEnd ℂ b = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * ((‖a + Complex.I ^ k * b‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Complex.sq_norm]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

/- English proof (translation)
Use `(h.memLp 2 μ).integrable_norm_pow (by norm_num)` as an intermediate fact. Simplify using `using this`.
-/
theorem schwartz_integrable_sq_norm_of_addHaar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (h : SchwartzMap V ℂ) :
    Integrable (fun x => ‖h x‖ ^ 2) μ := by
  have := (h.memLp 2 μ).integrable_norm_pow (by norm_num)
  simpa using this

/- English proof (translation)
Repeatedly rewrite using `[complex_mul_conj_eq_polarization (u _)]`. Rewrite using `[integral_const_mul, integral_finset_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul]`.

Use `congr 1`. Rewrite using `[← integral_complex_ofReal]`. Simplify using `[smul_eq_mul]`. Introduce `k _`. Use `Integrable.const_mul ?_ _` and prove the remaining obligations.

Use `(schwartz_integrable_sq_norm_of_addHaar μ (u + (Complex.I ^ k) • v)).ofReal (𝕜 := ℂ)` as an intermediate fact. Simplify using `using this`.
-/
theorem schwartz_integral_mul_conj_eq_polarization {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (u v : SchwartzMap V ℂ) :
    ∫ x, u x * starRingEnd ℂ (v x) ∂μ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * ((∫ x, ‖(u + (Complex.I ^ k) • v) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp_rw [complex_mul_conj_eq_polarization (u _)]
  rw [integral_const_mul, integral_finset_sum]
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [← integral_complex_ofReal]
    simp [smul_eq_mul]
  · intro k _
    refine Integrable.const_mul ?_ _
    have := (schwartz_integrable_sq_norm_of_addHaar μ (u + (Complex.I ^ k) • v)).ofReal (𝕜 := ℂ)
    simpa using this

/- English proof (translation)
Introduce `hT f g`. Rewrite using `[schwartz_integral_mul_conj_eq_polarization, schwartz_integral_mul_conj_eq_polarization]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← map_smul, ← map_add, hT]`.
-/
theorem schwartz_L2_isometry_preserves_inner {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ) :
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  intro hT f g
  rw [schwartz_integral_mul_conj_eq_polarization, schwartz_integral_mul_conj_eq_polarization]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul, ← map_add, hT]

end GlobalTheory
