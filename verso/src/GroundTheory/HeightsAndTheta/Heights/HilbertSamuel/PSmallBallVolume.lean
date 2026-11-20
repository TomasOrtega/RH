import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Real Module
open scoped Nat

noncomputable section

/- English proof (translation)
Establish `hπ` using `pi_lt_d2`. Establish `hπ0` using `pi_pos`. Establish `step : ∀ k, 3 ≤ k → π ^ (k + 1) / ((k + 1) ! : ℝ) ≤ π ^ k / (k ! : ℝ)`. Introduce `k hk`. Establish `hk' : (4 : ℝ) ≤ (k : ℝ) + 1`.

Establish `: (3 : ℝ) ≤ k` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Nat.factorial_succ, Nat.cast_mul, pow_succ]`. Establish `hf : (0 : ℝ) < (k ! : ℝ)` using `by exact_mod_cast Nat.factorial_pos k`. Rewrite using `[div_le_div_iff₀ (by positivity) hf]`.

Use `push_cast`. Establish `hp : 0 < π ^ k` using `pow_pos hπ0 k`. Use polynomial arithmetic with `[mul_pos hp hf]`. Establish `h3 : π ^ 3 / ((3 : ℕ) ! : ℝ) ≤ 6`. Evaluate the numerical expressions using `[Nat.factorial]`.

Use polynomial arithmetic with `[sq_nonneg π, mul_pos hπ0 hπ0]`. Break down `lt_or_ge k 3 with hk | hk` into its components or cases. Use `interval_cases k`. Evaluate the numerical expressions. Evaluate the numerical expressions.

Combine the linear equalities and inequalities to obtain the conclusion. Evaluate the numerical expressions using `[Nat.factorial]`. Use the polynomial consequences of the given equalities and inequalities. Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => exact h3`.

Consider the case `succ n hn ih => exact (step n hn).trans ih`.
-/
theorem pi_pow_div_factorial_le_six (k : ℕ) : π ^ k / (k ! : ℝ) ≤ 6 := by
  have hπ := pi_lt_d2
  have hπ0 := pi_pos
  have step : ∀ k, 3 ≤ k → π ^ (k + 1) / ((k + 1) ! : ℝ) ≤ π ^ k / (k ! : ℝ) := by
    intro k hk
    have hk' : (4 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_div_iff₀ (by positivity) hf]
    push_cast
    have hp : 0 < π ^ k := pow_pos hπ0 k
    nlinarith [mul_pos hp hf]
  have h3 : π ^ 3 / ((3 : ℕ) ! : ℝ) ≤ 6 := by
    norm_num [Nat.factorial]
    nlinarith [sq_nonneg π, mul_pos hπ0 hπ0]
  rcases lt_or_ge k 3 with hk | hk
  · interval_cases k
    · norm_num
    · norm_num; linarith
    · norm_num [Nat.factorial]; nlinarith
  · induction k, hk using Nat.le_induction with
    | base => exact h3
    | succ n hn ih => exact (step n hn).trans ih

/- English proof (translation)
Establish `hπ` using `pi_lt_d2`. Establish `hπ0` using `pi_pos`. Establish `step : ∀ k, 2 ≤ k → π ^ (k + 1) * 2 ^ (k + 1 + 1) / ((2 * (k + 1) + 1)‼ : ℝ) ≤ π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ)`. Introduce `k hk`. Establish `hk' : (7 : ℝ) ≤ 2 * (k : ℝ) + 3`.

Establish `: (2 : ℝ) ≤ k` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : 2 * (k + 1) + 1 = (2 * k + 1) + 2` using `by ring`. Rewrite using `[he, Nat.doubleFactorial_add_two, Nat.cast_mul, pow_succ, pow_succ (2 : ℝ) (k + 1)]`. Establish `hf : (0 : ℝ) < ((2 * k + 1)‼ : ℝ)` using `by exact_mod_cast Nat.doubleFactorial_pos _`.

Rewrite using `[div_le_div_iff₀ (by positivity) hf]`. Use `push_cast`. Establish `hp : 0 < π ^ k * 2 ^ (k + 1)` using `by positivity`. Use polynomial arithmetic with `[mul_pos hp hf]`. Establish `h2 : π ^ 2 * 2 ^ (2 + 1) / ((2 * 2 + 1)‼ : ℝ) ≤ 6`.

Evaluate the numerical expressions using `[Nat.doubleFactorial]`. Use the polynomial consequences of the given equalities and inequalities. Break down `lt_or_ge k 2 with hk | hk` into its components or cases. Use `interval_cases k`. Evaluate the numerical expressions using `[Nat.doubleFactorial]`.

Evaluate the numerical expressions using `[Nat.doubleFactorial]`. Combine the linear equalities and inequalities to obtain the conclusion. Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => exact h2`. Consider the case `succ n hn ih => exact (step n hn).trans ih`.
-/
theorem pi_pow_mul_two_pow_div_doubleFactorial_le_six (k : ℕ) :
    π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) ≤ 6 := by
  have hπ := pi_lt_d2
  have hπ0 := pi_pos
  have step : ∀ k, 2 ≤ k → π ^ (k + 1) * 2 ^ (k + 1 + 1) / ((2 * (k + 1) + 1)‼ : ℝ) ≤
      π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) := by
    intro k hk
    have hk' : (7 : ℝ) ≤ 2 * (k : ℝ) + 3 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [he, Nat.doubleFactorial_add_two, Nat.cast_mul, pow_succ, pow_succ (2 : ℝ) (k + 1)]
    have hf : (0 : ℝ) < ((2 * k + 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
    rw [div_le_div_iff₀ (by positivity) hf]
    push_cast
    have hp : 0 < π ^ k * 2 ^ (k + 1) := by positivity
    nlinarith [mul_pos hp hf]
  have h2 : π ^ 2 * 2 ^ (2 + 1) / ((2 * 2 + 1)‼ : ℝ) ≤ 6 := by
    norm_num [Nat.doubleFactorial]
    nlinarith
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · norm_num [Nat.doubleFactorial]
    · norm_num [Nat.doubleFactorial]; linarith
  · induction k, hk using Nat.le_induction with
    | base => exact h2
    | succ n hn ih => exact (step n hn).trans ih

/- English proof (translation)
Introduce `R`. Unfold `unitBallVolume`. Establish `hfin : finrank ℝ (EuclideanSpace ℝ (Fin R)) = R` using `finrank_euclideanSpace_fin`. Break down `Nat.even_or_odd' R with ⟨k, hk | hk⟩` into its components or cases. Break down `Nat.eq_zero_or_pos k with h0 | hpos` into its components or cases.

Substitute `h0` using the available equality. Simplify using `only [mul_zero] at hk`. Substitute `hk` using the available equality. Establish `: (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal ≤ 1`. Establish `hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1) ≤ 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage MeasurableSet.univ.nullMeasurableSet, Set.preimage_univ, MeasureTheory.volume_pi, Measure.pi_univ]`. Simplify using the standard rewrite rules. Conclude with `ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: Nontrivial (EuclideanSpace ℝ (Fin R))` using `Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)`. Rewrite using `[InnerProductSpace.volume_ball_of_dim_even (hfin.trans hk), ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (by positivity)]`. Conclude with `pi_pow_div_factorial_le_six k`. Rewrite using `[InnerProductSpace.volume_ball_of_dim_odd (hfin.trans hk), ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (by positivity), hfin, hk]`. Conclude with `pi_pow_mul_two_pow_div_doubleFactorial_le_six k`.
-/
theorem SmallBallVolume.proof : SmallBallVolume.Statement := by
  intro R
  unfold unitBallVolume
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin R)) = R := finrank_euclideanSpace_fin
  rcases Nat.even_or_odd' R with ⟨k, hk | hk⟩
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp only [mul_zero] at hk
      subst hk
      have : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal ≤ 1 := by
        have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1) ≤ 1 := by
          calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)
              ≤ volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := measure_mono (Set.subset_univ _)
            _ = 1 := by
              rw [← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage
                MeasurableSet.univ.nullMeasurableSet, Set.preimage_univ, MeasureTheory.volume_pi,
                Measure.pi_univ]
              simp
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
      linarith
    · have : Nontrivial (EuclideanSpace ℝ (Fin R)) :=
        Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
      rw [InnerProductSpace.volume_ball_of_dim_even (hfin.trans hk), ENNReal.ofReal_one, one_pow,
        one_mul, ENNReal.toReal_ofReal (by positivity)]
      exact pi_pow_div_factorial_le_six k
  · rw [InnerProductSpace.volume_ball_of_dim_odd (hfin.trans hk), ENNReal.ofReal_one, one_pow,
      one_mul, ENNReal.toReal_ofReal (by positivity), hfin, hk]
    exact pi_pow_mul_two_pow_div_doubleFactorial_le_six k

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
