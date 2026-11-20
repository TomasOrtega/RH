import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting

namespace ReciprocityTheory.ChartRestriction.G.FD

open Metric Set

/- English proof (translation)
Establish `h1` using `Real.exp_one_lt_d9`. Establish `h2 : |Real.exp (1 / 4) - ∑ m ∈ Finset.range 4, (1 / 4 : ℝ) ^ m / m.factorial| ≤ |(1 / 4 : ℝ)| ^ 4 * ((Nat.succ 4 : ℕ) / ((Nat.factorial 4 : ℕ) * 4))` using `Real.exp_bound (by norm_num [abs_of_pos]) (by norm_num)`. Establish `h3 : Real.exp (1 / 4) < 1.2841`. Use `(abs_le.mp h2).2` as an intermediate fact. Evaluate the numerical expressions using `[Finset.sum_range_succ, Nat.factorial] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : Real.exp (9 / 4) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4)`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Evaluate the numerical expressions. Establish `he : 0 < Real.exp 1` using `Real.exp_pos 1`.

Establish `he4 : 0 < Real.exp (1 / 4)` using `Real.exp_pos _`. Rewrite using `[h4]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma exp_nine_quarters_lt : Real.exp (9 / 4) < 9.5 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : |Real.exp (1 / 4) - ∑ m ∈ Finset.range 4, (1 / 4 : ℝ) ^ m / m.factorial| ≤
      |(1 / 4 : ℝ)| ^ 4 * ((Nat.succ 4 : ℕ) / ((Nat.factorial 4 : ℕ) * 4)) :=
    Real.exp_bound (by norm_num [abs_of_pos]) (by norm_num)
  have h3 : Real.exp (1 / 4) < 1.2841 := by
    have := (abs_le.mp h2).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have h4 : Real.exp (9 / 4) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he4 : 0 < Real.exp (1 / 4) := Real.exp_pos _
  rw [h4]
  calc Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) ≤ 2.7182818286 * 2.7182818286 * 1.2841 := by
        gcongr
    _ < 9.5 := by norm_num

/- English proof (translation)
Introduce `V _ _ γ ρ S hρ hd hb h1 h2 Z hZ`. Establish `hS : 0 < S` using `by linarith [norm_nonneg (γ 0)]`. Establish `hmaps : MapsTo γ (ball 0 ρ) (closedBall (γ 0) ((Real.exp (9 / 4) + 1) * S))`. Introduce `z hz`. Rewrite using `[mem_closedBall, dist_eq_norm]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hZρ : Z ∈ ball (0 : V) ρ` using `ball_subset_ball (by linarith) hZ`. Establish `key` using `Complex.dist_le_div_mul_dist_of_mapsTo_ball (hd.mono ball_subset_closedBall) hmaps hZρ`. Establish `hZn : ‖Z‖ < ρ / 21` using `by simpa using hZ`. Rewrite `key` using `[dist_zero_right]`.

Introduce `h0`. Rewrite `key` using `[h0, dist_comm, dist_zero_right]`. Establish `hexp` using `exp_nine_quarters_lt`. Establish `: (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ < S / 2`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem schwarzLemmaBall_holds : SchwarzLemmaBall := by
  intro V _ _ γ ρ S hρ hd hb h1 h2 Z hZ
  have hS : 0 < S := by linarith [norm_nonneg (γ 0)]
  have hmaps : MapsTo γ (ball 0 ρ) (closedBall (γ 0) ((Real.exp (9 / 4) + 1) * S)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖γ z - γ 0‖ ≤ ‖γ z‖ + ‖γ 0‖ := norm_sub_le _ _
      _ ≤ Real.exp (9 / 4) * S + S := add_le_add (hb z (ball_subset_closedBall hz)) h2
      _ = (Real.exp (9 / 4) + 1) * S := by ring
  have hZρ : Z ∈ ball (0 : V) ρ := ball_subset_ball (by linarith) hZ
  have key := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hd.mono ball_subset_closedBall) hmaps hZρ
  have hZn : ‖Z‖ < ρ / 21 := by simpa using hZ
  rw [dist_zero_right] at key
  intro h0
  rw [h0, dist_comm, dist_zero_right] at key
  have hexp := exp_nine_quarters_lt
  have : (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ < S / 2 := by
    calc (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ ≤ (Real.exp (9 / 4) + 1) * S / ρ * (ρ / 21) := by
          gcongr
      _ = (Real.exp (9 / 4) + 1) * S / 21 := by field_simp
      _ < S / 2 := by nlinarith
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
