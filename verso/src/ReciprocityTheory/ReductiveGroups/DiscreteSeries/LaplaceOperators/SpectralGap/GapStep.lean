import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapLapStepGapStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Introduce `n ε lam h hp hq hG`. Take `⟨-, -, hN⟩` from `hG`. Unfold `hNeed at hN`. Establish `h1` using `lt_of_le_of_lt (le_max_left _ _) hN`. Establish `h3` using `lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN`.

Establish `hcast : (((qOf ε - 1 : ℕ) : ℕ) : ℝ) = (qOf ε : ℝ) - 1`. Rewrite using `[Nat.cast_sub hq, Nat.cast_one]`. Establish `hm : (1 : ℝ) ≤ (min (pOf ε) (qOf ε) : ℕ)`. Conclude with `le_min hp hq` after adjusting the coercions. Establish `hs : 0 < Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℕ) : ℝ)` using `Real.sqrt_pos.mpr (by linarith)`.

Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Rewrite using `[hcast, lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gapLap_stepGap : GapLapStepGapStatement := by
  intro n ε lam h hp hq hG
  obtain ⟨-, -, hN⟩ := hG
  unfold hNeed at hN
  have h1 := lt_of_le_of_lt (le_max_left _ _) hN
  have h3 := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hcast : (((qOf ε - 1 : ℕ) : ℕ) : ℝ) = (qOf ε : ℝ) - 1 := by
    rw [Nat.cast_sub hq, Nat.cast_one]
  have hm : (1 : ℝ) ≤ (min (pOf ε) (qOf ε) : ℕ) := by
    exact_mod_cast le_min hp hq
  have hs : 0 < Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨by linarith, ?_⟩
  rw [hcast, lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
  linarith
