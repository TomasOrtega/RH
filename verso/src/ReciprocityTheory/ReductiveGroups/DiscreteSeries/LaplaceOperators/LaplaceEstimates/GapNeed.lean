import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Introduce `k r ε h hp hq hg`. Unfold `StepGap at hg`. Unfold `hNeed S7.q0`. Take `⟨h1, h2⟩` from `hg`. Rewrite `h2`, the goal using `[← Nat.cast_min]`.

Establish `hqr : ((qOf ε : ℕ) : ℝ) - 1 = (r : ℝ)` using `by rw [hq]; push_cast; ring`. Rewrite using `[hqr]`. Establish `hm : 1 ≤ min (pOf ε) (qOf ε)`. Assume the negation of the conclusion as `hc`. Establish `h0 : min (pOf ε) (qOf ε) = 0` using `by omega`.

Rewrite `h2` using `[h0]`. Simplify using `at h2`. Combine the linear relations using `[le_max_left (0 : ℝ) (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2)]`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Use `set m := min (pOf ε) (qOf ε) with hmdef`.

Use `set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hN`. Establish `hN1 : (1 : ℝ) ≤ N` using `by rw [hN]; norm_cast; omega`. Establish `hm1 : (1 : ℝ) ≤ (m : ℝ)` using `by exact_mod_cast hm`. Establish `hsq : 1 ≤ Real.sqrt (2 * (m : ℝ))` using `Real.one_le_sqrt.mpr (by linarith)`. Use `set s := 8 * Real.sqrt (2 * (m : ℝ)) with hs`.

Establish `hs8 : 8 ≤ s` using `by rw [hs]; linarith`. Establish `hspos : 0 < s` using `by linarith`. Use `set X := max (2 * N * (m : ℝ)) (2 * (r : ℝ) * N ^ 2) with hX`. Establish `hX1 : 2 * N * m ≤ X` using `le_max_left _ _`. Establish `hNm : 1 ≤ N * m` using `by nlinarith`.

Establish `hC : s * (4 * X + 1) < h`. Establish `h4` using `h2`. Rewrite `h4` using `[lt_sub_iff_add_lt, lt_div_iff₀ hspos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsX : 8 * X ≤ s * X` using `by nlinarith`.

Use `max_lt (by linarith) (max_lt ?_ hC)` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gapNeed : GapNeedStatement := by
  intro k r ε h hp hq hg
  unfold StepGap at hg
  unfold hNeed S7.q0
  obtain ⟨h1, h2⟩ := hg
  rw [← Nat.cast_min] at h2 ⊢
  have hqr : ((qOf ε : ℕ) : ℝ) - 1 = (r : ℝ) := by rw [hq]; push_cast; ring
  rw [hqr]
  have hm : 1 ≤ min (pOf ε) (qOf ε) := by
    by_contra hc
    have h0 : min (pOf ε) (qOf ε) = 0 := by omega
    rw [h0] at h2
    simp at h2
    linarith [le_max_left (0 : ℝ) (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2)]
  refine ⟨hm, ?_⟩
  set m := min (pOf ε) (qOf ε) with hmdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; norm_cast; omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsq : 1 ≤ Real.sqrt (2 * (m : ℝ)) := Real.one_le_sqrt.mpr (by linarith)
  set s := 8 * Real.sqrt (2 * (m : ℝ)) with hs
  have hs8 : 8 ≤ s := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  set X := max (2 * N * (m : ℝ)) (2 * (r : ℝ) * N ^ 2) with hX
  have hX1 : 2 * N * m ≤ X := le_max_left _ _
  have hNm : 1 ≤ N * m := by nlinarith
  have hC : s * (4 * X + 1) < h := by
    have h4 := h2
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hspos] at h4
    linarith
  have hsX : 8 * X ≤ s * X := by nlinarith
  refine max_lt (by linarith) (max_lt ?_ hC)
  nlinarith

end ReciprocityTheory.ChartRestriction.DS.Lap
