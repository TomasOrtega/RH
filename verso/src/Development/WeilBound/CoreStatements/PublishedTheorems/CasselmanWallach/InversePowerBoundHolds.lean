import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace InversePowerBound

/- English proof (translation)
Establish `h1 : 0 < 1 + y` using `by linarith`. Establish `hpos : 0 < (1 + y) ^ s` using `pow_pos h1 s`. Establish `hA : 1 - (s : ℝ) * y / 2 ≤ Real.exp (-((s : ℝ) * y / 2))`. Combine the linear relations using `[Real.add_one_le_exp (-((s : ℝ) * y / 2))]`. Establish `hB : (1 + y) ^ s ≤ Real.exp ((s : ℝ) * y)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hC : (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
lemma sq_le_inv_pow (s : ℕ) (y : ℝ) (hy : -1 < y) (h0 : 0 ≤ 1 - (s : ℝ) * y / 2) :
    (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((1 + y) ^ s)⁻¹ := by
  have h1 : 0 < 1 + y := by linarith
  have hpos : 0 < (1 + y) ^ s := pow_pos h1 s

  have hA : 1 - (s : ℝ) * y / 2 ≤ Real.exp (-((s : ℝ) * y / 2)) := by
    linarith [Real.add_one_le_exp (-((s : ℝ) * y / 2))]
  have hB : (1 + y) ^ s ≤ Real.exp ((s : ℝ) * y) := by
    calc (1 + y) ^ s ≤ (Real.exp y) ^ s :=
          pow_le_pow_left₀ h1.le (by linarith [Real.add_one_le_exp y]) s
      _ = Real.exp ((s : ℝ) * y) := by rw [← Real.exp_nat_mul]
  have hC : (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y)) := by
    calc (1 - (s : ℝ) * y / 2) ^ 2 ≤ (Real.exp (-((s : ℝ) * y / 2))) ^ 2 :=
          pow_le_pow_left₀ h0 hA 2
      _ = Real.exp (-((s : ℝ) * y)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y)) := hC
    _ = (Real.exp ((s : ℝ) * y))⁻¹ := by rw [Real.exp_neg]
    _ ≤ ((1 + y) ^ s)⁻¹ := inv_anti₀ hpos hB

end InversePowerBound

/- English proof (translation)
Introduce `s _hs`. Use `⟨(s : ℝ) ^ 4 / 16, by positivity, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hpos : 0 < ((1 + y) ^ s)⁻¹` using `inv_pos.mpr (pow_pos (by linarith) s)`. Establish `hsq : 1 - (s : ℝ) * y + (s : ℝ) ^ 2 / 4 * y ^ 2 = (1 - (s : ℝ) * y / 2) ^ 2` using `by ring`. Establish `e : (s : ℝ) ^ 4 / 16 * y ^ 4 = ((s : ℝ) * y / 2) ^ 4` using `by ring`.

Distinguish the cases in `h0 : 0 ≤ 1 - (s : ℝ) * y / 2`. Establish `h` using `InversePowerBound.sq_le_inv_pow s y hy h0`. Establish `: 0 ≤ (s : ℝ) ^ 4 / 16 * y ^ 4` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h0` using `[not_le]`.

Establish `hu : 1 < (s : ℝ) * y / 2` using `by linarith`. Establish `k1 : (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 2` using `by nlinarith`. Establish `k2 : ((s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 4`. Establish `: 1 ≤ ((s : ℝ) * y / 2) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inverse_power_bound_holds : A10 := by
  intro s _hs
  refine ⟨(s : ℝ) ^ 4 / 16, by positivity, fun y hy => ?_⟩
  have hpos : 0 < ((1 + y) ^ s)⁻¹ := inv_pos.mpr (pow_pos (by linarith) s)

  have hsq : 1 - (s : ℝ) * y + (s : ℝ) ^ 2 / 4 * y ^ 2 = (1 - (s : ℝ) * y / 2) ^ 2 := by ring
  have e : (s : ℝ) ^ 4 / 16 * y ^ 4 = ((s : ℝ) * y / 2) ^ 4 := by ring
  by_cases h0 : 0 ≤ 1 - (s : ℝ) * y / 2
  · have h := InversePowerBound.sq_le_inv_pow s y hy h0
    have : 0 ≤ (s : ℝ) ^ 4 / 16 * y ^ 4 := by positivity
    linarith
  ·
    rw [not_le] at h0
    have hu : 1 < (s : ℝ) * y / 2 := by linarith
    have k1 : (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
    have k2 : ((s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 4 := by
      have : 1 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
      nlinarith
    linarith

end PositivityTheory.CW

end
