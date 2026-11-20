import Formalism.SizeWindowBrackets.SlopeExcessBoundExponentZero
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedMeanLemmaNeedsDegree
import Formalism.RankGapBounds.RankGapProofs.WeightedMeanData

open Real Filter

namespace Formalism.LFunctionChainParameters.PhiMonotonicityLemmas

/- English proof (authored)
The square root of twice 1/131072 is 1/256. Substituting the parameters makes the error equal to (8/7)(4 log(33) + 6). Since 33 ≤ 64, log(33) ≤ 6 log(2). The bound log(2) < 7/10 follows because the first four terms of the exponential series at 7/10 already sum to more than 2. Hence one plus the error is less than 947/35, which is below 32.
-/
theorem corollary_model_side_condition :
    (0 + 1 + ErrF (1 / 8) 1 32 (5 * (1 / 32) + 3 * (1 / 192)) (2 * (1 / 131072))) - 0 ≤ (32 : ℝ) := by
  have hs2 : Real.sqrt (2 * (1 / 131072)) = 1 / 256 := by
    rw [show (2 * (1 / 131072) : ℝ) = (1 / 256) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hl : Real.log (1 + 32 / 1) ≤ 6 * Real.log 2 := by
    rw [show (6 : ℝ) * Real.log 2 = Real.log (2 ^ 6) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9
  unfold ErrF phi
  rw [hs2]
  norm_num at hl ⊢
  linarith

/- English proof (authored)
Take μ = 0, the logarithmic term equal to 1, deletion parameter 1/8, both size parameters equal to 1, and height 32. Take x = 2, c = 5 and b = 1, so the height bound is an equality. Use e₀ = 1/131072, e = 2e₀, d = 1/36864 and C₁ = 3. The two square roots are 1/192 and 1/256, and their weighted contributions add to 1/32, which is the reciprocal of 2 to the power five. Set η to 5/32 + 3/192. These values satisfy the positivity and size conditions. Taking s equal to 1 plus the resulting error gives the final equality, while the preceding numerical bound gives s ≤ 32.
-/
theorem corollary_final_model : CorFinalModel := by
  have hp : (2 : ℝ) ^ (5 : ℝ) = 32 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hn : (2 : ℝ) ^ (-(5 : ℝ)) = 1 / 32 := by
    rw [Real.rpow_neg (by norm_num), hp]; norm_num
  have hs1 : Real.sqrt (1 / 36864) = 1 / 192 := by
    rw [show (1 / 36864 : ℝ) = (1 / 192) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hs2 : Real.sqrt (2 * (1 / 131072)) = 1 / 256 := by
    rw [show (2 * (1 / 131072) : ℝ) = (1 / 256) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨0 + 1 + ErrF (1 / 8) 1 32 (5 * (1 / 32) + 3 * (1 / 192)) (2 * (1 / 131072)), 0, 1, 1 / 8,
    1, 1, 32, 5 * (1 / 32) + 3 * (1 / 192), 2 * (1 / 131072), 1 / 131072, 1 / 36864, 3, 1, 2, 5,
    le_refl _, by norm_num, by norm_num, by norm_num, ?_, by norm_num, le_refl _, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, rfl, by norm_num, ?_, by norm_num,
    corollary_model_side_condition, by ring⟩
  · rw [hp]; norm_num
  · rw [hn]; norm_num
  · rw [hn, hs1]
  · rw [hn, hs1, hs2]; norm_num

section SizeData₂

open Formalism.RankGapBounds.WeightedMeanData

end SizeData₂

end Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
