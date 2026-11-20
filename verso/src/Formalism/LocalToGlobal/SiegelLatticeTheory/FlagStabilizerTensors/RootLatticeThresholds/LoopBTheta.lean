import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.LoopBTheta

/- English proof (translation)
Establish `hL : 0 ≤ large₂.sc.L` using `by show 0 ≤ large₂.sc.x ^ large₂.sc.eps`. Conclude with `le_of_lt (Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _)`. Establish `hb : (1 : ℝ) ≤ large₂.sc.b` using `by show (1 : ℝ) ≤ Real.exp large₂.sc.L`. Conclude with `Real.one_le_exp hL`. Establish `hc : 0 ≤ C1 * (D.R.m : ℝ) ^ 2` using `mul_nonneg hC1 (sq_nonneg _)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hc)`. Conclude with `Real.one_le_rpow hb hc`.
-/
theorem normWin_one {D : D7} (large₂ : SizeData₂ D) {C1 : ℝ} (hC1 : 0 ≤ C1) : normWin D large₂ C1 1 := by
  have hL : 0 ≤ large₂.sc.L := by
    show 0 ≤ large₂.sc.x ^ large₂.sc.eps
    exact le_of_lt (Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _)
  have hb : (1 : ℝ) ≤ large₂.sc.b := by
    show (1 : ℝ) ≤ Real.exp large₂.sc.L
    exact Real.one_le_exp hL
  have hc : 0 ≤ C1 * (D.R.m : ℝ) ^ 2 := mul_nonneg hC1 (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hc)
  · exact Real.one_le_rpow hb hc

end Formalism.L2.SG.Pf.LoopBTheta
