import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

/- English proof (translation)
Unfold `ArithVariety.IsLive at hc`. Use `push Not at hc`. Take `⟨k, hk⟩` from `hc`. Unfold `chartMonomial`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]`.

Conclude with `P.ideal.mul_mem_right _ (P.ideal.pow_mem_of_mem hk _ (hd k))`.
-/
theorem ArithVariety.chartMonomial_mem_of_not_isLive (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  unfold ArithVariety.IsLive at hc
  push Not at hc
  obtain ⟨k, hk⟩ := hc
  unfold chartMonomial
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  exact P.ideal.mul_mem_right _ (P.ideal.pow_mem_of_mem hk _ (hd k))

/- English proof (translation)
Introduce `ι _ _ n P D d g hg c c' j`. Distinguish the cases in `hc : P.IsLive c`. Distinguish the cases in `hc' : P.IsLive c'`. Rewrite using `[← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc, hg.value c' hc']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hg.dead c' hc', mul_zero, sub_zero]`. Conclude with `P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc' hg.pos)`. Rewrite using `[hg.dead c hc, mul_zero, zero_sub]`. Conclude with `P.ideal.neg_mem_iff.mpr (P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc hg.pos))`.
-/
theorem ChartCrossRatio.proof : ChartCrossRatio.Statement := by
  intro ι _ _ n P D d g hg c c' j
  by_cases hc : P.IsLive c
  · by_cases hc' : P.IsLive c'
    · rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc, hg.value c' hc']
      ring
    · rw [hg.dead c' hc', mul_zero, sub_zero]
      exact P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc' hg.pos)
  · rw [hg.dead c hc, mul_zero, zero_sub]
    exact P.ideal.neg_mem_iff.mpr
      (P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc hg.pos))

end GroundTheory.Heights₂.Heights
