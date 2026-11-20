import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeronese
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPointHeightFS
import ReciprocityTheory.GeometryOfNumbers.AsymptoticSequences.ClosingHS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

/- English proof (translation)
Simplify using `[chiP, monoNormSq, Finset.Nat.antidiagonalTuple_one]`.
-/
theorem chiP_zero_dim (n : ℕ) : chiP 0 n = 0 := by
  simp [chiP, monoNormSq, Finset.Nat.antidiagonalTuple_one]

/- English proof (translation)
Introduce `D I hI`. Break down `Nat.eq_zero_or_pos D with rfl | hD` into its components or cases. Establish `hh` using `h0 I hI`. Use `(isLittleO_zero (fun n : ℕ => (n : ℝ) ^ (0 + 1)) atTop).congr' ?_ EventuallyEq.rfl` and prove the remaining obligations. Use `Eventually.of_forall fun n => ?_` and prove the remaining obligations.

Simplify using `[hsDefect, hh, chiP_zero_dim]`. Take `⟨Ω, _, _, κ, _, d, hchi, htop, hdeg⟩` from `hV D hD`. Establish `h2` using `(hR D Ω κ I d hI).2`. Establish `hfun : resChi d = fun m => chiP D (2 * m)` using `funext hchi`. Rewrite `h2` using `[hfun, htop I hI, hdeg]`.

Move the coercions through the operations in `at h2`. Conclude with `hilbertSamuelDefect_projectiveSpace_isLittleO D (hhOf I D) h2`.
-/
theorem HilbertSamuelProjective.proof (hR : ReductionToProjective.Statement) (hV : SecondVeronese.Statement)
    (h0 : PointHeightFS.Statement) : HilbertSamuelProjective.Statement := by
  intro D I hI
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hh := h0 I hI
    refine (isLittleO_zero (fun n : ℕ => (n : ℝ) ^ (0 + 1)) atTop).congr' ?_ EventuallyEq.rfl
    refine Eventually.of_forall fun n => ?_
    simp [hsDefect, hh, chiP_zero_dim]
  · obtain ⟨Ω, _, _, κ, _, d, hchi, htop, hdeg⟩ := hV D hD
    have h2 := (hR D Ω κ I d hI).2
    have hfun : resChi d = fun m => chiP D (2 * m) := funext hchi
    rw [hfun, htop I hI, hdeg] at h2
    push_cast at h2
    exact hilbertSamuelDefect_projectiveSpace_isLittleO D (hhOf I D) h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
