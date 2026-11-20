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
Simplify using the standard rewrite rules.
-/
theorem chiP_zero_dim (n : ℕ) : chiP 0 n = 0 := by
  simp [chiP, monoNormSq, Finset.Nat.antidiagonalTuple_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
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
