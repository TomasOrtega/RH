import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantPowLeHaarWeight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
open NumberField Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGramInvariantPowLeHaarWeight.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.T.gram_invariant_pow_le_haar_weight : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (r k TT : ℕ) (rd H : ℝ) (γ : PN.Pts E r), 0 < rd → (∀ a, 1 ≤ ∏ v : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2) → NDPt rd γ ≤ H → NGPt rd TT γ ^ (k - 1) ≤ H ^ (6 * (2 * r + 2)) * nPt rd k TT γ := by
  first | exact @GlobalTheory.HaarWeight.gram_pow_le_haar | exact GlobalTheory.HaarWeight.gram_pow_le_haar | (intros; apply GlobalTheory.HaarWeight.gram_pow_le_haar <;> assumption)
