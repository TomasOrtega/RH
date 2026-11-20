import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPos
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagMeas.LProd.neg_log_prod_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNegLogProdLValEtaLeAndPos.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.neg_log_prod_lValEta_le_and_pos : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ n₀ n : ℕ, 2 ≤ n₀ → -Real.log (∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M) ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) ∧ 0 < ∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M := by
  first | exact @GlobalTheory.FlagMeas.LProd.neg_log_prod_le | exact GlobalTheory.FlagMeas.LProd.neg_log_prod_le | (intros; apply GlobalTheory.FlagMeas.LProd.neg_log_prod_le <;> assumption)
