import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FQuotientMeasureRightInvariant.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.quotientMeasure_right_invariant : PI.QuotInv := by
  first | exact @GlobalTheory.QuotRightInv.quotInv | exact GlobalTheory.QuotRightInv.quotInv | (intros; apply GlobalTheory.QuotRightInv.quotInv <;> assumption)
