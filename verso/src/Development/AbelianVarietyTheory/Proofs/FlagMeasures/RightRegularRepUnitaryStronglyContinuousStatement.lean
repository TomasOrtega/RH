import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRightRegularRepUnitaryStronglyContinuous.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous : ∀ B : RowsAut, B.R 1 = 1 ∧ (∀ g h, B.R (g * h) = B.R g * B.R h) ∧ (∀ g F, ‖B.R g F‖ = ‖F‖) ∧ (∀ F, Continuous fun g => B.R g F) ∧ ∀ F : B.I.L2 B.μf B.fund, (∀ᵐ y ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, B.I.ext F (γ * y) = B.I.ext F y) ∧ AEStronglyMeasurable (B.I.ext F) (B.I.muA B.μf) := by
  first | exact @GlobalTheory.RightRegFund.rightReg_unitary_continuous | exact GlobalTheory.RightRegFund.rightReg_unitary_continuous | (intros; apply GlobalTheory.RightRegFund.rightReg_unitary_continuous <;> assumption)
