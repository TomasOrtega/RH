import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmQuadraticAdjoinSqrtNegNat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsCmQuadraticAdjoinSqrtNegNat.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_cmQuadratic_adjoin_sqrt_neg_nat : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) → ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  first | exact @GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg | exact GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg | (intros; apply GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg <;> assumption)
