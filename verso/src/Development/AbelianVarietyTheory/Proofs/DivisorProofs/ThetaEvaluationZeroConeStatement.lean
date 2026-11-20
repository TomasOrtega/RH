import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroCone
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaEvaluationZeroCone.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.theta_evaluation_zero_cone : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.EvZero ∧ GlobalTheory.ThK.EvCone := by
  first | exact @GlobalTheory.ThK.EvMaps.evZero_evCone | exact GlobalTheory.ThK.EvMaps.evZero_evCone | (intros; apply GlobalTheory.ThK.EvMaps.evZero_evCone <;> assumption)
