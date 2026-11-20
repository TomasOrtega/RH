import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPiMulWeightLengthLeMaxWeightDegreeSq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OrientationExclusive
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwoPiMulWeightLengthLeMaxWeightDegreeSq.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.two_pi_mul_weightLength_le_maxWeightDegree_sq : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 2 * Real.pi * (Tp.nWn : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) ^ 2 := by
  first | exact @GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq | exact GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq | (intros; apply GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq <;> assumption)
