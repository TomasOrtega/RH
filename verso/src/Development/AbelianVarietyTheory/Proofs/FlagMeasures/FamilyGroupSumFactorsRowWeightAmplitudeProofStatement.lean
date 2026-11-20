import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFamilyGroupSumFactorsRowWeightAmplitudeProof.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  first | exact @GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | exact GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | (intros; apply GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude <;> assumption)
