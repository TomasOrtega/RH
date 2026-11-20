import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | exact GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | (intros; apply GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  first | exact @GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | exact GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | (intros; apply GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude <;> assumption)
