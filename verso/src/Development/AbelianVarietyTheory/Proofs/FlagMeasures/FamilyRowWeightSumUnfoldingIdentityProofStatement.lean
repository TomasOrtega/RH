import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProof
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.familyRowWeightSumUnfoldingIdentity : GlobalTheory.SnFam.FamilyWeightSumUnfoldingIdentity := by
  first | exact @GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof | exact GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof | (intros; apply GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof <;> assumption)
