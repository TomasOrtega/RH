import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyStepOfFourGlobalLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.stepFamC_of_globalLeaves` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFamilyStepOfFourGlobalLeaves.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.familyStep_of_four_globalLeaves : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric → Formalism.L2.SG.FamDefs.ExistNG → Formalism.L2.SG.NGLocModel.StepFamC := by
  first | exact @GlobalTheory.stepFamC_of_globalLeaves | exact GlobalTheory.stepFamC_of_globalLeaves | (intros; apply GlobalTheory.stepFamC_of_globalLeaves <;> assumption)
