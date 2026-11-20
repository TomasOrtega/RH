import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeil
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
open GlobalTheory.SnFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGenericFamilyStepOfSiegelWeil.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.genericFamilyStep_of_siegelWeil : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFamTop.stepFamG_of_SWXS | exact GlobalTheory.SnFamTop.stepFamG_of_SWXS | (intros; apply GlobalTheory.SnFamTop.stepFamG_of_SWXS <;> assumption)
