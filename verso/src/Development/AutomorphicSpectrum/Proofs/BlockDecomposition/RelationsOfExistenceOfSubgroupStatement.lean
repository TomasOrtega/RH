import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationsOfExistenceOfSubgroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRelationsOfExistenceOfSubgroup.lean&line=293#L293)
-/
theorem _root_.GlobalTheory.T.relations_of_existence_of_subgroup : ExSub → RelOfMain := by
  first | exact @GlobalTheory.CompanionTheory.LocalParam.relOfMain_of_exSub | exact GlobalTheory.CompanionTheory.LocalParam.relOfMain_of_exSub | (intros; apply GlobalTheory.CompanionTheory.LocalParam.relOfMain_of_exSub <;> assumption)
