import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceOfSubgroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ExSubLeaf.exSub` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistenceOfSubgroup.lean&line=245#L245)
-/
theorem _root_.GlobalTheory.T.existence_of_subgroup : ExSub := by
  first | exact @GlobalTheory.CompanionTheory.ExSubLeaf.exSub | exact GlobalTheory.CompanionTheory.ExSubLeaf.exSub | (intros; apply GlobalTheory.CompanionTheory.ExSubLeaf.exSub <;> assumption)
