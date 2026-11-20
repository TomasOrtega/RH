import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationInequalityAbelian
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRelationInequalityAbelian.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.relation_inequality_abelian : RelIneAb := by
  first | exact @GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb | exact GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb | (intros; apply GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb <;> assumption)
