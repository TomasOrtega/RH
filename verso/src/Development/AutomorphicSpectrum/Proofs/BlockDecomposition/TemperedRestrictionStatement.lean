import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedRestriction
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTemperedRestriction.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.tempered_restriction : TempRes := by
  first | exact @GlobalTheory.CompanionTheory.TempRes.tempRes | exact GlobalTheory.CompanionTheory.TempRes.tempRes | (intros; apply GlobalTheory.CompanionTheory.TempRes.tempRes <;> assumption)
