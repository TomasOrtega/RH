import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbedding
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SubEmb.subEmbedding` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSupportSubschemeEmbedding.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.support_subscheme_embedding : Ysupp.SubEmbedding := by
  first | exact @GlobalTheory.CompanionTheory.SubEmb.subEmbedding | exact GlobalTheory.CompanionTheory.SubEmb.subEmbedding | (intros; apply GlobalTheory.CompanionTheory.SubEmb.subEmbedding <;> assumption)
