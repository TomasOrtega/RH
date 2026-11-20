import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSum
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.CasimirScalarOfCapelliDeterminantEigenvalueImpor
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CasimirDS.casDS` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FCasimirDiagonalSum.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.CasimirDiagonalSum : CasDS := by
  first | exact @GlobalTheory.CompanionTheory.CasimirDS.casDS | exact GlobalTheory.CompanionTheory.CasimirDS.casDS | (intros; apply GlobalTheory.CompanionTheory.CasimirDS.casDS <;> assumption)
