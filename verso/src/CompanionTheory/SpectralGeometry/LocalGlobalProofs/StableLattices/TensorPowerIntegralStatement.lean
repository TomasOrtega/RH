import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FTensorPowerIntegral.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.TensorPowerIntegral : OKTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTens.okTens | exact GlobalTheory.CompanionTheory.ZuckTens.okTens | (intros; apply GlobalTheory.CompanionTheory.ZuckTens.okTens <;> assumption)
