import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZuckTensHom.tensHom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FSnTens2.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.tensHom' : TensHom := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTensHom.tensHom | exact GlobalTheory.CompanionTheory.ZuckTensHom.tensHom | (intros; apply GlobalTheory.CompanionTheory.ZuckTensHom.tensHom <;> assumption)
