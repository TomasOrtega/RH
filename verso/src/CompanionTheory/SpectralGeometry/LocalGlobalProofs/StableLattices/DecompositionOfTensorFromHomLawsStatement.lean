import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLaws
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZuckDecTens.decTens` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FDecompositionOfTensorFromHomLaws.lean&line=134#L134)
-/
theorem _root_.GlobalTheory.T.decomposition_of_tensor_from_hom_laws : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecTens.decTens | exact GlobalTheory.CompanionTheory.ZuckDecTens.decTens | (intros; apply GlobalTheory.CompanionTheory.ZuckDecTens.decTens <;> assumption)
