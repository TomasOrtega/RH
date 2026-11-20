import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetLemmaHolds.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.jacquet_lemma_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 | exact GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 | (intros; apply GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 <;> assumption)
