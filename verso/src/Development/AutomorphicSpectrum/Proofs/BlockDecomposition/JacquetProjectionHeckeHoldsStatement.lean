import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetProjectionHeckeHolds.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.jacquet_projection_hecke_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A2 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | exact GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | (intros; apply GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines <;> assumption)
