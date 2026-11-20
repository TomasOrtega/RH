import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstProperty
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCasselmanFirstProperty.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.casselman_first_property : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A1 G := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | exact GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | (intros; apply GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract <;> assumption)
