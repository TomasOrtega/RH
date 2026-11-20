import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContraction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DomUnitary.domU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDominantUnipotentContraction.lean&line=133#L133)
-/
theorem _root_.GlobalTheory.T.dominant_unipotent_contraction : PositivityTheory.SphericalProduct.DomU := by
  first | exact @GlobalTheory.CompanionTheory.DomUnitary.domU | exact GlobalTheory.CompanionTheory.DomUnitary.domU | (intros; apply GlobalTheory.CompanionTheory.DomUnitary.domU <;> assumption)
