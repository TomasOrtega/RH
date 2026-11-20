import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.IwUnit.iwahoriU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIwahoriUnipotentDatum.lean&line=289#L289)
-/
theorem _root_.GlobalTheory.T.iwahori_unipotent_datum : PositivityTheory.SphericalProduct.IwahoriU := by
  first | exact @GlobalTheory.CompanionTheory.IwUnit.iwahoriU | exact GlobalTheory.CompanionTheory.IwUnit.iwahoriU | (intros; apply GlobalTheory.CompanionTheory.IwUnit.iwahoriU <;> assumption)
