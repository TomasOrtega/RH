import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDegreeRationalSubspace.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.degree_rational_subspace : DegBasisG → DegRat := by
  first | exact @GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG | exact GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG | (intros; apply GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG <;> assumption)
