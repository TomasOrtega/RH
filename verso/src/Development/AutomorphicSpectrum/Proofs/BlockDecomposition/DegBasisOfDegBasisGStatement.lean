import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisG
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDegBasisOfDegBasisG.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.degBasis_of_degBasisG' : DegBasisG → DegBasis := by
  first | exact @GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG | exact GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG | (intros; apply GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG <;> assumption)
