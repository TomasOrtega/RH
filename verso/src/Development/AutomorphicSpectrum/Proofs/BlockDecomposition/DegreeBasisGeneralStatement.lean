import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDegreeBasisGeneral.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.degree_basis_general : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  first | exact @GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | exact GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | (intros; apply GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of <;> assumption)
