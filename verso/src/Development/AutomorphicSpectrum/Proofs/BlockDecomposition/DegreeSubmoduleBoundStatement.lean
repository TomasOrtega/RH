import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDegreeSubmoduleBound.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.degree_submodule_bound : WedgeF → WedgeI → WedgeSub → FinSupp → DegBasisG → TwoBases → DegSubmod := by
  first | exact @GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | exact GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | (intros; apply GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of <;> assumption)
