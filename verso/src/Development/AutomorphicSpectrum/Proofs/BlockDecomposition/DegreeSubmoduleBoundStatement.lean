import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | exact GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | (intros; apply GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.degree_submodule_bound : WedgeF → WedgeI → WedgeSub → FinSupp → DegBasisG → TwoBases → DegSubmod := by
  first | exact @GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | exact GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | (intros; apply GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of <;> assumption)
