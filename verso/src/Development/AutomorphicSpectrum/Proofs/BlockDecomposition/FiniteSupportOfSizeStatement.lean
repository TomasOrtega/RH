import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteSupportOfSize.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.finite_support_of_size : MulF → MulI → SzFin → FinSupp := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul | exact GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul | (intros; apply GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul <;> assumption)
