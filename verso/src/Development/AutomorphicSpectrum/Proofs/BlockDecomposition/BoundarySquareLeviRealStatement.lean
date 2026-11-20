import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundarySquareLeviReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KPChains.bdSqL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBoundarySquareLeviReal.lean&line=256#L256)
-/
theorem _root_.GlobalTheory.T.boundary_square_levi_real : PositivityTheory.RgBcC.RealD.BdSqL := by
  first | exact @GlobalTheory.CompanionTheory.KPChains.bdSqL | exact GlobalTheory.CompanionTheory.KPChains.bdSqL | (intros; apply GlobalTheory.CompanionTheory.KPChains.bdSqL <;> assumption)
