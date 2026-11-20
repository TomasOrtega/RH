import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecomposition
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitaryChamberDecomposition.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.unitary_chamber_decomposition : PositivityTheory.SphericalProduct.ChamberU := by
  first | exact @GlobalTheory.CompanionTheory.ChamberInd.chamberU | exact GlobalTheory.CompanionTheory.ChamberInd.chamberU | (intros; apply GlobalTheory.CompanionTheory.ChamberInd.chamberU <;> assumption)
