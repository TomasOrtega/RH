import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecomposition
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.ChamberInd.chamberU | exact GlobalTheory.CompanionTheory.ChamberInd.chamberU | (intros; apply GlobalTheory.CompanionTheory.ChamberInd.chamberU <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unitary_chamber_decomposition : PositivityTheory.SphericalProduct.ChamberU := by
  first | exact @GlobalTheory.CompanionTheory.ChamberInd.chamberU | exact GlobalTheory.CompanionTheory.ChamberInd.chamberU | (intros; apply GlobalTheory.CompanionTheory.ChamberInd.chamberU <;> assumption)
