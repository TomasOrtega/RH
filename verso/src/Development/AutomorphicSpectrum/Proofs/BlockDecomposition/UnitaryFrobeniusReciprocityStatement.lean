import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocity
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FrobRec.frobU | exact GlobalTheory.CompanionTheory.FrobRec.frobU | (intros; apply GlobalTheory.CompanionTheory.FrobRec.frobU <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unitary_frobenius_reciprocity : PositivityTheory.SphericalProduct.FrobU := by
  first | exact @GlobalTheory.CompanionTheory.FrobRec.frobU | exact GlobalTheory.CompanionTheory.FrobRec.frobU | (intros; apply GlobalTheory.CompanionTheory.FrobRec.frobU <;> assumption)
