import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SplitPlace.splitDict | exact GlobalTheory.CompanionTheory.SplitPlace.splitDict | (intros; apply GlobalTheory.CompanionTheory.SplitPlace.splitDict <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.split_dictionary_holds : SplitDict := by
  first | exact @GlobalTheory.CompanionTheory.SplitPlace.splitDict | exact GlobalTheory.CompanionTheory.SplitPlace.splitDict | (intros; apply GlobalTheory.CompanionTheory.SplitPlace.splitDict <;> assumption)
