import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebra
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SpecModel.specTrace | exact GlobalTheory.CompanionTheory.SpecModel.specTrace | (intros; apply GlobalTheory.CompanionTheory.SpecModel.specTrace <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.spectral_trace_of_model_algebra : UModel → LocAlg → SpecTrace := by
  first | exact @GlobalTheory.CompanionTheory.SpecModel.specTrace | exact GlobalTheory.CompanionTheory.SpecModel.specTrace | (intros; apply GlobalTheory.CompanionTheory.SpecModel.specTrace <;> assumption)
