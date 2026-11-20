import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensity
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | exact GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.schwartz_tensor_density : SchwTensor := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | exact GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor <;> assumption)
