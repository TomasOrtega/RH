import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuity
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FArchimedeanFamilyContinuity.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.archimedean_family_continuity : PositivityTheory.PfSWUS.SchInf.FamCont := by
  first | exact @GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | exact GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | (intros; apply GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push <;> assumption)
