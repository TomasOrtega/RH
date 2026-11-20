import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScaling
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FArchimedeanScaling.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.archimedean_scaling : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | exact GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | (intros; apply GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf <;> assumption)
