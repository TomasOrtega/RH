import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSection
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FArchimedeanSection.lean&line=267#L267)
-/
theorem _root_.GlobalTheory.T.archimedean_section : PositivityTheory.PfSWUS.SchInf.SecInf := by
  first | exact @GlobalTheory.CompanionTheory.SecInf.secInf | exact GlobalTheory.CompanionTheory.SecInf.secInf | (intros; apply GlobalTheory.CompanionTheory.SecInf.secInf <;> assumption)
