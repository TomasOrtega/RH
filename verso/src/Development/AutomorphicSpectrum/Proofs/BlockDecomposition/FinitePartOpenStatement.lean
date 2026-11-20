import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpen
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFinitePartOpen.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.finite_part_open : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  first | exact @GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | exact GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | (intros; apply GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen <;> assumption)
