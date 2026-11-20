import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHolds
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinHalfHolds.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.eisenstein_half_holds : EisHalf := by
  first | exact @GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf | exact GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf | (intros; apply GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf <;> assumption)
