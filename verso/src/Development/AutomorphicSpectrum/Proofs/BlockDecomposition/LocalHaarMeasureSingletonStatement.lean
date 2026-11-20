import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarMeasureSingleton
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalHaarMeasureSingleton.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.local_haar_measure_singleton : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero | exact GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero <;> assumption)
