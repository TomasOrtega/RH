import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralMultipleBoundedPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsIntegralMultipleBoundedPlaces.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.exists_integral_multiple_bounded_places : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator | exact GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator <;> assumption)
