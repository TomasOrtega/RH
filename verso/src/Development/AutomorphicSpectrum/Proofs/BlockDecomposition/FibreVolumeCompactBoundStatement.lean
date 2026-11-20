import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFibreVolumeCompactBound.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.fibre_volume_compact_bound : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ P : Set V, IsCompact P → IsOpen P → P ⊆ Z → ∃ c : ℝ≥0, ∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le <;> assumption)
