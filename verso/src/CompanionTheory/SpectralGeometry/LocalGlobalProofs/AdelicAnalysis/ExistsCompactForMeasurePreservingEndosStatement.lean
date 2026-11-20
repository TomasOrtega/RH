import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsCompactForMeasurePreservingEndos
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FExistsCompactForMeasurePreservingEndos.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_compact_for_measure_preserving_endos : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ → ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C → (∀ y, ∃ l, y - j l ∈ C) → ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ → ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving | exact GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving | (intros; apply GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving <;> assumption)
