import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMeasurableSetOrbitExistsMeasurableSection.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.measurableSet_orbit_exists_measurable_section : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), MeasurableSet {y : X | ∃ g : G, g • x₀ = y} ∧ ∃ s : X → G, Measurable s ∧ ∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y := by
  first | exact @GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section | exact GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section | (intros; apply GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section <;> assumption)
