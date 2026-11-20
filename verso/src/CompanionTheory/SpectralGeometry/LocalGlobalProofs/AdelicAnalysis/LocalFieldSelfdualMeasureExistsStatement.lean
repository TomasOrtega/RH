import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalFieldSelfdualMeasureExists
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.LocalFields.LocalFourier
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FLocalFieldSelfdualMeasureExists.lean&line=173#L173)
-/
theorem _root_.GlobalTheory.T.local_field_selfdual_measure_exists : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (ψ : AddChar K Circle), Continuous ψ → ψ ≠ 1 → SelfDual (GroundTheory.LocalField.selfDualMeasure ψ) (fun s t => ((ψ (s * t) : Circle) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure | exact GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure <;> assumption)
