import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalUnitsContinuousSquareRoot
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FLocalUnitsContinuousSquareRoot.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.local_units_continuous_square_root : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ, ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧ (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit <;> assumption)
