import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalingMeasureProductArchimedean
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FScalingMeasureProductArchimedean.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.scaling_measure_product_archimedean : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ (ι : Type) [Fintype ι] (ε : ℝ), 0 < ε → Measure.map (fun (y : ι → Ainf F) (i : ι) => θ ε * y i) (Measure.pi fun _ => li) = ENNReal.ofReal ((ε ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • Measure.pi fun _ => li := by
  first | exact @GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi | exact GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi | (intros; apply GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi <;> assumption)
