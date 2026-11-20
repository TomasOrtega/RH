import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.NonarchimedeanSelfdualMeasurePi
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FNonarchimedeanSelfdualMeasurePi.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.nonarchimedean_selfdual_measure_pi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiV F ψ v (x ⬝ᵥ y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v | exact GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v | (intros; apply GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v <;> assumption)
