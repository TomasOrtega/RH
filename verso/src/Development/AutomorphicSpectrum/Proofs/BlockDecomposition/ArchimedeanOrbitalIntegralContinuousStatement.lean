import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FArchimedeanOrbitalIntegralContinuous.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.archimedean_orbital_integral_continuous : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
  (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  Continuous (coreC J μ (fun X => f (e X))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz <;> assumption)
