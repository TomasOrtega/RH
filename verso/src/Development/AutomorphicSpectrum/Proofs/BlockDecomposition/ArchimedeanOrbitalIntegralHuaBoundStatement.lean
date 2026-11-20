import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FArchimedeanOrbitalIntegralHuaBound.lean&line=273#L273)
-/
theorem _root_.GlobalTheory.T.archimedean_orbital_integral_hua_bound : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ), (∀ w, (J w).IsHermitian) → (∀ w, (J w).det ≠ 0) →
  ∀ (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  ∃ C : ℝ, ∀ b : W → hermC n, ‖coreC J μ (fun X => f (e X)) b‖ ≤
    C * ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound <;> assumption)
