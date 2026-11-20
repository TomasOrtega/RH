import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousMvPowerSeriesAlgHomExt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPadicContinuousMvPowerSeriesAlgHomExt.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.padicContinuous_mvPowerSeries_algHom_ext : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] (F F' : MvPowerSeries σ O →ₐ[O] A), (∀ i, F (X i) = F' (X i)) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F f) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F' f) → F = F' := by
  first | exact @GlobalTheory.PadicMvPowerSeriesExt.algHom_ext | exact GlobalTheory.PadicMvPowerSeriesExt.algHom_ext | (intros; apply GlobalTheory.PadicMvPowerSeriesExt.algHom_ext <;> assumption)
