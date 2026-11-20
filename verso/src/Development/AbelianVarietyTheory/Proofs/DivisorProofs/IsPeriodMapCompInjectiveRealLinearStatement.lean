import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinear
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsPeriodMapCompInjectiveRealLinear.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isPeriodMap_comp_injective_realLinear : ∀ {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → Function.Injective R → (∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) → M.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) → (∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) → IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  first | exact @GlobalTheory.PELU.isPeriod_comp_realLinear | exact GlobalTheory.PELU.isPeriod_comp_realLinear | (intros; apply GlobalTheory.PELU.isPeriod_comp_realLinear <;> assumption)
