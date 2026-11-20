import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrix
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PosOpen.posopen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEventuallyPosDefHermFormNearZeroMatrix.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.eventually_posDef_hermForm_near_zero_matrix : ∀ {g : ℕ} (M₀ : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M₀ z z).re) → ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), (1 - C.map star * C).det ≠ 0 ∧ (1 - C * C.map star).det ≠ 0 ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) z z).re := by
  first | exact @GlobalTheory.PosOpen.posopen | exact GlobalTheory.PosOpen.posopen | (intros; apply GlobalTheory.PosOpen.posopen; all_goals assumption)
