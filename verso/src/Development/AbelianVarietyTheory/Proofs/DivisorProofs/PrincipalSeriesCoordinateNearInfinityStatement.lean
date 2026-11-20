import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesCoordinateNearInfinity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrinTwo.coord_eq_of_far` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrincipalSeriesCoordinateNearInfinity.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.principal_series_coordinate_near_infinity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by
  first | exact @GlobalTheory.PrinTwo.coord_eq_of_far | exact GlobalTheory.PrinTwo.coord_eq_of_far | (intros; apply GlobalTheory.PrinTwo.coord_eq_of_far <;> assumption)
