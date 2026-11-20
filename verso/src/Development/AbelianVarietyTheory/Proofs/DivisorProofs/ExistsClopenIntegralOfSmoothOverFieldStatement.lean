import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverField
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsClopenIntegralOfSmoothOverField.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_clopen_integral_of_smooth_over_field' : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z, ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧ z ∈ Set.range j := by
  first | exact @GlobalTheory.exists_clopen_integral_of_smooth_over_field | exact GlobalTheory.exists_clopen_integral_of_smooth_over_field | (intros; apply GlobalTheory.exists_clopen_integral_of_smooth_over_field <;> assumption)
