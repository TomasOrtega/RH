import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveBalancedFormEqOfSameRay
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolFan.isPrim_ray_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPrimitiveBalancedFormEqOfSameRay.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  first | exact @GlobalTheory.PolFan.isPrim_ray_eq | exact GlobalTheory.PolFan.isPrim_ray_eq | (intros; apply GlobalTheory.PolFan.isPrim_ray_eq <;> assumption)
