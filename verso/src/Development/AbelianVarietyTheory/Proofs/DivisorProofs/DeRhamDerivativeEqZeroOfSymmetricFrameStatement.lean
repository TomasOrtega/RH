import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeRhamDerivativeEqZeroOfSymmetricFrame.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  first | exact @GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | exact GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | (intros; apply GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm <;> assumption)
