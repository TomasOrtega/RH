import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProperLiftTraitOfGenericLift.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.proper_lift_trait_of_generic_lift : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by
  first | exact @GlobalTheory.proper_lift_trait | exact GlobalTheory.proper_lift_trait | (intros; apply GlobalTheory.proper_lift_trait <;> assumption)
