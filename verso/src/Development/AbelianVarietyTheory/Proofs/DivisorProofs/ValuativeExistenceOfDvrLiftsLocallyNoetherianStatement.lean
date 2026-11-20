import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeExistenceOfDvrLiftsLocallyNoetherian
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuativeExistenceOfDvrLiftsLocallyNoetherian.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.valuativeExistence_of_dvr_lifts_locallyNoetherian : ∀ {Y S : Scheme.{0}} [IsLocallyNoetherian S] (π : Y ⟶ S), LocallyOfFiniteType π → QuasiCompact π → IsSeparated π → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y → ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) → ValuativeCriterion.Existence π := by
  first | exact @GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing | exact GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing | (intros; apply GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing <;> assumption)
