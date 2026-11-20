import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedClosedFibreProperCompleteLocalNoet
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsPreconnectedClosedFibreProperCompleteLocalNoet.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.isPreconnected_closedFibre_proper_completeLocalNoetherian : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A], IsAdicComplete (maximalIdeal A) A → ∀ (X : Scheme.{0}) (f : X ⟶ Sp A), IsProper f → PreconnectedSpace X → _root_.IsPreconnected {x : X | f x = closedPoint A} := by
  first | exact @GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre | exact GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre | (intros; apply GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre <;> assumption)
