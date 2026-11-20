import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZConn.isPreconnected_fibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FZariskiConnectednessIsPreconnectedFibre.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.zariski_connectedness_isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsLocallyNoetherian Y → IsProper a → (∀ V : Y.Opens, Function.Bijective (a.app V).hom) → ∀ y : Y, _root_.IsPreconnected {x : X | a x = y} := by
  first | exact @GlobalTheory.ZConn.isPreconnected_fibre | exact GlobalTheory.ZConn.isPreconnected_fibre | (intros; apply GlobalTheory.ZConn.isPreconnected_fibre <;> assumption)
