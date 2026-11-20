import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldPair.ratRes_locRing_of_isClosed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasRationalResidueFieldPointLocalRingClosedPoint.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ) [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) → RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed <;> assumption)
