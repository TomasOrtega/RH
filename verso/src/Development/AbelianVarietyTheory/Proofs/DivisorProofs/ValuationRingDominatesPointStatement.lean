import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingDominatesPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.Cell.exists_valuationRing_dominating_geo` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationRingDominatesPoint.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.valuation_ring_dominates_point : ∀ {P : Type} [CommRing P] (t t' : PrimeSpectrum P), t ≤ t' → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : ValuationRing R) (_ : Algebra R (Cell.GeoF t)) (_ : IsFractionRing R (Cell.GeoF t)) (χR : P →+* R), (algebraMap R (Cell.GeoF t)).comp χR = Cell.geoHom t ∧ RingHom.ker ((IsLocalRing.residue R).comp χR) = t'.asIdeal := by
  first | exact @GlobalTheory.ShFam.Cell.exists_valuationRing_dominating_geo | exact GlobalTheory.ShFam.Cell.exists_valuationRing_dominating_geo | (intros; apply GlobalTheory.ShFam.Cell.exists_valuationRing_dominating_geo <;> assumption)
