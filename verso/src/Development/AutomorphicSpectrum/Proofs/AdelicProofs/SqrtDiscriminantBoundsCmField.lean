import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.WeilBound.CoreStatements.SesquilinearFractions.SqrtDiscriminantBoundsCmField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FSesquilinearFractions%2FSqrtDiscriminantBoundsCmField.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  first | exact @PositivityTheory.Xgf.sqrt_discriminant_bounds_cm_field | exact PositivityTheory.Xgf.sqrt_discriminant_bounds_cm_field
