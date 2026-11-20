import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SqrtDiscriminantBoundsCmField
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAdelicProofs%2FSqrtDiscriminantBoundsCmField.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field | exact GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field | (intros; apply GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field <;> assumption)
