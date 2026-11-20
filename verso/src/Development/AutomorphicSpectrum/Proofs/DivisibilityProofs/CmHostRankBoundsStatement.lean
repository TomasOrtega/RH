import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FCmHostRankBounds.lean&line=202#L202)
-/
theorem _root_.GlobalTheory.T.cm_host_rank_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 2 ≤ hostRd E ∧ Nonempty (CMType H) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers | exact GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers <;> assumption)
