import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelEstablished
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FM2ModelEstablished.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.rootLineDeRhamModel_holds : RootLineDeRhamModel := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds | exact GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds <;> assumption)
