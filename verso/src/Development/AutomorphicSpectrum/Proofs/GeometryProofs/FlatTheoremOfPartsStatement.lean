import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfParts
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFlatTheoremOfParts.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.flat_theorem_of_parts : PartI → FlatLineGenerator → FlatLineGeneratorComponent → FinConst → ThmFlatA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_parts | exact GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_parts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_parts <;> assumption)
