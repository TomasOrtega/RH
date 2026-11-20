import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLargeDegreeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Sl.TopSlope.slopeBound` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FSlopeBoundOfLargeDegreeLine.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.slope_bound_of_large_degree_line : LineOfLargeDegree.Statement → KeyDegSt → SlopeBoundSt ∧ Prov.LemmaS := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TopSlope.slopeBound | exact GlobalTheory.CompanionTheory.Ar.Sl.TopSlope.slopeBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TopSlope.slopeBound <;> assumption)
