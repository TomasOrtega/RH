import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyDegreeOfBadReduction
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
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
Apply `GlobalTheory.CompanionTheory.Ar.Sl.keyDeg_of_keyBad` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FKeyDegreeOfBadReduction.lean&line=223#L223)
-/
theorem _root_.GlobalTheory.T.key_degree_of_bad_reduction : KeyBadSt → KeyDegSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.keyDeg_of_keyBad | exact GlobalTheory.CompanionTheory.Ar.Sl.keyDeg_of_keyBad | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.keyDeg_of_keyBad <;> assumption)
