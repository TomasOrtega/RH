import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KollarTwoPointSeparationOfNadelVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.pointSeparationPair_of_vanishing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKollarTwoPointSeparationOfNadelVanishing.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.kollarTwoPointSeparation_of_nadelVanishing : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.PointSeparationPair := by
  first | exact @GlobalTheory.pointSeparationPair_of_vanishing | exact GlobalTheory.pointSeparationPair_of_vanishing | (intros; apply GlobalTheory.pointSeparationPair_of_vanishing <;> assumption)
