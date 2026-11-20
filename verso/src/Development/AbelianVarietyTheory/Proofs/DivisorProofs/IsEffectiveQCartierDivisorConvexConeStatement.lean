import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectiveQCartierDivisorConvexCone
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
Apply `GlobalTheory.QCartCone.isQCart_cone` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsEffectiveQCartierDivisorConvexCone.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.isEffectiveQCartierDivisor_convexCone : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D B : X → ℚ) (c : ℚ), IsQCart D → IsQCart B → 0 ≤ c → IsQCart (D + B) ∧ IsQCart (c • D) ∧ IsQCart (0 : X → ℚ) := by
  first | exact @GlobalTheory.QCartCone.isQCart_cone | exact GlobalTheory.QCartCone.isQCart_cone | (intros; apply GlobalTheory.QCartCone.isQCart_cone <;> assumption)
