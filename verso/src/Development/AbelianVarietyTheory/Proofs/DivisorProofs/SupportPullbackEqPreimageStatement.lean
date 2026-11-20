import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportPullbackEqPreimage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QCoh.support_pullback` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSupportPullbackEqPreimage.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.support_pullback_eq_preimage : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [IsFiniteQC G], support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G := by
  first | exact @GlobalTheory.QCoh.support_pullback | exact GlobalTheory.QCoh.support_pullback | (intros; apply GlobalTheory.QCoh.support_pullback <;> assumption)
