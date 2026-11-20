import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermLineBundlePairBallsFinite.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.hermLineBundlePair_balls_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  first | exact @GlobalTheory.VolBr.BallFinite.bl_finite | exact GlobalTheory.VolBr.BallFinite.bl_finite | (intros; apply GlobalTheory.VolBr.BallFinite.bl_finite <;> assumption)
