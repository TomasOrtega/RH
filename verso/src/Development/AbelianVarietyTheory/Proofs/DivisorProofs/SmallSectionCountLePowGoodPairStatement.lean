import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLePowGoodPair
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
Apply `GlobalTheory.VolBr.crude_upper_lc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmallSectionCountLePowGoodPair.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.smallSectionCount_le_pow_goodPair : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.crude_upper_lc | exact GlobalTheory.VolBr.crude_upper_lc | (intros; apply GlobalTheory.VolBr.crude_upper_lc <;> assumption)
