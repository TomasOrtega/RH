import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSmallSectionCountRegimeFromRadiusOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsShiftSmallSectionCountRegimeFromRadiusOne.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_shift_smallSectionCount_regime_from_radius_one : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → P.A.SemiPos D → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Regime (shiftA P u) D := by
  first | exact @GlobalTheory.HSNef.regime_shiftA | exact GlobalTheory.HSNef.regime_shiftA | (intros; apply GlobalTheory.HSNef.regime_shiftA <;> assumption)
