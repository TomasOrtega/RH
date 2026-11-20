import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLower
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeArithVolumeOfFrequentlySmallSectionsLower.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  first | exact @GlobalTheory.VolBr.le_arVol_of_frequently_le | exact GlobalTheory.VolBr.le_arVol_of_frequently_le | (intros; apply GlobalTheory.VolBr.le_arVol_of_frequently_le <;> assumption)
