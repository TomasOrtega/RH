import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone
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
Apply `GlobalTheory.NefShift.isNef_shift_mono` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermitianLineBundleIsNefShiftMonotone.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.hermitianLineBundle_isNef_shift_monotone : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t t' : ℝ), t ≤ t' → (M.shift (fun _ => t) fun _ => rfl).IsNef D → (M.shift (fun _ => t') fun _ => rfl).IsNef D := by
  first | exact @GlobalTheory.NefShift.isNef_shift_mono | exact GlobalTheory.NefShift.isNef_shift_mono | (intros; apply GlobalTheory.NefShift.isNef_shift_mono <;> assumption)
