import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerLiftOfNonvanishingOnClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAmplePowerLiftOfNonvanishingOnClosed.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ) (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ → ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed | exact GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed | (intros; apply GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed <;> assumption)
