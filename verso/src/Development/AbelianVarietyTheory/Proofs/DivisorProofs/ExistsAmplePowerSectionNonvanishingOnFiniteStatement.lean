import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerSectionNonvanishingOnFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAmplePowerSectionNonvanishingOnFinite.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_ample_power_section_nonvanishing_on_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  first | exact @GlobalTheory.HSAmp.exists_sec_nonvanishing_finite | exact GlobalTheory.HSAmp.exists_sec_nonvanishing_finite | (intros; apply GlobalTheory.HSAmp.exists_sec_nonvanishing_finite <;> assumption)
