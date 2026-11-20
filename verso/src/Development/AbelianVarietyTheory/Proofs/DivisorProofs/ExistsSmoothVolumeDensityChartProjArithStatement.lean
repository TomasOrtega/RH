import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVolumeDensityChartProjArith
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSmoothVolumeDensityChartProjArith.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_smoothVolumeDensityChart_projArith : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ σ : k →+* ℂ, Nonempty (VolDens p σ D) := by
  first | exact @GlobalTheory.HSAmp.exists_volDens | exact GlobalTheory.HSAmp.exists_volDens | (intros; apply GlobalTheory.HSAmp.exists_volDens <;> assumption)
