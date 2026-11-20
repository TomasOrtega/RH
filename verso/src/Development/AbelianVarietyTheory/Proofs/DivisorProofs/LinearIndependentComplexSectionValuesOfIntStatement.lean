import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexSectionValuesOfInt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLinearIndependentComplexSectionValuesOfInt.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.linearIndependent_complex_sectionValues_of_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (ι : Type) [Fintype ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ c : ι → ℂ, (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∑ i, c i * val P a b σ y (f i) = 0) → c = 0 := by
  first | exact @GlobalTheory.HSAmp.linearIndependent_vals | exact GlobalTheory.HSAmp.linearIndependent_vals | (intros; apply GlobalTheory.HSAmp.linearIndependent_vals <;> assumption)
