import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSAmp.finrank_ratF_eq_gdeg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankFunctionFieldQuotientSubfieldEqDegree.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  first | exact @GlobalTheory.HSAmp.finrank_ratF_eq_gdeg | exact GlobalTheory.HSAmp.finrank_ratF_eq_gdeg | (intros; apply GlobalTheory.HSAmp.finrank_ratF_eq_gdeg <;> assumption)
