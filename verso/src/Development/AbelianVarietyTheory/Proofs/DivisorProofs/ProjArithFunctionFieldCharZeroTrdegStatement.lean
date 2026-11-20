import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdeg
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArithFnField.charZero_and_trdeg_functionField` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjArithFunctionFieldCharZeroTrdeg.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.projArith_functionField_charZero_trdeg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → CharZero X.functionField ∧ Algebra.trdeg ℤ X.functionField = D := by
  first | exact @GlobalTheory.ArithFnField.charZero_and_trdeg_functionField | exact GlobalTheory.ArithFnField.charZero_and_trdeg_functionField | (intros; apply GlobalTheory.ArithFnField.charZero_and_trdeg_functionField <;> assumption)
