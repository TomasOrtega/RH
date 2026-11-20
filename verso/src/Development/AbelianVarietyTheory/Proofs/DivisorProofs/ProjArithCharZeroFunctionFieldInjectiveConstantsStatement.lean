import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithCharZeroFunctionFieldInjectiveConstants
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isArithVar_charZero_functionField_and_injective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjArithCharZeroFunctionFieldInjectiveConstants.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.projArith_charZero_functionField_injective_constants : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  first | exact @GlobalTheory.isArithVar_charZero_functionField_and_injective | exact GlobalTheory.isArithVar_charZero_functionField_and_injective | (intros; apply GlobalTheory.isArithVar_charZero_functionField_and_injective <;> assumption)
