import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldPointMemOpenOfReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MBLow.TanGauge.top_le_of_redE` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualNumberFieldPointMemOpenOfReduction.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.dualNumber_field_point_mem_open_of_reduction : ∀ (C : Type) [Field C] {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens),
    ⊤ ≤ (redE C ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U := by
  first | exact @GlobalTheory.MBLow.TanGauge.top_le_of_redE | exact GlobalTheory.MBLow.TanGauge.top_le_of_redE | (intros; apply GlobalTheory.MBLow.TanGauge.top_le_of_redE <;> assumption)
