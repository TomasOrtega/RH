import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBox
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BoxVolume.volM_box` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMatrixEntrywiseProductMeasureUniformizerPowerBox.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [Fintype D] (c : A → D → ℤ),
    volM ν A D {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} =
      ν (𝒪[k] : Set k) ^ (Fintype.card A * Fintype.card D) *
        ENNReal.ofReal ((resCard k : ℝ) ^ (-∑ i, ∑ j, c i j)) := by
  first | exact @GlobalTheory.BoxVolume.volM_box | exact GlobalTheory.BoxVolume.volM_box | (intros; apply GlobalTheory.BoxVolume.volM_box <;> assumption)
