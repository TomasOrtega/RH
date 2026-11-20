import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
open PositivityTheory.Rg.BcB.G8

open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarProd

/- English proof (translation)
Introduce `G A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ α _ e`. Establish `: (μ.map e).IsHaarMeasure` using `e.isHaarMeasure_map μ`. Set `β₀ : Measure B` to `Measure.haar`. Establish `hc` using `Measure.isMulLeftInvariant_eq_smul (μ.map e) (α.prod β₀)`. Establish `hpos` using `Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map e) (α.prod β₀)`.

Use `⟨Measure.haarScalarFactor (μ.map e) (α.prod β₀) • β₀, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Measure.IsHaarMeasure.nnreal_smul _ hpos.ne'`. Rewrite using `[Measure.prod_smul_right]`. Conclude with `hc`.
-/
theorem haarSplit : HaarSplit := by
  intro G A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ α _ e
  have : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  let β₀ : Measure B := Measure.haar
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map e) (α.prod β₀)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map e) (α.prod β₀)
  refine ⟨Measure.haarScalarFactor (μ.map e) (α.prod β₀) • β₀, ?_, ?_⟩
  · exact Measure.IsHaarMeasure.nnreal_smul _ hpos.ne'
  · rw [Measure.prod_smul_right]
    exact hc

end GlobalTheory.CompanionTheory.HaarProd
