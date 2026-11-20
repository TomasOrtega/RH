import Mathlib

open MeasureTheory Measure
open scoped NNReal ENNReal

namespace GlobalTheory.St.HaarSplit

/- English proof (translation)
Set `ν : Measure B` to `Measure.haar`. Establish `: ((μA.prod ν).map e).IsHaarMeasure` using `ContinuousMulEquiv.isHaarMeasure_map (μA.prod ν) e`. Establish `h` using `isMulLeftInvariant_eq_smul μC ((μA.prod ν).map e)`. Establish `hc : 0 < haarScalarFactor μC ((μA.prod ν).map e)` using `haarScalarFactor_pos_of_isHaarMeasure _ _`. Use `⟨haarScalarFactor μC ((μA.prod ν).map e) • ν, IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [h]`. Generalize the expression as in `haarScalarFactor μC ((μA.prod ν).map e) = c`. Rewrite using `[← Measure.map_smul]`. Use `congr 1`. Rewrite using `[ENNReal.smul_def, ENNReal.smul_def, Measure.prod_smul_right]`.
-/
theorem exists_haar_map_prod_eq {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [BorelSpace A] [BorelSpace B] [BorelSpace C]
    [LocallyCompactSpace A] [LocallyCompactSpace B] [LocallyCompactSpace C]
    [SecondCountableTopology A] [SecondCountableTopology B] [SecondCountableTopology C]
    (e : (A × B) ≃ₜ* C) (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure] :
    ∃ μB : Measure B, μB.IsHaarMeasure ∧ (μA.prod μB).map e = μC := by
  let ν : Measure B := Measure.haar
  have : ((μA.prod ν).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μA.prod ν) e
  have h := isMulLeftInvariant_eq_smul μC ((μA.prod ν).map e)
  have hc : 0 < haarScalarFactor μC ((μA.prod ν).map e) := haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨haarScalarFactor μC ((μA.prod ν).map e) • ν, IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  conv_rhs => rw [h]
  generalize haarScalarFactor μC ((μA.prod ν).map e) = c
  rw [← Measure.map_smul]
  congr 1
  rw [ENNReal.smul_def, ENNReal.smul_def, Measure.prod_smul_right]

end GlobalTheory.St.HaarSplit
