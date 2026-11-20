import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.MinfUnique
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero

namespace Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory Formalism.BasicNotions

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem exists_haar_measure_with_density (p q : ℕ) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ∃ m : Measure (UpqT p q), m.IsHaarMeasure ∧ OmegaDensity m c := by
  obtain ⟨c', hc'0, hc't, hd⟩ :=
    Formalism.BasicNotions.Examples₂.CD.omegaDensity_haar p q (MeasureTheory.Measure.haar : Measure (UpqT p q))
  refine ⟨(c / c') • MeasureTheory.Measure.haar, ?_, ?_⟩
  · exact MeasureTheory.Measure.IsHaarMeasure.smul _ (ENNReal.div_pos_iff.mpr ⟨hc0, hc't⟩).ne'
      (ENNReal.div_lt_top hct hc'0).ne
  · have h := Formalism.BasicNotions.Examples₂.CD.omegaDensity_smul p q hd (c / c') (ENNReal.div_lt_top hct hc'0).ne
    rwa [ENNReal.div_mul_cancel hc'0 hc't] at h

end Formalism.IndefR.Leaf.Proofs
