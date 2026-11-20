import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.MinfMeasure

/- English proof (translation)
Establish `hm0 : minfDensity (p + q) ≠ 0` using `ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top (by simp))`. Establish `hmt : minfDensity (p + q) ≠ ⊤` using `ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)`. Establish `hne0 : minfDensity (p + q) / c ≠ 0` using `ENNReal.div_ne_zero.2 ⟨hm0, ht⟩`. Establish `hnet : minfDensity (p + q) / c ≠ ⊤` using `ENNReal.div_ne_top hmt h0`. Use `lift minfDensity (p + q) / c to ℝ≥0 using hnet with t htc`.

Use `⟨t • μ, Measure.IsHaarMeasure.nnreal_smul μ (by exact_mod_cast hne0), ?_⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.CompactDualUnique.omegaDensity_smul t hc`. Rewrite `h` using `[htc, ENNReal.div_mul_cancel h0 ht]`. Then use the resulting hypothesis.
-/
theorem exists_isMinf_of_density {p q : ℕ} (μ : Measure (UpqT p q)) (hμ : μ.IsHaarMeasure) (c : ℝ≥0∞)
    (h0 : c ≠ 0) (ht : c ≠ ⊤) (hc : OmegaDensity μ c) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  have hm0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top (by simp))
  have hmt : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hne0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hm0, ht⟩
  have hnet : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top hmt h0
  lift minfDensity (p + q) / c to ℝ≥0 using hnet with t htc
  refine ⟨t • μ, Measure.IsHaarMeasure.nnreal_smul μ (by exact_mod_cast hne0), ?_⟩
  have h := GlobalTheory.CompactDualUnique.omegaDensity_smul t hc
  rwa [htc, ENNReal.div_mul_cancel h0 ht] at h

/- English proof (translation)
Take `⟨cd⟩` from `h`. Take `⟨c, h0, ht, hc, -⟩` from `cd.trick p q`. Conclude with `exists_isMinf_of_density _ (cd.haar p q) c h0 ht hc`.
-/
theorem exists_isMinf_of_cd (h : Nonempty CDHaar) (p q : ℕ) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  obtain ⟨cd⟩ := h
  obtain ⟨c, h0, ht, hc, -⟩ := cd.trick p q
  exact exists_isMinf_of_density _ (cd.haar p q) c h0 ht hc

end GlobalTheory.MinfMeasure
