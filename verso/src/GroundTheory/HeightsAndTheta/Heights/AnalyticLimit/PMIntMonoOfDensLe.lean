import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntMonoOfDensLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens mInt MIntegrable ChartPartition integralWith)

/- English proof (translation)
Introduce `D X _ _ A V Φ Ψ hd g hg0 hgV hgi`. Unfold `mInt`. Use `split_ifs with h`. Unfold `integralWith`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations.

Establish `hTm` using `(A.chart j).open_target.measurableSet`. Take `⟨hKc, hKs⟩` from `ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j) (isClosed_tsupport (h.some.χ j)) (h.some.tsupport_subset j)`. Establish `hcc` using `ReciprocityTheory.AnForm.M.chi_comp_continuousOn h.some j`. Establish `hint : IntegrableOn (fun y => h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target`. Use `ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport (h.some.χ j)) (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_` and prove the remaining obligations.

Establish `h1` using `(hgi j _ hKs hKc).mul_continuousOn (hcc.mono hKs) hKc`. Conclude with `h1.congr_fun (fun y _ => by ring) hKc.measurableSet`. Use `integral_mono_of_nonneg (ae_restrict_of_forall_mem hTm fun y hy => ?_) hint (ae_restrict_of_forall_mem hTm fun y hy => ?_)` and prove the remaining obligations. Distinguish the cases in `hyV : (A.chart j).symm y ∈ V`. Conclude with `mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg0 _)) (hd j y hy hyV).1`.

Simplify using `[hgV _ hyV]`. Distinguish the cases in `hyV : (A.chart j).symm y ∈ V`. Conclude with `mul_le_mul_of_nonneg_left (hd j y hy hyV).2 (mul_nonneg (h.some.nonneg j _) (hg0 _))`. Simplify using `[hgV _ hyV]`. Conclude with `le_rfl`.
-/
theorem MIntMonoOfDensLe.proof : MIntMonoOfDensLe.Statement := by
  intro D X _ _ A V Φ Ψ hd g hg0 hgV hgi
  unfold mInt
  split_ifs with h
  · unfold integralWith
    refine Finset.sum_le_sum fun j _ => ?_
    have hTm := (A.chart j).open_target.measurableSet
    obtain ⟨hKc, hKs⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j)
      (isClosed_tsupport (h.some.χ j)) (h.some.tsupport_subset j)
    have hcc := ReciprocityTheory.AnForm.M.chi_comp_continuousOn h.some j
    have hint : IntegrableOn (fun y => h.some.χ j ((A.chart j).symm y) *
        g ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target := by
      refine ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j)
        (Z := tsupport (h.some.χ j)) (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
      have h1 := (hgi j _ hKs hKc).mul_continuousOn (hcc.mono hKs) hKc
      exact h1.congr_fun (fun y _ => by ring) hKc.measurableSet
    refine integral_mono_of_nonneg (ae_restrict_of_forall_mem hTm fun y hy => ?_) hint
      (ae_restrict_of_forall_mem hTm fun y hy => ?_)
    · by_cases hyV : (A.chart j).symm y ∈ V
      · exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg0 _)) (hd j y hy hyV).1
      · simp [hgV _ hyV]
    · by_cases hyV : (A.chart j).symm y ∈ V
      · exact mul_le_mul_of_nonneg_left (hd j y hy hyV).2 (mul_nonneg (h.some.nonneg j _) (hg0 _))
      · simp [hgV _ hyV]
  · exact le_rfl

end GroundTheory.Heights₂.Heights.AnalyticLimit
