import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem BdWeight.proof (hP : BdPartition.Statement) (hI : IndicatorSmooth.Statement)
    (hN : NormSqSmooth.Statement) : BdWeight.Statement := by
  intro X _ _ _ D A R g hg hg0 hcoc
  obtain ⟨χ, hχs, hχ0, hχ1, hχsupp⟩ := hP D A R
  refine ⟨bdWeight R χ g, ?_, ?_, ?_⟩
  · intro j i
    have hterm : ∀ l, A.SmoothOn (bdDom R j)
        ((bdDom R l).indicator fun z => χ l z * ‖g j l z‖ ^ 2) := fun l =>
      hI D A (bdDom R j) (bdDom R l) (χ l) (fun z => ‖g j l z‖ ^ 2) (isOpen_bdDom R j)
        (isOpen_bdDom R l) (hχs l) (hχsupp l) (hN D A _ (g j l) (hg j l))
    have h := ContDiffOn.sum (s := Finset.univ) (fun l _ => hterm l i)
    convert h using 1
    ext x
    simp [bdWeight]
  · intro j y hy
    obtain ⟨l, hl⟩ : ∃ l, 0 < χ l y := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have h1 := hχ1 y
      have h2 : ∑ l, χ l y ≤ 0 := Finset.sum_nonpos fun l _ => h l
      linarith
    have hyl : y ∈ bdDom R l := hχsupp l (subset_tsupport _ (ne_of_gt hl))
    have hgne : g j l y ≠ 0 := hg0 j l y ⟨hy, hyl⟩
    unfold bdWeight
    refine Finset.sum_pos' (fun i _ => Set.indicator_nonneg
      (fun z _ => mul_nonneg (hχ0 i z) (sq_nonneg _)) y) ⟨l, Finset.mem_univ _, ?_⟩
    rw [Set.indicator_of_mem hyl]
    exact mul_pos hl (pow_pos (norm_pos_iff.mpr hgne) 2)
  · rintro j k y ⟨hyj, hyk⟩
    unfold bdWeight
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hyl : y ∈ bdDom R l
    · simp only [Set.indicator_of_mem hyl]
      rw [hcoc j k l y ⟨⟨hyj, hyk⟩, hyl⟩, norm_mul, mul_pow]
      ring
    · simp [hyl]

end GroundTheory.Heights₂.Heights.AnalyticLimit
