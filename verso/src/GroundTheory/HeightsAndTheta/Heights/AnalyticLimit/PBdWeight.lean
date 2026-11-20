import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

/- English proof (translation)
Introduce `X _ _ _ D A R g hg hg0 hcoc`. Take `⟨χ, hχs, hχ0, hχ1, hχsupp⟩` from `hP D A R`. Use `⟨bdWeight R χ g, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j i`. Establish `hterm : ∀ l, A.SmoothOn (bdDom R j) ((bdDom R l).indicator fun z => χ l z * ‖g j l z‖ ^ 2)` using `fun l => hI D A (bdDom R j) (bdDom R l) (χ l) (fun z => ‖g j l z‖ ^ 2) (isOpen_bdDom R j) (isOpen_bdDom R l) (hχs l) (hχsupp l) (hN D A _ (g j l) (hg j l))`.

Establish `h` using `ContDiffOn.sum (s := Finset.univ) (fun l _ => hterm l i)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `[bdWeight]`. Introduce `j y hy`.

Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, 0 < χ l y := by`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_lt] at h`. Establish `h1` using `hχ1 y`. Establish `h2 : ∑ l, χ l y ≤ 0` using `Finset.sum_nonpos fun l _ => h l`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hyl : y ∈ bdDom R l` using `hχsupp l (subset_tsupport _ (ne_of_gt hl))`. Establish `hgne : g j l y ≠ 0` using `hg0 j l y ⟨hy, hyl⟩`. Unfold `bdWeight`. Use `Finset.sum_pos' (fun i _ => Set.indicator_nonneg (fun z _ => mul_nonneg (hχ0 i z) (sq_nonneg _)) y) ⟨l, Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem hyl]`. Conclude with `mul_pos hl (pow_pos (norm_pos_iff.mpr hgne) 2)`. Introduce and unpack `j k y ⟨hyj, hyk⟩`. Unfold `bdWeight`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hyl : y ∈ bdDom R l`. Simplify using `only [Set.indicator_of_mem hyl]`. Rewrite using `[hcoc j k l y ⟨⟨hyj, hyk⟩, hyl⟩, norm_mul, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hyl]`.
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
