import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Simplify using the standard rewrite rules. Establish `hr1 : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hrC : 0 ≤ (r : ℝ) * C` using `mul_nonneg (Nat.cast_nonneg r) hC`. Establish `hlog2 : 0 < Real.log 2` using `Real.log_pos one_lt_two`.

Establish `hL : Real.log 2 ≤ Real.log ((r : ℝ) + 1)` using `Real.log_le_log two_pos (by linarith)`. Establish `hc : 0 ≤ Real.log (2 * (1 + C))` using `Real.log_nonneg (by linarith)`. Establish `hX0 : 0 ≤ Real.log (2 * (1 + r * C))` using `Real.log_nonneg (by linarith)`. Establish `hX : Real.log (2 * (1 + r * C)) ≤ Real.log (2 * (1 + C)) + Real.log ((r : ℝ) + 1)`. Rewrite using `[← Real.log_mul (by linarith : (0 : ℝ) < 2 * (1 + C)).ne' (by positivity)]`.

Conclude with `Real.log_le_log (by linarith) (by nlinarith)`. Establish `hcL : Real.log (2 * (1 + C)) ≤ Real.log (2 * (1 + C)) / Real.log 2 * Real.log ((r : ℝ) + 1)`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hlog2]`. Conclude with `mul_le_mul_of_nonneg_left hL hc`. Establish `hK : Real.log (2 * (1 + r * C)) ≤ (1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1)`.

Establish `e : (1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1) = Real.log ((r : ℝ) + 1) + Real.log (2 * (1 + C)) / Real.log 2 * Real.log ((r : ℝ) + 1)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem LatticePointCount.log_error_le {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    (r : ℝ) * Real.log (2 * (1 + r * C)) ≤
      (1 + Real.log (2 * (1 + C)) / Real.log 2) * (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrC : 0 ≤ (r : ℝ) * C := mul_nonneg (Nat.cast_nonneg r) hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : Real.log 2 ≤ Real.log ((r : ℝ) + 1) := Real.log_le_log two_pos (by linarith)
  have hc : 0 ≤ Real.log (2 * (1 + C)) := Real.log_nonneg (by linarith)
  have hX0 : 0 ≤ Real.log (2 * (1 + r * C)) := Real.log_nonneg (by linarith)
  have hX : Real.log (2 * (1 + r * C)) ≤ Real.log (2 * (1 + C)) + Real.log ((r : ℝ) + 1) := by
    rw [← Real.log_mul (by linarith : (0 : ℝ) < 2 * (1 + C)).ne' (by positivity)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hcL : Real.log (2 * (1 + C)) ≤
      Real.log (2 * (1 + C)) / Real.log 2 * Real.log ((r : ℝ) + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hL hc
  have hK : Real.log (2 * (1 + r * C)) ≤
      (1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1) := by
    have e : (1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1) =
        Real.log ((r : ℝ) + 1) + Real.log (2 * (1 + C)) / Real.log 2 * Real.log ((r : ℝ) + 1) := by
      ring
    rw [e]
    linarith
  calc (r : ℝ) * Real.log (2 * (1 + r * C)) ≤ ((r : ℝ) + 1) * Real.log (2 * (1 + r * C)) :=
        mul_le_mul_of_nonneg_right (by linarith) hX0
    _ ≤ ((r : ℝ) + 1) * ((1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hK (by linarith)
    _ = (1 + Real.log (2 * (1 + C)) / Real.log 2) * (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1)) := by
        ring

/- English proof (translation)
Introduce `C hC`. Use `⟨1 + Real.log (2 * (1 + C)) / Real.log 2, ?_⟩` and prove the remaining obligations. Introduce `E _ _ r b hb S hS hcl`. Establish `hmem : ∀ x : E, x ∈ AddSubgroup.closure (Set.range b) ↔ x ∈ Submodule.span ℤ (Set.range b)` using `fun x ↦ by rw [← Submodule.span_int_eq_addSubgroupClosure]; exact Submodule.mem_toAddSubgroup _`. Establish `hspan : Submodule.span ℤ (S : Set E) = Submodule.span ℤ (Set.range b)` using `Submodule.toAddSubgroup_injective (by`.

Rewrite using `[Submodule.span_int_eq_addSubgroupClosure, Submodule.span_int_eq_addSubgroupClosure, hcl])`. Establish `hset : {x : E | x ∈ AddSubgroup.closure (Set.range b) ∧ ‖x‖ ≤ 1} = {x : E | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ 1}`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, hmem]`. Take `⟨hfin, hlog⟩` from `hA E r b hb (S : Set E) C hC.le hS hspan`.

Establish `hnn : 0 ≤ gram b`. Unfold `gram`. Conclude with `(Matrix.posSemidef_gram ℝ b).det_nonneg`. Establish `hg : -Real.log (Real.sqrt (gram b)) = -(1 / 2) * Real.log (Matrix.of fun i j ↦ @inner ℝ E _ (b i) (b j)).det`. Rewrite using `[Real.log_sqrt hnn]`.

Unfold `gram`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hset]`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`.

Use `LatticePointCount.log_error_le hC.le r` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem LatticePointCount.hilbDegreeBound_alt_of_statement (hA : GroundTheory.Heights₂.Heights.LatticePointCount.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LatticePointCount.Statement := by
  intro C hC
  refine ⟨1 + Real.log (2 * (1 + C)) / Real.log 2, ?_⟩
  intro E _ _ r b hb S hS hcl
  have hmem : ∀ x : E, x ∈ AddSubgroup.closure (Set.range b) ↔ x ∈ Submodule.span ℤ (Set.range b) :=
    fun x ↦ by rw [← Submodule.span_int_eq_addSubgroupClosure]; exact Submodule.mem_toAddSubgroup _
  have hspan : Submodule.span ℤ (S : Set E) = Submodule.span ℤ (Set.range b) :=
    Submodule.toAddSubgroup_injective (by
      rw [Submodule.span_int_eq_addSubgroupClosure, Submodule.span_int_eq_addSubgroupClosure, hcl])
  have hset : {x : E | x ∈ AddSubgroup.closure (Set.range b) ∧ ‖x‖ ≤ 1} =
      {x : E | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, hmem]
  obtain ⟨hfin, hlog⟩ := hA E r b hb (S : Set E) C hC.le hS hspan
  have hnn : 0 ≤ gram b := by
    unfold gram
    exact (Matrix.posSemidef_gram ℝ b).det_nonneg
  have hg : -Real.log (Real.sqrt (gram b)) =
      -(1 / 2) * Real.log (Matrix.of fun i j ↦ @inner ℝ E _ (b i) (b j)).det := by
    rw [Real.log_sqrt hnn]
    unfold gram
    ring
  rw [hset]
  refine ⟨hfin, ?_⟩
  rw [hg]
  have := LatticePointCount.log_error_le hC.le r
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
