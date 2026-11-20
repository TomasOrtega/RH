import ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeDefs

namespace ReciprocityTheory.ThetaSummability.Est

open MeasureTheory Finset

variable {r : ℕ}

/- English proof (translation)
Establish `h1 : univ.filter (fun j : Fin r => k ≤ j) = insert k (univ.filter (fun j : Fin r => k < j))`. Use extensionality with `j`. Simplify using `[le_iff_eq_or_lt, eq_comm]`. Unfold `tailSum`. Rewrite using `[h1, Finset.sum_insert (by simp)]`.

Use `congr 1`. Use `split_ifs with h`. Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]`.

Use linear arithmetic over natural numbers and integers. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hj`. Use linear arithmetic over natural numbers and integers.
-/
theorem tailSum_eq_add (y : Fin r → ℝ) (k : Fin r) :
    tailSum y k = y k + (if h : k.val + 1 < r then tailSum y ⟨k.val + 1, h⟩ else 0) := by
  have h1 : univ.filter (fun j : Fin r => k ≤ j) = insert k (univ.filter (fun j : Fin r => k < j)) := by
    ext j; simp [le_iff_eq_or_lt, eq_comm]
  unfold tailSum
  rw [h1, Finset.sum_insert (by simp)]
  congr 1
  split_ifs with h
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]; omega
  · apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hj; omega

/- English proof (translation)
Use function extensionality and compare the values at `k`. Unfold `gap`. Rewrite using `[tailSum_eq_add]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem gap_tailSum (y : Fin r → ℝ) : gap (tailSum y) = y := by
  funext k
  unfold gap
  rw [tailSum_eq_add]
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[tailSum_eq_add]`. Use `split_ifs with h`. Rewrite using `[tailSum_gap_apply x ⟨k.val + 1, h⟩, gap, dif_pos h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[gap, dif_neg h]`.

Expand and normalize the polynomial expressions, which then agree. Use `termination_by r - k.val`. Use `decreasing_by omega`.
-/
theorem tailSum_gap_apply (x : Fin r → ℝ) (k : Fin r) : tailSum (gap x) k = x k := by
  rw [tailSum_eq_add]
  split_ifs with h
  · rw [tailSum_gap_apply x ⟨k.val + 1, h⟩, gap, dif_pos h]; ring
  · rw [gap, dif_neg h]; ring
termination_by r - k.val
decreasing_by omega

/- English proof (translation)
The claim follows from `funext (tailSum_gap_apply x)`.
-/
theorem tailSum_gap (x : Fin r → ℝ) : tailSum (gap x) = x := funext (tailSum_gap_apply x)

def tailMat (r : ℕ) : Matrix (Fin r) (Fin r) ℝ := fun i j => if i ≤ j then 1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, tailMat, tailSum, Finset.sum_filter, ite_mul]`.
-/
theorem tailMat_mulVec (y : Fin r → ℝ) : (tailMat r).mulVec y = tailSum y := by
  funext k
  simp [Matrix.mulVec, dotProduct, tailMat, tailSum, Finset.sum_filter, ite_mul]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular]`. Simplify using `[tailMat]`. Introduce `i j hij`. Establish `: ¬ i ≤ j` using `not_le.mpr hij`. Simplify using `[tailMat, this]`.
-/
theorem det_tailMat : (tailMat r).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [tailMat]
  · intro i j hij
    have : ¬ i ≤ j := not_le.mpr hij
    simp [tailMat, this]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[Matrix.toLin'_apply, tailMat_mulVec]`.
-/
theorem tailSum_eq_toLin' : (tailSum (r := r)) = ⇑(Matrix.toLin' (tailMat r)) := by
  funext y; rw [Matrix.toLin'_apply, tailMat_mulVec]

/- English proof (translation)
Rewrite using `[tailSum_eq_toLin']`. Conclude with `LinearMap.continuous_of_finiteDimensional _`.
-/
theorem continuous_tailSum : Continuous (tailSum (r := r)) := by
  rw [tailSum_eq_toLin']; exact LinearMap.continuous_of_finiteDimensional _

/- English proof (translation)
Use `continuous_pi fun k => ?_` and prove the remaining obligations. Unfold `gap`. Use `split_ifs`. Conclude with `(continuous_apply _).sub (continuous_apply _)`. Conclude with `(continuous_apply _).sub continuous_const`.
-/
theorem continuous_gap : Continuous (gap (r := r)) := by
  refine continuous_pi fun k => ?_
  unfold gap
  split_ifs
  · exact (continuous_apply _).sub (continuous_apply _)
  · exact (continuous_apply _).sub continuous_const

/- English proof (translation)
Use `⟨continuous_tailSum.measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[tailSum_eq_toLin', Real.map_linearMap_volume_pi_eq_smul_volume_pi]`. Simplify using `[LinearMap.det_toLin', det_tailMat]`. Simplify using `[LinearMap.det_toLin', det_tailMat]`.
-/
theorem measurePreserving_tailSum :
    MeasurePreserving (tailSum (r := r)) volume volume := by
  refine ⟨continuous_tailSum.measurable, ?_⟩
  rw [tailSum_eq_toLin', Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · simp [LinearMap.det_toLin', det_tailMat]
  · simp [LinearMap.det_toLin', det_tailMat]

def tailSumEquiv (r : ℕ) : (Fin r → ℝ) ≃ᵐ (Fin r → ℝ) where
  toFun := tailSum
  invFun := gap
  left_inv := gap_tailSum
  right_inv := tailSum_gap
  measurable_toFun := continuous_tailSum.measurable
  measurable_invFun := continuous_gap.measurable

/- English proof (translation)
The claim follows from `(tailSumEquiv r).measurableEmbedding`.
-/
theorem measurableEmbedding_tailSum : MeasurableEmbedding (tailSum (r := r)) :=
  (tailSumEquiv r).measurableEmbedding

/- English proof (translation)
Simplify using `[logCone, lowerBox, gap_tailSum, Pi.le_def]`.
-/
theorem tailSum_mem_logCone_iff (c : ℝ) (y : Fin r → ℝ) :
    tailSum y ∈ logCone r c ↔ y ∈ lowerBox r c := by
  simp [logCone, lowerBox, gap_tailSum, Pi.le_def]

/- English proof (translation)
Use extensionality with `y`. Conclude with `tailSum_mem_logCone_iff c y`.
-/
theorem preimage_tailSum_logCone (c : ℝ) : tailSum ⁻¹' logCone r c = lowerBox r c := by
  ext y; exact tailSum_mem_logCone_iff c y

/- English proof (translation)
Rewrite using `[← preimage_tailSum_logCone c, measurePreserving_tailSum.setIntegral_preimage_emb measurableEmbedding_tailSum]`.
-/
theorem setIntegral_logCone (c : ℝ) (f : (Fin r → ℝ) → ℝ) :
    ∫ x in logCone r c, f x = ∫ y in lowerBox r c, f (tailSum y) := by
  rw [← preimage_tailSum_logCone c,
    measurePreserving_tailSum.setIntegral_preimage_emb measurableEmbedding_tailSum]

/- English proof (translation)
Rewrite using `[← preimage_tailSum_logCone c]`. Conclude with `(measurePreserving_tailSum.integrableOn_comp_preimage measurableEmbedding_tailSum).symm`.
-/
theorem integrableOn_logCone_iff (c : ℝ) (f : (Fin r → ℝ) → ℝ) :
    IntegrableOn f (logCone r c) ↔ IntegrableOn (fun y => f (tailSum y)) (lowerBox r c) := by
  rw [← preimage_tailSum_logCone c]
  exact (measurePreserving_tailSum.integrableOn_comp_preimage measurableEmbedding_tailSum).symm

end ReciprocityTheory.ThetaSummability.Est
