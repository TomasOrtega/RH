import ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeDefs

namespace ReciprocityTheory.ThetaSummability.Est

open MeasureTheory Finset

variable {r : ℕ}

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
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
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem gap_tailSum (y : Fin r → ℝ) : gap (tailSum y) = y := by
  funext k
  unfold gap
  rw [tailSum_eq_add]
  split_ifs <;> ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem tailSum_gap_apply (x : Fin r → ℝ) (k : Fin r) : tailSum (gap x) k = x k := by
  rw [tailSum_eq_add]
  split_ifs with h
  · rw [tailSum_gap_apply x ⟨k.val + 1, h⟩, gap, dif_pos h]; ring
  · rw [gap, dif_neg h]; ring
termination_by r - k.val
decreasing_by omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tailSum_gap (x : Fin r → ℝ) : tailSum (gap x) = x := funext (tailSum_gap_apply x)

def tailMat (r : ℕ) : Matrix (Fin r) (Fin r) ℝ := fun i j => if i ≤ j then 1 else 0

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem tailMat_mulVec (y : Fin r → ℝ) : (tailMat r).mulVec y = tailSum y := by
  funext k
  simp [Matrix.mulVec, dotProduct, tailMat, tailSum, Finset.sum_filter, ite_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem det_tailMat : (tailMat r).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [tailMat]
  · intro i j hij
    have : ¬ i ≤ j := not_le.mpr hij
    simp [tailMat, this]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem tailSum_eq_toLin' : (tailSum (r := r)) = ⇑(Matrix.toLin' (tailMat r)) := by
  funext y; rw [Matrix.toLin'_apply, tailMat_mulVec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_tailSum : Continuous (tailSum (r := r)) := by
  rw [tailSum_eq_toLin']; exact LinearMap.continuous_of_finiteDimensional _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_gap : Continuous (gap (r := r)) := by
  refine continuous_pi fun k => ?_
  unfold gap
  split_ifs
  · exact (continuous_apply _).sub (continuous_apply _)
  · exact (continuous_apply _).sub continuous_const

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
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
A detailed English derivation is pending.
-/
theorem measurableEmbedding_tailSum : MeasurableEmbedding (tailSum (r := r)) :=
  (tailSumEquiv r).measurableEmbedding

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem tailSum_mem_logCone_iff (c : ℝ) (y : Fin r → ℝ) :
    tailSum y ∈ logCone r c ↔ y ∈ lowerBox r c := by
  simp [logCone, lowerBox, gap_tailSum, Pi.le_def]

/- English proof (translation)
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem preimage_tailSum_logCone (c : ℝ) : tailSum ⁻¹' logCone r c = lowerBox r c := by
  ext y; exact tailSum_mem_logCone_iff c y

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem setIntegral_logCone (c : ℝ) (f : (Fin r → ℝ) → ℝ) :
    ∫ x in logCone r c, f x = ∫ y in lowerBox r c, f (tailSum y) := by
  rw [← preimage_tailSum_logCone c,
    measurePreserving_tailSum.setIntegral_preimage_emb measurableEmbedding_tailSum]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem integrableOn_logCone_iff (c : ℝ) (f : (Fin r → ℝ) → ℝ) :
    IntegrableOn f (logCone r c) ↔ IntegrableOn (fun y => f (tailSum y)) (lowerBox r c) := by
  rw [← preimage_tailSum_logCone c]
  exact (measurePreserving_tailSum.integrableOn_comp_preimage measurableEmbedding_tailSum).symm

end ReciprocityTheory.ThetaSummability.Est
