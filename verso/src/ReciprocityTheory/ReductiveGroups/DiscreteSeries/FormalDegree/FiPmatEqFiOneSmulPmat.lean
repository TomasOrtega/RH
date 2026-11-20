import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.LseConvexOn

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Check the signs of the components of the expression.
-/
theorem wS_nonneg' {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) : 0 ≤ wS z hi S := by
  unfold wS
  positivity

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem fi_eq_lse {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (t : ℝ) :
    Fi ((t : ℂ) • pmat z) i = Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1)) := by
  unfold Fi
  rw [lemma3a z hi t]
  congr 1
  have h : (∑ S, ((wS z hi S : ℝ) : ℂ) * Complex.exp ((t * yS z S.1 : ℝ) : ℂ)) =
      ((∑ S, wS z hi S * Real.exp (t * yS z S.1) : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.ofReal_exp, Complex.ofReal_mul]
  rw [h, Complex.ofReal_re]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fi_pmat_eq_fi_one_smul_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) :
    Fi (pmat z) i = Fi (((1 : ℝ) : ℂ) • pmat z) i := by
  rw [Complex.ofReal_one, one_smul]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fi_convex {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) := by
  have h : (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) =
      fun t : ℝ => Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1)) := by
    funext t
    exact fi_eq_lse z hi t
  rw [h]
  exact lse_convexOn (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem fi_zero (i : ℕ) : Fi (0 : Matrix (Fin n) (Fin n) ℂ) i = 0 := by
  unfold Fi Del
  rw [NormedSpace.exp_zero]
  split_ifs with h
  · rw [Matrix.submatrix_one _ (Fin.castLE_injective h)]
    simp
  · simp

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem fi_nonneg {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) : 0 ≤ Fi (pmat z) i := by
  by_cases hi : i ≤ n
  · rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi]
    apply Real.log_nonneg
    have h := lse_one_le (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    simpa only [one_mul] using h
  · unfold Fi Del
    rw [dif_neg hi]
    simp

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Check the signs of the components of the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem fi_lower {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) {ep : ℝ}
    (h1 : rhoP z ≤ ep) (h2 : ep ≤ 1) : Vi (pmat z) i / 2 * (1 - ep) ≤ Fi (pmat z) i := by
  have hr : 0 ≤ rhoP z := by
    unfold rhoP
    positivity
  rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi, ← lemma3d z hi]
  have h := lse_lower (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    (hr.trans h1) h2 (fun S => by
      have := abs_sum_pev_le z S.1
      unfold yS
      linarith)
  simpa only [one_mul] using h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem fi_upper {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (h1 : rhoP z ≤ 1) :
    Fi (pmat z) i ≤ Vi (pmat z) i := by
  rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi, ← lemma3d z hi]
  have h := lse_upper (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    (fun S => by
      have := abs_sum_pev_le z S.1
      unfold yS
      linarith)
  simpa only [one_mul] using h

end ReciprocityTheory.ChartRestriction.DS
