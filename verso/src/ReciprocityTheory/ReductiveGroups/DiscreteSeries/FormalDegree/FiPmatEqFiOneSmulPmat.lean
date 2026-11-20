import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.LseConvexOn

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Unfold `wS`. Check the signs of the components of the expression.
-/
theorem wS_nonneg' {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) : 0 ≤ wS z hi S := by
  unfold wS
  positivity

/- English proof (translation)
Unfold `Fi`. Rewrite using `[lemma3a z hi t]`. Use `congr 1`. Establish `h : (∑ S, ((wS z hi S : ℝ) : ℂ) * Complex.exp ((t * yS z S.1 : ℝ) : ℂ)) = ((∑ S, wS z hi S * Real.exp (t * yS z S.1) : ℝ) : ℂ)`. Use `push_cast`.

Simplify using `only [Complex.ofReal_exp, Complex.ofReal_mul]`. Rewrite using `[h, Complex.ofReal_re]`.
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
Rewrite using `[Complex.ofReal_one, one_smul]`.
-/
theorem fi_pmat_eq_fi_one_smul_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) :
    Fi (pmat z) i = Fi (((1 : ℝ) : ℂ) • pmat z) i := by
  rw [Complex.ofReal_one, one_smul]

/- English proof (translation)
Establish `h : (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) = fun t : ℝ => Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1))`. Use function extensionality and compare the values at `t`. Conclude with `fi_eq_lse z hi t`. Rewrite using `[h]`. Conclude with `lse_convexOn (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi)`.
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
Unfold `Fi Del`. Rewrite using `[NormedSpace.exp_zero]`. Use `split_ifs with h`. Rewrite using `[Matrix.submatrix_one _ (Fin.castLE_injective h)]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem fi_zero (i : ℕ) : Fi (0 : Matrix (Fin n) (Fin n) ℂ) i = 0 := by
  unfold Fi Del
  rw [NormedSpace.exp_zero]
  split_ifs with h
  · rw [Matrix.submatrix_one _ (Fin.castLE_injective h)]
    simp
  · simp

/- English proof (translation)
Distinguish the cases in `hi : i ≤ n`. Rewrite using `[fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi]`. Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `h` using `lse_one_le (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)`. Simplify `h` using `only [one_mul]`.

Unfold `Fi Del`. Rewrite using `[dif_neg hi]`. Simplify using the standard rewrite rules.
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
Establish `hr : 0 ≤ rhoP z`. Unfold `rhoP`. Check the signs of the components of the expression. Rewrite using `[fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi, ← lemma3d z hi]`. Establish `h` using `lse_lower (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi) (hr.trans h1) h2 (fun S => by`.

Use `abs_sum_pev_le z S.1` as an intermediate fact. Unfold `yS`. Use the proof step `linarith)`. Simplify `h` using `only [one_mul]`.
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
Rewrite using `[fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi, ← lemma3d z hi]`. Establish `h` using `lse_upper (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi) (fun S => by`. Use `abs_sum_pev_le z S.1` as an intermediate fact. Unfold `yS`. Use the proof step `linarith)`.

Simplify `h` using `only [one_mul]`.
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
