import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem succAbove_val {n : ℕ} (p : Fin (n + 1)) (l : Fin n) :
    (p.succAbove l).val = if l.val < p.val then l.val else l.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def] <;> omega

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem zb_det (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) :
    (Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val).det = h.det * t ^ s * sgnW s := by
  induction s with
  | zero =>
    have hs : sgnW 0 = 1 := by simp [sgnW]
    rw [hs, pow_zero, mul_one, mul_one]
    show Matrix.det (Matrix.of fun a b : Fin i0 => Zb i0 0 h t a.val b.val) = _
    congr 1
    ext a b
    simp [Zb, a.isLt, b.isLt]
  | succ s ih =>
    rw [Matrix.det_succ_row _ (⟨i0, by omega⟩ : Fin (i0 + s + 1)), Finset.sum_eq_single (Fin.last _)]
    · have hsub : (Matrix.of fun a b : Fin (i0 + (s + 1)) => Zb i0 (s + 1) h t a.val b.val).submatrix
          (⟨i0, by omega⟩ : Fin (i0 + s + 1)).succAbove (Fin.last (i0 + s)).succAbove =
          Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, succAbove_val, Fin.succAbove_last,
          Fin.coe_castSucc]
        have hb := b.isLt
        by_cases ha : (a : ℕ) < i0
        · simp only [ha, if_true]
          unfold Zb
          split_ifs <;> first | rfl | omega
        · simp only [ha, if_false]
          unfold Zb
          split_ifs <;> first | rfl | omega
      rw [hsub, ih, sgnW_succ']
      have he : Zb i0 (s + 1) h t i0 (i0 + s) = t := by
        simp only [Zb]
        rw [dif_neg (lt_irrefl _), if_pos (by omega)]
      simp only [Matrix.of_apply, Fin.val_last]
      rw [he]
      rw [show i0 + (i0 + s) = 2 * i0 + s by ring, pow_add, pow_mul]
      norm_num
      ring
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i0 + s := fun e => hj (Fin.ext (by simp [e]))
      have he : Zb i0 (s + 1) h t i0 j = 0 := by
        have := j.isLt
        simp only [Zb]
        rw [dif_neg (lt_irrefl _), if_neg (by omega)]
      simp only [Matrix.of_apply]
      rw [he, mul_zero, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules.
-/
theorem derivative_leading_zb : DleadZb := by
  intro i0 s h t
  refine ⟨?_, zb_det i0 s h t⟩
  unfold Dlead
  congr 1
  ext a b
  simp [Zb, a.isLt, b.isLt]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem minors_first_case : MinorsFirstCase := by
  intro i0 s' h t c
  by_cases hc : c.val = i0
  · rw [if_pos hc, ← zb_det i0 s' h t]
    congr 1
    ext a l
    simp only [Matrix.of_apply, succAbove_val, hc]
    have hl := l.isLt
    by_cases hl0 : (l : ℕ) < i0
    · simp only [hl0, if_true]
      unfold Zb
      split_ifs <;> first | rfl | omega
    · simp only [hl0, if_false]
      unfold Zb
      split_ifs <;> first | rfl | omega
  · rw [if_neg hc]
    have hne : (⟨i0, by omega⟩ : Fin (i0 + s' + 1)) ≠ c := fun e => hc (by rw [← e])
    obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hne
    apply Matrix.det_eq_zero_of_column_eq_zero l0
    intro a
    simp only [Matrix.of_apply, hl0]
    have ha := a.isLt
    unfold Zb
    split_ifs <;> first | rfl | omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem third_polynomial_expansion : MinorsThirdCase := by
  intro i0 s'' h t
  rw [← zb_det i0 s'' h t]
  congr 1
  ext a b
  simp only [Matrix.of_apply, succAbove_val]
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha0 : (a : ℕ) < i0 <;> by_cases hb0 : (b : ℕ) < i0 <;>
    simp only [ha0, hb0, if_true, if_false] <;>
    unfold Zb <;> split_ifs <;> first | rfl | omega

end Formalism.FourierDecayAlt.P.SignAntidiagonal
