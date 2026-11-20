import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.GapSum

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem inP_apply_eq_zero {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inP ε Y) {a b : Fin n} (hab : ε a = ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hY.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul, hab] at h
  by_cases hb : ε b = true
  · simp only [hb, if_true] at h
    linear_combination h / 2
  · simp only [hb] at h
    simp only [Bool.false_eq_true, if_false] at h
    linear_combination -h / 2

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inP_norm_symm {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inP ε Y) (a b : Fin n) : ‖Y a b‖ = ‖Y b a‖ := by
  have h := congrFun (congrFun hY.1 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.add_apply, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Matrix.zero_apply] at h
  have h2 := congrArg norm (eq_neg_of_add_eq_zero_left h)
  rw [norm_neg, norm_mul, norm_mul, norm_star] at h2
  have e : ∀ c : Fin n, ‖(if ε c = true then (1 : ℂ) else -1)‖ = 1 := by
    intro c; split_ifs <;> simp
  rw [e, e] at h2
  linarith

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem telescope (L : ℕ → ℝ) (m a b : ℕ) (ha : a ≤ m) :
    ∑ i ∈ range m, (if i + 1 ≤ a ∧ b < i + 1 then L i - L (i + 1) + 1 else 0) =
      if b < a then L b - L a + ((a : ℝ) - b) else 0 := by
  rw [← Finset.sum_filter]
  have hf : (range m).filter (fun i => i + 1 ≤ a ∧ b < i + 1) = Finset.Ico b a := by
    ext i; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hf]
  split_ifs with hba
  · have hle : b ≤ a := hba.le
    clear hf ha hba
    induction a, hle using Nat.le_induction with
    | base => simp
    | succ k hk ih => rw [Finset.sum_Ico_succ_top hk, ih]; push_cast; ring
  · rw [Finset.Ico_eq_empty hba, Finset.sum_empty]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sum_symm_half {n : ℕ} (N : Fin n → Fin n → ℝ) (hs : ∀ a b, N a b = N b a)
    (h0 : ∀ a, N a a = 0) :
    ∑ a, ∑ b, N a b = 2 * ∑ a, ∑ b, if b < a then N a b else 0 := by
  have h1 : ∑ a, ∑ b, (if b < a then N a b else 0) = ∑ a, ∑ b, if a < b then N a b else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hs]
  rw [two_mul]
  nth_rewrite 2 [h1]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt]
  · subst h; simp [h0]
  · simp [h, h.not_gt]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem gap_mul_hs_le : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ), StrictAnti lam → GapAtLeast ε lam h → inP ε Y → h * hs Y / 2 ≤ ∑ i : Fin (n - 1), (lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1) * ∑ a : Fin n, ∑ b : Fin n, if i.val + 1 ≤ a.val ∧ b.val < i.val + 1 then ‖Y a b‖ ^ 2 else 0 := by
  intro n ε lam h Y hanti hgap hY
  let L : ℕ → ℝ := fun k => if hk : k < n then lam ⟨k, hk⟩ else 0
  have hL : ∀ a : Fin n, L a.val = lam a := fun a => by simp [L]
  have hR : (∑ i : Fin (n - 1), (lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1) *
      ∑ a : Fin n, ∑ b : Fin n, if i.val + 1 ≤ a.val ∧ b.val < i.val + 1 then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n,
        (if b.val < a.val then lam b - lam a + ((a.val : ℝ) - b.val) else 0) * ‖Y a b‖ ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hL a, ← hL b, ← telescope L (n - 1) a b (by omega), Finset.sum_mul,
      ← Fin.sum_univ_eq_sum_range (fun i => (if i + 1 ≤ a.val ∧ b.val < i + 1 then
        L i - L (i + 1) + 1 else 0) * ‖Y a b‖ ^ 2) (n - 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hL ⟨i.val, by omega⟩, ← hL ⟨i.val + 1, by omega⟩]
    split_ifs <;> simp
  rw [hR, hs, sum_symm_half (fun a b => ‖Y a b‖ ^ 2)
    (fun a b => by simp only [inP_norm_symm hY a b])
    (fun a => by simp [inP_apply_eq_zero hY (rfl : ε a = ε a)])]
  rw [show ∀ S : ℝ, h * (2 * S) / 2 = h * S from fun S => by ring, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hba : b < a
  · have hba' : b.val < a.val := hba
    rw [if_pos hba, if_pos hba']
    by_cases he : ε a = ε b
    · simp [inP_apply_eq_zero hY he]
    · have h1 := hgap a b he
      have h2 := hanti hba
      have h3 : (b.val : ℝ) < a.val := by exact_mod_cast hba'
      rw [abs_of_neg (by linarith)] at h1
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hba' : ¬ b.val < a.val := hba
    simp [hba, hba']

end GlobalTheory.GapSum
