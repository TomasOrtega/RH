import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def nuNext (ν : Fin n → ℝ) (i : Fin n) : ℝ := if h : (i : ℕ) + 1 < n then ν ⟨(i : ℕ) + 1, h⟩ else 0

/- English proof (translation)
Establish `h` using `congrFun (congrFun hY.2 a) b`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, hab] at h`. Apply the tactic sequence `cases hb : ε b <;> simp [hb] at h <;> first | exact h | linear_combination h / 2 | linear_combination -h / 2`.
-/
lemma inP_entry_zero {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) {a b : Fin n}
    (hab : ε a = ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hY.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, hab] at h
  cases hb : ε b <;> simp [hb] at h <;>
    first | exact h | linear_combination h / 2 | linear_combination -h / 2

/- English proof (translation)
Establish `hJ : Jm ε * Jm ε = 1`. Rewrite using `[Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `a`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `h1 : Yᴴ * Jm ε = Y * Jm ε`. Rewrite using `[hY.2]`. Conclude with `eq_neg_of_add_eq_zero_left hY.1`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma conjTranspose_eq_self_of_mem_noncompactPart {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) : Yᴴ = Y := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    split_ifs <;> norm_num
  have h1 : Yᴴ * Jm ε = Y * Jm ε := by
    rw [hY.2]
    exact eq_neg_of_add_eq_zero_left hY.1
  calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Y * Jm ε * Jm ε := by rw [h1]
    _ = Y := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

/- English proof (translation)
Establish `h` using `congrFun (congrFun (conjTranspose_eq_self_of_mem_noncompactPart hY) b) a`. Rewrite using `[← h, Matrix.conjTranspose_apply, norm_star]`.
-/
lemma inP_norm_symm {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) (a b : Fin n) :
    ‖Y b a‖ = ‖Y a b‖ := by
  have h := congrFun (congrFun (conjTranspose_eq_self_of_mem_noncompactPart hY) b) a
  rw [← h, Matrix.conjTranspose_apply, norm_star]

/- English proof (translation)
Establish `hsplit : ∀ a b : Fin n, ‖Y a b‖ ^ 2 = (if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0)`. Introduce `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, not_lt.mpr h.le]`. Substitute `h` using the available equality.

Simplify using `[inP_entry_zero hY rfl]`. Simplify using `[h, not_lt.mpr h.le]`. Establish `hswap : (∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0) = ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[inP_norm_symm hY]`. Unfold `hs`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_add_distrib]`. Use `_ = _ := by rw [hswap]; ring`.
-/
lemma hs_eq_two_lower {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    hs Y = 2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by
  have hsplit : ∀ a b : Fin n, ‖Y a b‖ ^ 2 =
      (if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [inP_entry_zero hY rfl]
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [inP_norm_symm hY]
  unfold hs
  calc (∑ a : Fin n, ∑ b : Fin n, ‖Y a b‖ ^ 2)
      = ∑ a : Fin n, ∑ b : Fin n, ((if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b
    _ = (∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0) +
        ∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0 := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

/- English proof (translation)
Introduce `m hm`. Proceed by induction on `m, hm using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_Ico_tele (f : ℕ → ℝ) {b : ℕ} : ∀ m, b ≤ m → ∑ i ∈ Finset.Ico b m, (f i - f (i + 1)) = f b - f m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; ring

/- English proof (translation)
Set `f : ℕ → ℝ` to `fun k => if h : k < n then ν ⟨k, h⟩ else 0`. Establish `h1 : ∀ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) = (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then f i - f (i + 1) else 0)`. Introduce `i`. Simplify using `[f, nuNext, i.isLt]`. Rewrite using `[Finset.sum_congr rfl (fun i _ => h1 i), Fin.sum_univ_eq_sum_range (fun k => if (b : ℕ) ≤ k ∧ k < (a : ℕ) then f k - f (k + 1) else 0) n, ← Finset.sum_filter]`.

Establish `hfil : (Finset.range n).filter (fun k => (b : ℕ) ≤ k ∧ k < (a : ℕ)) = Finset.Ico (b : ℕ) a`. Use extensionality with `k`. Use `a.isLt` as an intermediate fact. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hfil, sum_Ico_tele f (b := (b : ℕ)) (a : ℕ) (Fin.lt_iff_val_lt_val.mp hba).le]`. Simplify using `[f, b.isLt, a.isLt]`.
-/
lemma nuNext_tele (ν : Fin n → ℝ) {a b : Fin n} (hba : b < a) :
    ∑ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) = ν b - ν a := by
  let f : ℕ → ℝ := fun k => if h : k < n then ν ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) =
      (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then f i - f (i + 1) else 0) := by
    intro i
    simp [f, nuNext, i.isLt]
  rw [Finset.sum_congr rfl (fun i _ => h1 i),
    Fin.sum_univ_eq_sum_range (fun k => if (b : ℕ) ≤ k ∧ k < (a : ℕ) then f k - f (k + 1) else 0) n,
    ← Finset.sum_filter]
  have hfil : (Finset.range n).filter (fun k => (b : ℕ) ≤ k ∧ k < (a : ℕ)) = Finset.Ico (b : ℕ) a := by
    ext k
    have := a.isLt
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfil, sum_Ico_tele f (b := (b : ℕ)) (a : ℕ) (Fin.lt_iff_val_lt_val.mp hba).le]
  simp [f, b.isLt, a.isLt]

/- English proof (translation)
Rewrite using `[hs_eq_two_lower hY]`. Establish `hR : ∑ i : Fin n, (ν i - nuNext ν i) * (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0) = ∑ a : Fin n, ∑ b : Fin n, if b < a then (ν b - ν a) * ‖Y a b‖ ^ 2 else 0`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with hba`. Rewrite using `[← nuNext_tele ν hba, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> ring`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Conclude with `hba (Fin.lt_iff_val_lt_val.mpr (lt_of_le_of_lt h.1 h.2))`.

Rewrite using `[hR]`. Establish `hL : g * (2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0) / 2 = ∑ a : Fin n, ∑ b : Fin n, if b < a then g * ‖Y a b‖ ^ 2 else 0`. Establish `hg' : ∀ a b : Fin n, (if b < a then g * ‖Y a b‖ ^ 2 else 0) = g * (if b < a then ‖Y a b‖ ^ 2 else 0)`. Apply the tactic sequence `intro a b; split_ifs <;> simp`. Repeatedly rewrite using `[hg', ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL]`. Use `Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with hba`. Distinguish the cases in `hε : ε a = ε b`.

Rewrite using `[inP_entry_zero hY hε]`. Simplify using the standard rewrite rules. Conclude with `mul_le_mul_of_nonneg_right (hg a b hε hba) (by positivity)`. Conclude with `le_rfl`.
-/
theorem dec_weighted {ε : Fin n → Bool} (ν : Fin n → ℝ) (hν : Antitone ν) {g : ℝ}
    (hg : ∀ a b : Fin n, ε a ≠ ε b → b < a → g ≤ ν b - ν a) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    g * hs Y / 2 ≤
      ∑ i : Fin n, (ν i - nuNext ν i) *
        (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0) := by
  rw [hs_eq_two_lower hY]
  have hR : ∑ i : Fin n, (ν i - nuNext ν i) *
      (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then (ν b - ν a) * ‖Y a b‖ ^ 2 else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hba
    · rw [← nuNext_tele ν hba, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg, mul_zero]
      intro h
      exact hba (Fin.lt_iff_val_lt_val.mpr (lt_of_le_of_lt h.1 h.2))
  rw [hR]
  have hL : g * (2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0) / 2 =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then g * ‖Y a b‖ ^ 2 else 0 := by
    have hg' : ∀ a b : Fin n, (if b < a then g * ‖Y a b‖ ^ 2 else 0) =
        g * (if b < a then ‖Y a b‖ ^ 2 else 0) := by
      intro a b; split_ifs <;> simp
    simp_rw [hg', ← Finset.mul_sum]
    ring
  rw [hL]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  split_ifs with hba
  · by_cases hε : ε a = ε b
    · rw [inP_entry_zero hY hε]; simp
    · exact mul_le_mul_of_nonneg_right (hg a b hε hba) (by positivity)
  · exact le_rfl

end ReciprocityTheory.ChartRestriction.DS.S7
