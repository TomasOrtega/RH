import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

open Letters

/- English proof (translation)
Unfold `fT`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j hj`. Establish `hj1 : (0 : ℝ) < j` using `by exact_mod_cast (Finset.mem_Icc.mp hj).1`. Rewrite using `[zero_add, div_self hj1.ne', Real.log_one]`.
-/
theorem fT_zero (k' : ℕ) : fT k' 0 = 0 := by
  unfold fT
  apply Finset.sum_eq_zero
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  rw [zero_add, div_self hj1.ne', Real.log_one]

/- English proof (translation)
Unfold `fT`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`.
-/
theorem fT_succ (k' : ℕ) (y : ℝ) :
    fT (k' + 1) y = fT k' y + Real.log ((y + ((k' + 1 : ℕ) : ℝ)) / ((k' + 1 : ℕ) : ℝ)) := by
  unfold fT
  rw [Finset.sum_Icc_succ_top (by omega)]

/- English proof (translation)
Proceed by induction on `k' with`. Consider the case `zero => simp [fT]`. Consider the case `succ n ih`. Establish `hc : (0 : ℝ) < ((y + n).choose n : ℝ)`. Conclude with `Nat.choose_pos (Nat.le_add_left n y)` after adjusting the coercions.

Establish `hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)` using `by exact_mod_cast Nat.succ_pos n`. Establish `hy : (0 : ℝ) ≤ (y : ℝ)` using `Nat.cast_nonneg y`. Rewrite using `[fT_succ, ih, ← Real.log_mul hc.ne' (by positivity)]`. Use `congr 1`. Establish `h` using `Nat.add_one_mul_choose_eq (y + n) n`.

Establish `h' : (((y + n).succ : ℕ) : ℝ) * ((y + n).choose n : ℝ) = (((y + n).succ.choose n.succ : ℕ) : ℝ) * ((n.succ : ℕ) : ℝ)` using `by exact_mod_cast h`. Establish `e1 : (((y + n).succ : ℕ) : ℝ) = (y : ℝ) + ((n + 1 : ℕ) : ℝ)` using `by push_cast; ring`. Rewrite `h'` using `[e1]`. Establish `e2 : y + (n + 1) = (y + n).succ` using `rfl`. Rewrite using `[e2, mul_div_assoc', eq_comm, eq_div_iff hn.ne', ← h', mul_comm]`.
-/
theorem fT_nat (k' y : ℕ) : fT k' y = Real.log ((y + k').choose k') := by
  induction k' with
  | zero => simp [fT]
  | succ n ih =>
    have hc : (0 : ℝ) < ((y + n).choose n : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_left n y)
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    rw [fT_succ, ih, ← Real.log_mul hc.ne' (by positivity)]
    congr 1
    have h := Nat.add_one_mul_choose_eq (y + n) n
    have h' : (((y + n).succ : ℕ) : ℝ) * ((y + n).choose n : ℝ) =
        (((y + n).succ.choose n.succ : ℕ) : ℝ) * ((n.succ : ℕ) : ℝ) := by exact_mod_cast h
    have e1 : (((y + n).succ : ℕ) : ℝ) = (y : ℝ) + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1] at h'
    have e2 : y + (n + 1) = (y + n).succ := rfl
    rw [e2, mul_div_assoc', eq_comm, eq_div_iff hn.ne', ← h', mul_comm]

/- English proof (translation)
Establish `e : fT k' = fun y : ℝ => ∑ j ∈ Icc 1 k', Real.log ((y + j) / j)` using `rfl`. Rewrite using `[e]`. Unfold `fT'`. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises. Introduce `j hj`.

Establish `hj1 : (0 : ℝ) < j` using `by exact_mod_cast (Finset.mem_Icc.mp hj).1`. Establish `h1 : HasDerivAt (fun y : ℝ => (y + j) / j) (1 / j) y` using `((hasDerivAt_id y).add_const _).div_const _`. Establish `h2` using `h1.log (by positivity)`. Establish `e2 : 1 / (y + (j : ℝ)) = 1 / (j : ℝ) / ((y + j) / j)` using `(div_div_div_cancel_right₀ hj1.ne' _ _).symm`. Rewrite using `[e2]`.

Conclude with `h2`.
-/
theorem fT_hasDerivAt (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : HasDerivAt (fT k') (fT' k' y) y := by
  have e : fT k' = fun y : ℝ => ∑ j ∈ Icc 1 k', Real.log ((y + j) / j) := rfl
  rw [e]
  unfold fT'
  apply HasDerivAt.fun_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have h1 : HasDerivAt (fun y : ℝ => (y + j) / j) (1 / j) y :=
    ((hasDerivAt_id y).add_const _).div_const _
  have h2 := h1.log (by positivity)
  have e2 : 1 / (y + (j : ℝ)) = 1 / (j : ℝ) / ((y + j) / j) :=
    (div_div_div_cancel_right₀ hj1.ne' _ _).symm
  rw [e2]
  exact h2

/- English proof (translation)
Unfold `fT'`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `j _`. Check the signs of the components of the expression.
-/
theorem fT'_nonneg (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : 0 ≤ fT' k' y := by
  unfold fT'
  apply Finset.sum_nonneg
  intro j _
  positivity

/- English proof (translation)
Unfold `fT'`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j hj`. Establish `hj1 : (0 : ℝ) < j` using `by exact_mod_cast (Finset.mem_Icc.mp hj).1`. Apply `one_div_le_one_div_of_le (by positivity) (by linarith)` to reduce the goal to its premises.
-/
theorem fT'_anti (k' : ℕ) (y y' : ℝ) (hy : 0 ≤ y) (h : y ≤ y') : fT' k' y' ≤ fT' k' y := by
  unfold fT'
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

/- English proof (translation)
Unfold `fT'`. Establish `: (k' : ℝ) / (y + k') = ∑ _j ∈ Icc 1 k', 1 / (y + (k' : ℝ))`. Rewrite using `[Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]`. Simplify using `[div_eq_mul_inv]`. Rewrite using `[this]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j hj`. Establish `hj1 : (0 : ℝ) < j` using `by exact_mod_cast (Finset.mem_Icc.mp hj).1`. Establish `hj2 : (j : ℝ) ≤ k'` using `by exact_mod_cast (Finset.mem_Icc.mp hj).2`. Apply `one_div_le_one_div_of_le (by positivity) (by linarith)` to reduce the goal to its premises.
-/
theorem fT'_lower (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : (k' : ℝ) / (y + k') ≤ fT' k' y := by
  unfold fT'
  have : (k' : ℝ) / (y + k') = ∑ _j ∈ Icc 1 k', 1 / (y + (k' : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp [div_eq_mul_inv]
  rw [this]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hj2 : (j : ℝ) ≤ k' := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

/- English proof (translation)
Unfold `fT'`. Establish `: (k' : ℝ) / (y + 1) = ∑ _j ∈ Icc 1 k', 1 / (y + (1 : ℝ))`. Rewrite using `[Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]`. Simplify using `[div_eq_mul_inv]`. Rewrite using `[this]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j hj`. Establish `hj1 : (1 : ℝ) ≤ j` using `by exact_mod_cast (Finset.mem_Icc.mp hj).1`. Apply `one_div_le_one_div_of_le (by positivity) (by linarith)` to reduce the goal to its premises.
-/
theorem fT'_upper (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : fT' k' y ≤ (k' : ℝ) / (y + 1) := by
  unfold fT'
  have : (k' : ℝ) / (y + 1) = ∑ _j ∈ Icc 1 k', 1 / (y + (1 : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp [div_eq_mul_inv]
  rw [this]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

/- English proof (translation)
Establish `hk' : (0 : ℝ) < k'` using `by exact_mod_cast hk`. Conclude with `lt_of_lt_of_le (by positivity) (fT'_lower k' y hy)`.
-/
theorem fT'_pos (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) (hk : 1 ≤ k') : 0 < fT' k' y := by
  have hk' : (0 : ℝ) < k' := by exact_mod_cast hk
  exact lt_of_lt_of_le (by positivity) (fT'_lower k' y hy)

/- English proof (translation)
Establish `hk' : (0 : ℝ) < k'` using `by exact_mod_cast hk`. Use `le_trans ?_ (fT'_lower k' y (by linarith))` and prove the remaining obligations. Apply `div_le_div_of_nonneg_left hk'.le (by linarith) (by linarith)` to reduce the goal to its premises.
-/
theorem fT'_lower2 (k' : ℕ) (y : ℝ) (hy : (k' : ℝ) ≤ y) (hk : 1 ≤ k') :
    (k' : ℝ) / (2 * y) ≤ fT' k' y := by
  have hk' : (0 : ℝ) < k' := by exact_mod_cast hk
  refine le_trans ?_ (fT'_lower k' y (by linarith))
  apply div_le_div_of_nonneg_left hk'.le (by linarith) (by linarith)

/- English proof (translation)
Unfold `fT'`. Rewrite using `[Finset.sum_div]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j hj`. Establish `hj1 : (0 : ℝ) < j` using `by exact_mod_cast (Finset.mem_Icc.mp hj).1`.

Establish `hj2 : (j : ℝ) ≤ k'` using `by exact_mod_cast (Finset.mem_Icc.mp hj).2`. Establish `hy0 : 0 ≤ y` using `by linarith`. Rewrite using `[div_div]`. Apply `one_div_le_one_div_of_le (by positivity) (by linarith)` to reduce the goal to its premises.
-/
theorem fT'_half (k' : ℕ) (y y' : ℝ) (hy : (k' : ℝ) ≤ y) (h : 4 * y ≤ y') :
    fT' k' y' ≤ fT' k' y / 2 := by
  unfold fT'
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hj2 : (j : ℝ) ≤ k' := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  have hy0 : 0 ≤ y := by linarith
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

/- English proof (translation)
Unfold `fT fT'`. Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_mul]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j hj`. Establish `hj1 : (0 : ℝ) < j` using `by exact_mod_cast (Finset.mem_Icc.mp hj).1`.

Establish `hxj : 0 < x + j` using `by linarith`. Establish `hyj : 0 < y + j` using `by linarith`. Rewrite using `[← Real.log_div (by positivity) (by positivity)]`. Establish `e : (x + j) / j / ((y + j) / j) = (x + j) / (y + j)` using `by field_simp`. Rewrite using `[e]`.

Use `le_trans (Real.log_le_sub_one_of_pos (by positivity)) (le_of_eq ?_)` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fT_concave (k' : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    fT k' x - fT k' y ≤ fT' k' y * (x - y) := by
  unfold fT fT'
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hxj : 0 < x + j := by linarith
  have hyj : 0 < y + j := by linarith
  rw [← Real.log_div (by positivity) (by positivity)]
  have e : (x + j) / j / ((y + j) / j) = (x + j) / (y + j) := by field_simp
  rw [e]
  refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) (le_of_eq ?_)
  field_simp
  ring

/- English proof (translation)
Introduce `k'`. Conclude with `⟨fT_zero k', fT_nat k', fT_hasDerivAt k', fT'_pos k', fT'_anti k', fun y hy _ => ⟨fT'_lower k' y hy, fT'_upper k' y hy⟩, fT'_lower2 k', fT'_half k', fT_concave k'⟩`.
-/
theorem logBinomialProperties : LogBinomialProperties := by
  intro k'
  exact ⟨fT_zero k', fT_nat k', fT_hasDerivAt k', fT'_pos k', fT'_anti k',
    fun y hy _ => ⟨fT'_lower k' y hy, fT'_upper k' y hy⟩, fT'_lower2 k', fT'_half k', fT_concave k'⟩

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.sum_range_succ, ih]`. Simplify using the standard rewrite rules.
-/
theorem sum_incr (g : ℕ → ℝ) (L : ℕ) :
    ∑ u ∈ range (L + 1), (g u - (if u = 0 then 0 else g (u - 1))) = g L := by
  induction L with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h1 : ∑ u ∈ range (n + 1), (g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u (n + 1), d l = ∑ u ∈ range (n + 1), ((g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u n, d l + (g u - (if u = 0 then 0 else g (u - 1))) * d n)`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `u hu`. Establish `hu' : u ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)`. Rewrite using `[Finset.sum_Ico_succ_top hu', mul_add]`. Rewrite using `[h1, Finset.sum_add_distrib, ← Finset.sum_mul, sum_incr, Finset.sum_range_succ, Finset.sum_range_succ, ih]`. Simplify using the standard rewrite rules.
-/
theorem abel_tails (g d : ℕ → ℝ) (L : ℕ) :
    ∑ l ∈ range L, g l * d l =
      ∑ u ∈ range L, (g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u L, d l := by
  induction L with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ u ∈ range (n + 1), (g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u (n + 1), d l =
        ∑ u ∈ range (n + 1), ((g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u n, d l +
          (g u - (if u = 0 then 0 else g (u - 1))) * d n) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hu' : u ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
      rw [Finset.sum_Ico_succ_top hu', mul_add]
    rw [h1, Finset.sum_add_distrib, ← Finset.sum_mul, sum_incr, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    simp

/- English proof (translation)
Introduce `k' L al Bs hk hal hBs h4 hDe`. Establish `hk0 : (0 : ℝ) < k'` using `by exact_mod_cast hk`. Establish `hB0 : ∀ l, l < L → 0 ≤ Bs l` using `fun l hl => le_trans hk0.le (hBs l hl)`. Establish `hc : ∀ u, u < L → fT' k' (Bs u) / 2 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))`. Introduce `u hu`.

Establish `hn` using `fT'_nonneg k' (Bs u) (hB0 u hu)`. Distinguish the cases in `h0 : u = 0`. Rewrite using `[if_pos h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg h0]`.

Establish `e : u - 1 + 1 = u` using `Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)`. Establish `h` using `h4 (u - 1) (by rw [e]; exact hu)`. Rewrite `h` using `[e]`. Use `fT'_half k' (Bs u) (Bs (u - 1)) (hBs u hu) h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc0 : ∀ u, u < L → 0 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))`. Introduce `u hu`. Establish `hn` using `fT'_nonneg k' (Bs u) (hB0 u hu)`. Combine the linear relations using `[hc u hu]`. Establish `hmain : (∑ l ∈ range L, fT k' (al l)) - (∑ l ∈ range L, fT k' (Bs l)) ≤ ∑ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) * ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l))`.

Establish `h` using `abel_tails (fun l => fT' k' (Bs l)) (fun l => al l - Bs l) L`. Simplify using `only [Finset.sum_sub_distrib] at h`. Rewrite using `[← h, ← Finset.sum_sub_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `l hl`.

Conclude with `fT_concave k' (al l) (Bs l) (hal l) (hB0 l (Finset.mem_range.mp hl))`. Establish `hterm : ∀ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) * ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)) ≤ 0`. Introduce `u hu`. Establish `hu'` using `Finset.mem_range.mp hu`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (hc0 u hu') (hDe u hu')`.

Use `⟨hc, hmain, Finset.sum_nonpos hterm, ?_⟩` and prove the remaining obligations. Introduce `u₀ X hu₀ hX hdef`. Prove the components needed by the constructor for the conclusion. Use `le_trans hmain ?_` and prove the remaining obligations. Establish `h1` using `Finset.single_le_sum (f := fun u => -((fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) * ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)))) (fun u hu => neg_nonneg.mpr (hterm u hu)) (Finset.mem_range.mpr hu₀)`.

Rewrite `h1` using `[Finset.sum_neg_distrib]`. Establish `h2` using `mul_le_mul_of_nonneg_left hdef (hc0 u₀ hu₀)`. Establish `h3` using `mul_le_mul_of_nonneg_right (hc u₀ hu₀) hX`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `fT'_lower2 k' (Bs u₀) (hBs u₀ hu₀) hk`.

Establish `hBp : 0 < Bs u₀` using `lt_of_lt_of_le hk0 (hBs u₀ hu₀)`. Establish `e : X * k' / (4 * Bs u₀) = X * ((k' : ℝ) / (2 * Bs u₀)) / 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `mul_le_mul_of_nonneg_left h hX` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logBinomialDeficit : LogBinomialDeficit := by
  intro k' L al Bs hk hal hBs h4 hDe
  have hk0 : (0 : ℝ) < k' := by exact_mod_cast hk
  have hB0 : ∀ l, l < L → 0 ≤ Bs l := fun l hl => le_trans hk0.le (hBs l hl)
  have hc : ∀ u, u < L →
      fT' k' (Bs u) / 2 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1))) := by
    intro u hu
    have hn := fT'_nonneg k' (Bs u) (hB0 u hu)
    by_cases h0 : u = 0
    · rw [if_pos h0]; linarith
    · rw [if_neg h0]
      have e : u - 1 + 1 = u := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)
      have h := h4 (u - 1) (by rw [e]; exact hu)
      rw [e] at h
      have := fT'_half k' (Bs u) (Bs (u - 1)) (hBs u hu) h
      linarith
  have hc0 : ∀ u, u < L → 0 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1))) := by
    intro u hu
    have hn := fT'_nonneg k' (Bs u) (hB0 u hu)
    linarith [hc u hu]
  have hmain : (∑ l ∈ range L, fT k' (al l)) - (∑ l ∈ range L, fT k' (Bs l)) ≤
      ∑ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)) := by
    have h := abel_tails (fun l => fT' k' (Bs l)) (fun l => al l - Bs l) L
    simp only [Finset.sum_sub_distrib] at h
    rw [← h, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro l hl
    exact fT_concave k' (al l) (Bs l) (hal l) (hB0 l (Finset.mem_range.mp hl))
  have hterm : ∀ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)) ≤ 0 := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    exact mul_nonpos_of_nonneg_of_nonpos (hc0 u hu') (hDe u hu')
  refine ⟨hc, hmain, Finset.sum_nonpos hterm, ?_⟩
  intro u₀ X hu₀ hX hdef
  constructor
  · refine le_trans hmain ?_
    have h1 := Finset.single_le_sum
      (f := fun u => -((fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l))))
      (fun u hu => neg_nonneg.mpr (hterm u hu)) (Finset.mem_range.mpr hu₀)
    rw [Finset.sum_neg_distrib] at h1
    have h2 := mul_le_mul_of_nonneg_left hdef (hc0 u₀ hu₀)
    have h3 := mul_le_mul_of_nonneg_right (hc u₀ hu₀) hX
    linarith
  · have h := fT'_lower2 k' (Bs u₀) (hBs u₀ hu₀) hk
    have hBp : 0 < Bs u₀ := lt_of_lt_of_le hk0 (hBs u₀ hu₀)
    have e : X * k' / (4 * Bs u₀) = X * ((k' : ℝ) / (2 * Bs u₀)) / 2 := by
      field_simp
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h hX
    linarith

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hN : (1 : ℝ) ≤ ((k' + n + 1 : ℕ) : ℝ)` using `by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)`. Establish `hN0 : (0 : ℝ) < ((k' + n + 1 : ℕ) : ℝ)` using `by linarith`.

Establish `e : fT (k' + (n + 1)) y = fT (k' + n) y + Real.log ((y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ))` using `fT_succ (k' + n) y`. Establish `h1 : 1 ≤ (y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ)`. Rewrite using `[le_div_iff₀ hN0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ) ≤ 1 + y`.

Rewrite using `[div_le_iff₀ hN0]`. Use polynomial arithmetic with `[mul_nonneg hy (sub_nonneg.mpr hN)]`. Establish `l1` using `Real.log_nonneg h1`. Establish `l2` using `Real.log_le_log (by linarith) h2`. Establish `ec : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1` using `by push_cast; ring`.

Rewrite using `[e, ec]`. Prove the components needed by the constructor for the conclusion. Combine the linear relations using `[ih.1]`. Combine the linear relations using `[ih.2]`.
-/
theorem fT_add_bounds (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) (d : ℕ) :
    0 ≤ fT (k' + d) y - fT k' y ∧ fT (k' + d) y - fT k' y ≤ (d : ℝ) * Real.log (1 + y) := by
  induction d with
  | zero => simp
  | succ n ih =>
    have hN : (1 : ℝ) ≤ ((k' + n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hN0 : (0 : ℝ) < ((k' + n + 1 : ℕ) : ℝ) := by linarith
    have e : fT (k' + (n + 1)) y = fT (k' + n) y +
        Real.log ((y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ)) := fT_succ (k' + n) y
    have h1 : 1 ≤ (y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hN0]; linarith
    have h2 : (y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ) ≤ 1 + y := by
      rw [div_le_iff₀ hN0]
      nlinarith [mul_nonneg hy (sub_nonneg.mpr hN)]
    have l1 := Real.log_nonneg h1
    have l2 := Real.log_le_log (by linarith) h2
    have ec : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, ec]
    constructor
    · linarith [ih.1]
    · linarith [ih.2]

/- English proof (translation)
Introduce `D A0 hA0 hr hrN hK hB`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd, hdle⟩ : ∃ d : ℕ, D.k - 1 = D.k' + d ∧ d ≤ D.r + 2 * D.Ns := by`. Use `⟨D.r + 2 * D.Ns - 1, ?_, by omega⟩` and prove the remaining obligations. Unfold `Letters.k Letters.k'`. Use linear arithmetic over natural numbers and integers.

Establish `hk1 : 1 ≤ D.k` using `by unfold Letters.k; omega`. Establish `hlog : Real.log (D.rankAA : ℝ) = ∑ i ∈ Icc 1 D.n0, fT (D.k' + d) (D.B i)`. Unfold `Letters.rankAA`. Rewrite using `[Nat.cast_prod, Real.log_prod]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[fT_nat, ← hd]`. Establish `: D.B i + D.k - 1 = D.B i + (D.k - 1)` using `by omega`. Rewrite using `[this]`. Introduce `i _`.

Establish `: 0 < (D.B i + D.k - 1).choose (D.k - 1)` using `Nat.choose_pos (by omega)`. Conclude with `this.ne'` after adjusting the coercions. Rewrite using `[hlog, ← Finset.sum_sub_distrib]`. Establish `hl0 : 0 ≤ Real.log (1 + A0)` using `Real.log_nonneg (by linarith)`. Prove the components needed by the constructor for the conclusion.

Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `i _`. Conclude with `(fT_add_bounds D.k' (D.B i) (Nat.cast_nonneg _) d).1`. Establish `h1 : ∑ i ∈ Icc 1 D.n0, (fT (D.k' + d) (D.B i) - fT D.k' (D.B i)) ≤ ∑ _i ∈ Icc 1 D.n0, ((D.r : ℝ) + 2 * D.Ns) * Real.log (1 + A0)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i hi`. Establish `hi'` using `Finset.mem_Icc.mp hi`. Establish `hBi : (0 : ℝ) ≤ (D.B i : ℝ)` using `Nat.cast_nonneg _`. Use `le_trans (fT_add_bounds D.k' (D.B i) hBi d).2 ?_` and prove the remaining obligations. Establish `hdR : (d : ℝ) ≤ (D.r : ℝ) + 2 * D.Ns` using `by exact_mod_cast hdle`.

Establish `hll : Real.log (1 + (D.B i : ℝ)) ≤ Real.log (1 + A0)` using `Real.log_le_log (by linarith) (by linarith [hB i hi'.1 hi'.2])`. Conclude with `mul_le_mul hdR hll (Real.log_nonneg (by linarith)) (by positivity)`. Use `le_trans h1 ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_assoc]`. Establish `hn : ((D.n0 + 1 - 1 : ℕ) : ℝ) ≤ (D.Ns : ℝ)`.

Establish `: D.n0 + 1 - 1 ≤ D.Ns` using `by unfold Letters.n0; omega`. Conclude with `this` after adjusting the coercions. Conclude with `mul_le_mul_of_nonneg_right hn (by positivity)`.
-/
theorem logRankEstimate : LogRankEstimate := by
  intro D A0 hA0 hr hrN hK hB
  obtain ⟨d, hd, hdle⟩ : ∃ d : ℕ, D.k - 1 = D.k' + d ∧ d ≤ D.r + 2 * D.Ns := by
    refine ⟨D.r + 2 * D.Ns - 1, ?_, by omega⟩
    unfold Letters.k Letters.k'
    omega
  have hk1 : 1 ≤ D.k := by unfold Letters.k; omega
  have hlog : Real.log (D.rankAA : ℝ) = ∑ i ∈ Icc 1 D.n0, fT (D.k' + d) (D.B i) := by
    unfold Letters.rankAA
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [fT_nat, ← hd]
      have : D.B i + D.k - 1 = D.B i + (D.k - 1) := by omega
      rw [this]
    · intro i _
      have : 0 < (D.B i + D.k - 1).choose (D.k - 1) := Nat.choose_pos (by omega)
      exact_mod_cast this.ne'
  rw [hlog, ← Finset.sum_sub_distrib]
  have hl0 : 0 ≤ Real.log (1 + A0) := Real.log_nonneg (by linarith)
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact (fT_add_bounds D.k' (D.B i) (Nat.cast_nonneg _) d).1
  · have h1 : ∑ i ∈ Icc 1 D.n0, (fT (D.k' + d) (D.B i) - fT D.k' (D.B i)) ≤
        ∑ _i ∈ Icc 1 D.n0, ((D.r : ℝ) + 2 * D.Ns) * Real.log (1 + A0) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hBi : (0 : ℝ) ≤ (D.B i : ℝ) := Nat.cast_nonneg _
      refine le_trans (fT_add_bounds D.k' (D.B i) hBi d).2 ?_
      have hdR : (d : ℝ) ≤ (D.r : ℝ) + 2 * D.Ns := by exact_mod_cast hdle
      have hll : Real.log (1 + (D.B i : ℝ)) ≤ Real.log (1 + A0) :=
        Real.log_le_log (by linarith) (by linarith [hB i hi'.1 hi'.2])
      exact mul_le_mul hdR hll (Real.log_nonneg (by linarith)) (by positivity)
    refine le_trans h1 ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_assoc]
    have hn : ((D.n0 + 1 - 1 : ℕ) : ℝ) ≤ (D.Ns : ℝ) := by
      have : D.n0 + 1 - 1 ≤ D.Ns := by unfold Letters.n0; omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hn (by positivity)

end Formalism.InvariantFactorPaths.BranchingDimensions
