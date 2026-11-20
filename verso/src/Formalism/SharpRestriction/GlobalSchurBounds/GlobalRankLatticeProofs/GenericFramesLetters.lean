import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace PrimeReciprocalSums

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp [Finset.Icc_eq_empty_of_lt]`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]`. Use `push_cast`.

Establish `hn : (0 : ℝ) ≤ (n : ℝ)` using `Nat.cast_nonneg n`. Establish `e : 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) - 1 / ((n : ℝ) + 1) ^ 2 = (n : ℝ) / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2))`. Apply the tactic sequence `field_simp <;> ring`. Establish `t : 0 ≤ (n : ℝ) / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2))` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem sum_Icc_inv_sq_le_two_sub (N : ℕ) :
    ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp [Finset.Icc_eq_empty_of_lt]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    push_cast
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have e : 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) - 1 / ((n : ℝ) + 1) ^ 2
        = (n : ℝ) / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by
      field_simp <;> ring
    have t : 0 ≤ (n : ℝ) / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by positivity
    linarith

/- English proof (translation)
Establish `h` using `sum_Icc_inv_sq_le_two_sub N`. Establish `h2 : 0 ≤ 2 / ((N : ℝ) + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_inv_sq_le (N : ℕ) : ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 2 := by
  have h := sum_Icc_inv_sq_le_two_sub N
  have h2 : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
  linarith

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hxne : x ≠ 0` using `hx0.ne'`. Establish `hL : 0 ≤ Real.log (x + 1)` using `Real.log_nonneg (by linarith)`. Establish `hl : Real.log (x + 1) ≤ Real.log x + 1 / x`. Establish `h1` using `Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < x + 1) hx0)`.

Rewrite `h1` using `[Real.log_div (by linarith : (0 : ℝ) < x + 1).ne' hxne]`. Establish `e : (x + 1) / x = 1 + 1 / x` using `by rw [add_div, div_self hxne]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx1 : x + 1 ≠ 0` using `(by linarith : (0 : ℝ) < x + 1).ne'`. Establish `e : (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) - Real.log (x + 1) / (x + 1) ^ 2 = (Real.log x - Real.log (x + 1) + 1 / x) / x + Real.log (x + 1) / (x * (x + 1) ^ 2) + (x - 1) / (x ^ 2 * (x + 1))`.

Apply the tactic sequence `field_simp <;> ring`. Establish `t1 : 0 ≤ (Real.log x - Real.log (x + 1) + 1 / x) / x` using `div_nonneg (by linarith) hx0.le`. Establish `t2 : 0 ≤ Real.log (x + 1) / (x * (x + 1) ^ 2)` using `div_nonneg hL (mul_nonneg hx0.le (sq_nonneg (x + 1)))`. Establish `t3 : 0 ≤ (x - 1) / (x ^ 2 * (x + 1))` using `div_nonneg (by linarith) (mul_nonneg (sq_nonneg x) (by linarith))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_step (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤
      (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hL : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hl : Real.log (x + 1) ≤ Real.log x + 1 / x := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < x + 1) hx0)
    rw [Real.log_div (by linarith : (0 : ℝ) < x + 1).ne' hxne] at h1
    have e : (x + 1) / x = 1 + 1 / x := by rw [add_div, div_self hxne]
    linarith
  have hx1 : x + 1 ≠ 0 := (by linarith : (0 : ℝ) < x + 1).ne'
  have e : (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) - Real.log (x + 1) / (x + 1) ^ 2
      = (Real.log x - Real.log (x + 1) + 1 / x) / x + Real.log (x + 1) / (x * (x + 1) ^ 2)
        + (x - 1) / (x ^ 2 * (x + 1)) := by
    field_simp <;> ring
  have t1 : 0 ≤ (Real.log x - Real.log (x + 1) + 1 / x) / x := div_nonneg (by linarith) hx0.le
  have t2 : 0 ≤ Real.log (x + 1) / (x * (x + 1) ^ 2) :=
    div_nonneg hL (mul_nonneg hx0.le (sq_nonneg (x + 1)))
  have t3 : 0 ≤ (x - 1) / (x ^ 2 * (x + 1)) :=
    div_nonneg (by linarith) (mul_nonneg (sq_nonneg x) (by linarith))
  linarith

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => norm_num`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1)]`. Establish `h` using `log_step ((n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem sum_Icc_log_div_sq_le_two_sub (N : ℕ) :
    ∑ q ∈ Finset.Icc 1 (N + 1), Real.log q / (q : ℝ) ^ 2 ≤
      2 - (Real.log ((N : ℝ) + 1) + 2) / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1)]
    have h := log_step ((n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    push_cast
    linarith

/- English proof (translation)
Break down `N with _ | k` into its components or cases. Simplify using `[Finset.Icc_eq_empty_of_lt]`. Establish `h` using `sum_Icc_log_div_sq_le_two_sub k`. Establish `hk : (0 : ℝ) ≤ (k : ℝ)` using `Nat.cast_nonneg k`. Establish `h1 : 0 ≤ Real.log ((k : ℝ) + 1)` using `Real.log_nonneg (by linarith)`.

Establish `h2 : 0 ≤ (Real.log ((k : ℝ) + 1) + 2) / ((k : ℝ) + 1)` using `div_nonneg (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_sq_le (N : ℕ) : ∑ q ∈ Finset.Icc 1 N, Real.log q / (q : ℝ) ^ 2 ≤ 2 := by
  rcases N with _ | k
  · simp [Finset.Icc_eq_empty_of_lt]
  · have h := sum_Icc_log_div_sq_le_two_sub k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ (Real.log ((k : ℝ) + 1) + 2) / ((k : ℝ) + 1) :=
      div_nonneg (by linarith) (by linarith)
    linarith

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hy1 : (0 : ℝ) < y + 1` using `by linarith`. Establish `h1` using `Real.log_le_sub_one_of_pos (div_pos hy0 hy1)`. Rewrite `h1` using `[Real.log_div hy0.ne' hy1.ne']`. Establish `e : y / (y + 1) = 1 - 1 / (y + 1)`.

Rewrite using `[eq_sub_iff_add_eq, ← add_div, div_self hy1.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem inv_succ_le_log_succ_sub_log (y : ℝ) (hy : 1 ≤ y) :
    1 / (y + 1) ≤ Real.log (y + 1) - Real.log y := by
  have hy0 : 0 < y := by linarith
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hy0 hy1)
  rw [Real.log_div hy0.ne' hy1.ne'] at h1
  have e : y / (y + 1) = 1 - 1 / (y + 1) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_self hy1.ne']
  linarith

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => norm_num`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1)]`. Establish `h` using `inv_succ_le_log_succ_sub_log ((n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ q ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / (q : ℝ) ≤ 1 + Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1)]
    have h := inv_succ_le_log_succ_sub_log ((n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    push_cast
    linarith

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, N = k + 1` from `⟨N - 1, by omega⟩`. Conclude with `sum_Icc_inv_le_one_add_log k` after adjusting the coercions.
-/
theorem sum_inv_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ≤ 1 + Real.log N := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  exact_mod_cast sum_Icc_inv_le_one_add_log k

/- English proof (translation)
Establish `hm0 : 0 < m` using `by omega`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not S (fun l => l % m = 1)]`. Establish `hG2 : ∑ q ∈ Finset.Icc 1 N, G q + ∑ q ∈ Finset.Icc 1 N, G q = 2 * ∑ q ∈ Finset.Icc 1 N, G q` using `by ring`. Rewrite using `[← hG2]`. Apply `add_le_add` to reduce the goal to its premises.

Establish `hq : ∀ l ∈ S.filter (fun l => l % m = 1), l = m * (l / m) + 1 ∧ 1 ≤ l / m ∧ l / m ≤ N`. Introduce `l hl`. Take `⟨hlS, hl1⟩` from `Finset.mem_filter.mp hl`. Take `⟨h2, hN, -⟩` from `hS l hlS`. Establish `hd` using `Nat.div_add_mod l m`.

Rewrite `hd` using `[hl1]`. Use `⟨hd.symm, ?_, le_trans (Nat.div_le_self l m) hN⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (l / m) with h0 | h0` into its components or cases. Rewrite `hd` using `[h0, mul_zero]`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `l hl`. Take `⟨he, h1, -⟩` from `hq l hl`.

Conclude with `hFG l (Finset.mem_filter.mp hl).1 (l / m) h1 (Or.inl he)`. Use `_ = ∑ q ∈ (S.filter (fun l => l % m = 1)).image (fun l => l / m), G q := by`. Rewrite using `[Finset.sum_image]`. Introduce `a ha b hb hab`. Establish `hab' : a / m = b / m` using `hab`.

Establish `ha'` using `(hq a ha).1`. Establish `hb'` using `(hq b hb).1`. Rewrite using `[ha', hb', hab']`. Use `_ ≤ ∑ q ∈ Finset.Icc 1 N, G q := by`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises.

Introduce `q hqi`. Take `⟨l, hl, rfl⟩` from `Finset.mem_image.mp hqi`. Take `⟨-, h1, h2⟩` from `hq l hl`. Conclude with `Finset.mem_Icc.mpr ⟨h1, h2⟩`. Introduce `q _ _`.

Conclude with `hG0 q`. Establish `hq : ∀ l ∈ S.filter (fun l => ¬ l % m = 1), l + 1 = m * ((l + 1) / m) ∧ 1 ≤ (l + 1) / m ∧ (l + 1) / m ≤ N`. Introduce `l hl`. Take `⟨hlS, hn1⟩` from `Finset.mem_filter.mp hl`. Take `⟨h2, hN, hor⟩` from `hS l hlS`.

Establish `hmod : (l + 1) % m = 0`. Break down `hor with h | h` into its components or cases. Conclude with `absurd h hn1`. Conclude with `h`. Establish `hd` using `Nat.div_add_mod (l + 1) m`.

Rewrite `hd` using `[hmod, add_zero]`. Establish `h4` using `Nat.mul_le_mul_right ((l + 1) / m) hm`. Use `⟨hd.symm, ?_, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos ((l + 1) / m) with h0 | h0` into its components or cases. Rewrite `hd` using `[h0, mul_zero]`.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `first | omega | linarith`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `l hl`. Take `⟨he, h1, -⟩` from `hq l hl`. Conclude with `hFG l (Finset.mem_filter.mp hl).1 ((l + 1) / m) h1 (Or.inr he)`. Use `_ = ∑ q ∈ (S.filter (fun l => ¬ l % m = 1)).image (fun l => (l + 1) / m), G q := by`. Rewrite using `[Finset.sum_image]`.

Introduce `a ha b hb hab`. Establish `hab' : (a + 1) / m = (b + 1) / m` using `hab`. Establish `ha'` using `(hq a ha).1`. Establish `hb'` using `(hq b hb).1`. Rewrite `ha'` using `[hab']`.

Apply the tactic sequence `first | omega | linarith`. Use `_ ≤ ∑ q ∈ Finset.Icc 1 N, G q := by`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `q hqi`. Take `⟨l, hl, rfl⟩` from `Finset.mem_image.mp hqi`.

Take `⟨-, h1, h2⟩` from `hq l hl`. Conclude with `Finset.mem_Icc.mpr ⟨h1, h2⟩`. Introduce `q _ _`. Conclude with `hG0 q`.
-/
theorem sum_split (m : ℕ) (hm : 4 ≤ m) (S : Finset ℕ) (N : ℕ)
    (hS : ∀ l ∈ S, 2 ≤ l ∧ l ≤ N ∧ (l % m = 1 ∨ (l + 1) % m = 0))
    (F G : ℕ → ℝ) (hG0 : ∀ q, 0 ≤ G q)
    (hFG : ∀ l ∈ S, ∀ q : ℕ, 1 ≤ q → (l = m * q + 1 ∨ l + 1 = m * q) → F l ≤ G q) :
    ∑ l ∈ S, F l ≤ 2 * ∑ q ∈ Finset.Icc 1 N, G q := by
  classical
  have hm0 : 0 < m := by omega
  rw [← Finset.sum_filter_add_sum_filter_not S (fun l => l % m = 1)]
  have hG2 : ∑ q ∈ Finset.Icc 1 N, G q + ∑ q ∈ Finset.Icc 1 N, G q
      = 2 * ∑ q ∈ Finset.Icc 1 N, G q := by ring
  rw [← hG2]
  apply add_le_add
  · have hq : ∀ l ∈ S.filter (fun l => l % m = 1), l = m * (l / m) + 1 ∧ 1 ≤ l / m ∧ l / m ≤ N := by
      intro l hl
      obtain ⟨hlS, hl1⟩ := Finset.mem_filter.mp hl
      obtain ⟨h2, hN, -⟩ := hS l hlS
      have hd := Nat.div_add_mod l m
      rw [hl1] at hd
      refine ⟨hd.symm, ?_, le_trans (Nat.div_le_self l m) hN⟩
      rcases Nat.eq_zero_or_pos (l / m) with h0 | h0
      · rw [h0, mul_zero] at hd
        omega
      · omega
    calc ∑ l ∈ S.filter (fun l => l % m = 1), F l
        ≤ ∑ l ∈ S.filter (fun l => l % m = 1), G (l / m) := by
          apply Finset.sum_le_sum
          intro l hl
          obtain ⟨he, h1, -⟩ := hq l hl
          exact hFG l (Finset.mem_filter.mp hl).1 (l / m) h1 (Or.inl he)
      _ = ∑ q ∈ (S.filter (fun l => l % m = 1)).image (fun l => l / m), G q := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          have hab' : a / m = b / m := hab
          have ha' := (hq a ha).1
          have hb' := (hq b hb).1
          rw [ha', hb', hab']
      _ ≤ ∑ q ∈ Finset.Icc 1 N, G q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hqi
            obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hqi
            obtain ⟨-, h1, h2⟩ := hq l hl
            exact Finset.mem_Icc.mpr ⟨h1, h2⟩
          · intro q _ _
            exact hG0 q
  · have hq : ∀ l ∈ S.filter (fun l => ¬ l % m = 1),
        l + 1 = m * ((l + 1) / m) ∧ 1 ≤ (l + 1) / m ∧ (l + 1) / m ≤ N := by
      intro l hl
      obtain ⟨hlS, hn1⟩ := Finset.mem_filter.mp hl
      obtain ⟨h2, hN, hor⟩ := hS l hlS
      have hmod : (l + 1) % m = 0 := by
        rcases hor with h | h
        · exact absurd h hn1
        · exact h
      have hd := Nat.div_add_mod (l + 1) m
      rw [hmod, add_zero] at hd
      have h4 := Nat.mul_le_mul_right ((l + 1) / m) hm
      refine ⟨hd.symm, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos ((l + 1) / m) with h0 | h0
        · rw [h0, mul_zero] at hd
          omega
        · omega
      · first | omega | linarith
    calc ∑ l ∈ S.filter (fun l => ¬ l % m = 1), F l
        ≤ ∑ l ∈ S.filter (fun l => ¬ l % m = 1), G ((l + 1) / m) := by
          apply Finset.sum_le_sum
          intro l hl
          obtain ⟨he, h1, -⟩ := hq l hl
          exact hFG l (Finset.mem_filter.mp hl).1 ((l + 1) / m) h1 (Or.inr he)
      _ = ∑ q ∈ (S.filter (fun l => ¬ l % m = 1)).image (fun l => (l + 1) / m), G q := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          have hab' : (a + 1) / m = (b + 1) / m := hab
          have ha' := (hq a ha).1
          have hb' := (hq b hb).1
          rw [hab'] at ha'
          first | omega | linarith
      _ ≤ ∑ q ∈ Finset.Icc 1 N, G q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hqi
            obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hqi
            obtain ⟨-, h1, h2⟩ := hq l hl
            exact Finset.mem_Icc.mpr ⟨h1, h2⟩
          · intro q _ _
            exact hG0 q

/- English proof (translation)
Establish `hm' : (4 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hq' : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hP : (4 : ℝ) ≤ (m : ℝ) * q` using `by nlinarith`. Break down `h with h | h` into its components or cases. Establish `hl : (l : ℝ) = (m : ℝ) * q + 1` using `by exact_mod_cast h`.

Apply the tactic sequence `constructor <;> linarith`. Establish `hl : (l : ℝ) + 1 = (m : ℝ) * q` using `by exact_mod_cast h`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem size_of_form (m q l : ℕ) (hm : 4 ≤ m) (hq : 1 ≤ q) (h : l = m * q + 1 ∨ l + 1 = m * q) :
    (3 / 4 : ℝ) * ((m : ℝ) * q) ≤ l ∧ (l : ℝ) ≤ 2 * ((m : ℝ) * q) := by
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP : (4 : ℝ) ≤ (m : ℝ) * q := by nlinarith
  rcases h with h | h
  · have hl : (l : ℝ) = (m : ℝ) * q + 1 := by exact_mod_cast h
    constructor <;> linarith
  · have hl : (l : ℝ) + 1 = (m : ℝ) * q := by exact_mod_cast h
    constructor <;> linarith

/- English proof (translation)
Establish `hL : 0 < L` using `lt_of_lt_of_le hc hcL`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem div_sq_le_div_sq_of_le_of_le (a A c L : ℝ) (hA : 0 ≤ A) (haA : a ≤ A) (hc : 0 < c)
    (hcL : c ≤ L) : a / L ^ 2 ≤ A / c ^ 2 := by
  have hL : 0 < L := lt_of_lt_of_le hc hcL
  calc a / L ^ 2 ≤ A / L ^ 2 := by gcongr
    _ ≤ A / c ^ 2 := by gcongr

/- English proof (translation)
Establish `hm0 : (0 : ℝ) < m`. Establish `: (4 : ℝ) ≤ m` using `by exact_mod_cast hm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm4' : (4 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hB : 0 ≤ Real.log 2 + Real.log m` using `add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by linarith))`.

Use `set N := S.sup id with hNdef`. Establish `hS' : ∀ l ∈ S, 2 ≤ l ∧ l ≤ N ∧ (l % m = 1 ∨ (l + 1) % m = 0)`. Introduce `l hl`. Conclude with `⟨(hS l hl).1, Finset.le_sup (f := id) hl, (hS l hl).2⟩`. Establish `hG0 : ∀ q : ℕ, 0 ≤ 16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2)`.

Introduce `q`. Apply `mul_nonneg (by positivity)` to reduce the goal to its premises. Conclude with `add_nonneg (div_nonneg hB (sq_nonneg _)) (div_nonneg (Real.log_natCast_nonneg q) (sq_nonneg _))`. Establish `hFG : ∀ l ∈ S, ∀ q : ℕ, 1 ≤ q → (l = m * q + 1 ∨ l + 1 = m * q) → Real.log l / (l : ℝ) ^ 2 ≤ 16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2)`. Introduce `l hl q hq hlq`.

Establish `hsz` using `size_of_form m q l hm hq hlq`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hmne : (m : ℝ) ≠ 0` using `hm0.ne'`. Establish `hqne : (q : ℝ) ≠ 0` using `hq0.ne'`. Establish `hc : (0 : ℝ) < (3 / 4 : ℝ) * ((m : ℝ) * q)` using `by positivity`.

Establish `hl1 : (1 : ℝ) ≤ l`. Establish `: (2 : ℝ) ≤ l` using `by exact_mod_cast (hS l hl).1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog : Real.log l ≤ Real.log 2 + Real.log m + Real.log q`. Rewrite using `[← Real.log_mul (by norm_num) hm0.ne', ← Real.log_mul (mul_pos (by norm_num) hm0).ne' hq0.ne']`.

Conclude with `Real.log_le_log (by linarith) (by linarith [hsz.2])`. Establish `hA : 0 ≤ Real.log 2 + Real.log m + Real.log q` using `le_trans (Real.log_nonneg hl1) hlog`. Establish `h1` using `div_sq_le_div_sq_of_le_of_le _ _ _ _ hA hlog hc hsz.1`. Establish `e : (Real.log 2 + Real.log m + Real.log q) / ((3 / 4 : ℝ) * ((m : ℝ) * q)) ^ 2 = 16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2)`. Apply the tactic sequence `field_simp <;> ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `sum_split m hm S N hS' (fun l => Real.log l / (l : ℝ) ^ 2) (fun q => 16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2)) hG0 hFG`. Apply the tactic sequence `try simp only at h`. Establish `hsum : ∑ q ∈ Finset.Icc 1 N, 16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2) = 16 / 9 / (m : ℝ) ^ 2 * (Real.log 2 + Real.log m) * ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ^ 2 + 16 / 9 / (m : ℝ) ^ 2 * ∑ q ∈ Finset.Icc 1 N, Real.log q / (q …`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `q _`. Expand and normalize the polynomial expressions, which then agree. Establish `hc1 : (0 : ℝ) ≤ 16 / 9 / (m : ℝ) ^ 2` using `by positivity`. Establish `i1` using `mul_le_mul_of_nonneg_left (sum_inv_sq_le N) (mul_nonneg hc1 hB)`.

Establish `i2` using `mul_le_mul_of_nonneg_left (sum_log_sq_le N) hc1`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_sq_bound (m : ℕ) (hm : 4 ≤ m) (S : Finset ℕ)
    (hS : ∀ l ∈ S, 2 ≤ l ∧ (l % m = 1 ∨ (l + 1) % m = 0)) :
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤
      2 * (16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) * 2 + 2)) := by
  classical
  have hm0 : (0 : ℝ) < m := by
    have : (4 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hm4' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hB : 0 ≤ Real.log 2 + Real.log m :=
    add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by linarith))
  set N := S.sup id with hNdef
  have hS' : ∀ l ∈ S, 2 ≤ l ∧ l ≤ N ∧ (l % m = 1 ∨ (l + 1) % m = 0) := by
    intro l hl
    exact ⟨(hS l hl).1, Finset.le_sup (f := id) hl, (hS l hl).2⟩
  have hG0 : ∀ q : ℕ, 0 ≤ 16 / 9 / (m : ℝ) ^ 2 *
      ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2) := by
    intro q
    apply mul_nonneg (by positivity)
    exact add_nonneg (div_nonneg hB (sq_nonneg _)) (div_nonneg (Real.log_natCast_nonneg q) (sq_nonneg _))
  have hFG : ∀ l ∈ S, ∀ q : ℕ, 1 ≤ q → (l = m * q + 1 ∨ l + 1 = m * q) →
      Real.log l / (l : ℝ) ^ 2 ≤ 16 / 9 / (m : ℝ) ^ 2 *
        ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2) := by
    intro l hl q hq hlq
    have hsz := size_of_form m q l hm hq hlq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hmne : (m : ℝ) ≠ 0 := hm0.ne'
    have hqne : (q : ℝ) ≠ 0 := hq0.ne'
    have hc : (0 : ℝ) < (3 / 4 : ℝ) * ((m : ℝ) * q) := by positivity
    have hl1 : (1 : ℝ) ≤ l := by
      have : (2 : ℝ) ≤ l := by exact_mod_cast (hS l hl).1
      linarith
    have hlog : Real.log l ≤ Real.log 2 + Real.log m + Real.log q := by
      rw [← Real.log_mul (by norm_num) hm0.ne', ← Real.log_mul (mul_pos (by norm_num) hm0).ne' hq0.ne']
      exact Real.log_le_log (by linarith) (by linarith [hsz.2])
    have hA : 0 ≤ Real.log 2 + Real.log m + Real.log q := le_trans (Real.log_nonneg hl1) hlog
    have h1 := div_sq_le_div_sq_of_le_of_le _ _ _ _ hA hlog hc hsz.1
    have e : (Real.log 2 + Real.log m + Real.log q) / ((3 / 4 : ℝ) * ((m : ℝ) * q)) ^ 2
        = 16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2) := by
      field_simp <;> ring
    linarith
  have h := sum_split m hm S N hS' (fun l => Real.log l / (l : ℝ) ^ 2)
    (fun q => 16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2))
    hG0 hFG
  try simp only at h
  have hsum : ∑ q ∈ Finset.Icc 1 N, 16 / 9 / (m : ℝ) ^ 2 *
      ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2)
      = 16 / 9 / (m : ℝ) ^ 2 * (Real.log 2 + Real.log m) * ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ^ 2
        + 16 / 9 / (m : ℝ) ^ 2 * ∑ q ∈ Finset.Icc 1 N, Real.log q / (q : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hc1 : (0 : ℝ) ≤ 16 / 9 / (m : ℝ) ^ 2 := by positivity
  have i1 := mul_le_mul_of_nonneg_left (sum_inv_sq_le N) (mul_nonneg hc1 hB)
  have i2 := mul_le_mul_of_nonneg_left (sum_log_sq_le N) hc1
  nlinarith

/- English proof (translation)
Establish `hL : 0 < L` using `lt_of_lt_of_le hc hcL`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem div_le_div_of_le_of_le (a A c L : ℝ) (hA : 0 ≤ A) (haA : a ≤ A) (hc : 0 < c)
    (hcL : c ≤ L) : a / L ≤ A / c := by
  have hL : 0 < L := lt_of_lt_of_le hc hcL
  calc a / L ≤ A / L := by gcongr
    _ ≤ A / c := by gcongr

/- English proof (translation)
Establish `hm0 : (0 : ℝ) < m`. Establish `: (4 : ℝ) ≤ m` using `by exact_mod_cast hm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hY0 : 0 < Y` using `by linarith`.

Establish `hlY : 0 ≤ Real.log Y` using `Real.log_nonneg (by linarith)`. Establish `hG0 : ∀ q : ℕ, 0 ≤ 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ))`. Introduce `q`. Conclude with `mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hlY) hm0.le) (by positivity)`. Establish `hFG : ∀ l ∈ S, ∀ q : ℕ, 1 ≤ q → (l = m * q + 1 ∨ l + 1 = m * q) → Real.log l / (l : ℝ) ≤ 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ))`.

Introduce `l hl q hq hlq`. Establish `hsz` using `size_of_form m q l hm hq hlq`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hmne : (m : ℝ) ≠ 0` using `hm0.ne'`. Establish `hqne : (q : ℝ) ≠ 0` using `hq0.ne'`.

Establish `hc : (0 : ℝ) < (3 / 4 : ℝ) * ((m : ℝ) * q)` using `by positivity`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast (hS l hl).1`. Establish `hlN : (l : ℝ) ≤ N` using `by exact_mod_cast (hS l hl).2.1`. Establish `hlog : Real.log l ≤ Real.log Y` using `Real.log_le_log (by linarith) (by linarith)`. Establish `h1` using `div_le_div_of_le_of_le _ _ _ _ hlY hlog hc hsz.1`.

Establish `e : Real.log Y / ((3 / 4 : ℝ) * ((m : ℝ) * q)) = 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ))`. Apply the tactic sequence `field_simp <;> ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `sum_split m hm S N hS (fun l => Real.log l / (l : ℝ)) (fun q => 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ))) hG0 hFG`. Apply the tactic sequence `try simp only at h`.

Rewrite `h` using `[← Finset.mul_sum]`. Establish `hs` using `sum_inv_le N hN`. Establish `hlN : Real.log N ≤ Real.log Y` using `Real.log_le_log (by linarith) hNY`. Establish `hc1 : 0 ≤ 4 / 3 * Real.log Y / (m : ℝ)` using `div_nonneg (mul_nonneg (by norm_num) hlY) hm0.le`. Establish `i1` using `mul_le_mul_of_nonneg_left hs hc1`.

Establish `i2` using `mul_le_mul_of_nonneg_left hlN hc1`. Use polynomial arithmetic with `[i1, i2]`.
-/
theorem sum_lin_bound (m : ℕ) (hm : 4 ≤ m) (S : Finset ℕ) (N : ℕ) (Y : ℝ) (hN : 1 ≤ N)
    (hNY : (N : ℝ) ≤ Y)
    (hS : ∀ l ∈ S, 2 ≤ l ∧ l ≤ N ∧ (l % m = 1 ∨ (l + 1) % m = 0)) :
    ∑ l ∈ S, Real.log l / (l : ℝ) ≤
      2 * (4 / 3 * Real.log Y / (m : ℝ) * (1 + Real.log Y)) := by
  have hm0 : (0 : ℝ) < m := by
    have : (4 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hY0 : 0 < Y := by linarith
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hG0 : ∀ q : ℕ, 0 ≤ 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ)) := by
    intro q
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hlY) hm0.le) (by positivity)
  have hFG : ∀ l ∈ S, ∀ q : ℕ, 1 ≤ q → (l = m * q + 1 ∨ l + 1 = m * q) →
      Real.log l / (l : ℝ) ≤ 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ)) := by
    intro l hl q hq hlq
    have hsz := size_of_form m q l hm hq hlq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hmne : (m : ℝ) ≠ 0 := hm0.ne'
    have hqne : (q : ℝ) ≠ 0 := hq0.ne'
    have hc : (0 : ℝ) < (3 / 4 : ℝ) * ((m : ℝ) * q) := by positivity
    have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (hS l hl).1
    have hlN : (l : ℝ) ≤ N := by exact_mod_cast (hS l hl).2.1
    have hlog : Real.log l ≤ Real.log Y := Real.log_le_log (by linarith) (by linarith)
    have h1 := div_le_div_of_le_of_le _ _ _ _ hlY hlog hc hsz.1
    have e : Real.log Y / ((3 / 4 : ℝ) * ((m : ℝ) * q)) = 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ)) := by
      field_simp <;> ring
    linarith
  have h := sum_split m hm S N hS (fun l => Real.log l / (l : ℝ))
    (fun q => 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ))) hG0 hFG
  try simp only at h
  rw [← Finset.mul_sum] at h
  have hs := sum_inv_le N hN
  have hlN : Real.log N ≤ Real.log Y := Real.log_le_log (by linarith) hNY
  have hc1 : 0 ≤ 4 / 3 * Real.log Y / (m : ℝ) := div_nonneg (mul_nonneg (by norm_num) hlY) hm0.le
  have i1 := mul_le_mul_of_nonneg_left hs hc1
  have i2 := mul_le_mul_of_nonneg_left hlN hc1
  nlinarith [i1, i2]

/- English proof (translation)
The claim follows from `(Nat.coprime_primes hl Nat.prime_two).mpr h2`.
-/
theorem coprime_two {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) : Nat.Coprime l 2 := (Nat.coprime_primes hl Nat.prime_two).mpr h2

/- English proof (translation)
Set `f : Multiplicative (ZMod (2 ^ e)) →* HGrp e` to `MonoidHom.mk' (fun a => iotaH e (Multiplicative.toAdd a)) (fun a b => iotaH_add e (Multiplicative.toAdd a) (Multiplicative.toAdd b))`. Establish `hf : Function.Injective f` using `fun a b h => Multiplicative.toAdd.injective (iotaH_injective e h)`. Establish `h` using `orderOf_injective f hf (Multiplicative.ofAdd x)`. Rewrite `h` using `[orderOf_ofAdd_eq_addOrderOf]`. Conclude with `h`.
-/
private theorem orderOf_iotaH_eq_addOrderOf (e : ℕ) (x : ZMod (2 ^ e)) : orderOf (iotaH e x) = addOrderOf x := by
  let f : Multiplicative (ZMod (2 ^ e)) →* HGrp e :=
    MonoidHom.mk' (fun a => iotaH e (Multiplicative.toAdd a))
      (fun a b => iotaH_add e (Multiplicative.toAdd a) (Multiplicative.toAdd b))
  have hf : Function.Injective f := fun a b h => Multiplicative.toAdd.injective (iotaH_injective e h)
  have h := orderOf_injective f hf (Multiplicative.ofAdd x)
  rw [orderOf_ofAdd_eq_addOrderOf] at h
  exact h

/- English proof (translation)
Unfold `hOf`. Rewrite using `[dif_pos hl]`. Unfold `ordH`. Rewrite using `[← orderOf_iotaH_eq_addOrderOf, iotaH_iotaHInv]`.
-/
theorem hOf_ord (e l : ℕ) (hl : Nat.Coprime l 2) :
    ordH (hOf e l) =
      orderOf (hcl e (ZMod.unitOfCoprime l (Nat.Coprime.pow_right (e + 2) hl))) := by
  unfold hOf
  rw [dif_pos hl]
  unfold ordH
  rw [← orderOf_iotaH_eq_addOrderOf, iotaH_iotaHInv]

/- English proof (translation)
Take `⟨k, rfl⟩` from `hx`. Break down `N with _ | _ | n` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [pow_one, Nat.sub_self, pow_zero, one_dvd, or_true, iff_true] left`. Conclude with `⟨2 * k ^ 2 + 2 * k, by ring⟩`.

Rewrite using `[show n + 1 + 1 - 1 = n + 1 by omega]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨c, hc⟩ | ⟨c, hc⟩)`. Establish `h4 : (4 : ℤ) * (k * (k + 1)) = 4 * (2 ^ n * c)`. Take the linear combination `hc`.

Establish `hkk : k * (k + 1) = 2 ^ n * c` using `mul_left_cancel₀ (by norm_num) h4`. Break down `Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩` into its components or cases. Establish `hcop : IsCoprime ((2 : ℤ) ^ n) (k + 1)`. Apply `IsCoprime.pow_left` to reduce the goal to its premises. Conclude with `⟨-r, 1, by rw [hr]; ring⟩`.

Take `⟨d, hd⟩` from `hcop.dvd_of_dvd_mul_right ⟨c, hkk⟩`. Use `left`. Conclude with `⟨d, by linear_combination 2 * hd⟩`. Establish `hcop : IsCoprime ((2 : ℤ) ^ n) k`. Apply `IsCoprime.pow_left` to reduce the goal to its premises.

Conclude with `⟨-r, 1, by rw [hr]; ring⟩`. Take `⟨d, hd⟩` from `hcop.dvd_of_dvd_mul_left ⟨c, hkk⟩`. Use `right`. Conclude with `⟨d, by linear_combination 2 * hd⟩`. Establish `h : (2 : ℤ) * (2 * (2 ^ n * c - k ^ 2 - k)) = 2 * 1`.

Take the linear combination `(-1 : ℤ) * hc`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `(⟨d, hd⟩ | ⟨d, hd⟩)`. Use `left`. Conclude with `⟨d + 2 ^ n * d ^ 2, by linear_combination (2 * k + 2 ^ (n + 1) * d + 2) * hd⟩`.

Use `left`. Conclude with `⟨-d + 2 ^ n * d ^ 2, by linear_combination (2 * k + 2 + 2 ^ (n + 1) * d - 2) * hd⟩`.
-/
private theorem two_pow_dvd_sq_pm_one_iff_of_odd (x : ℤ) (hx : Odd x) (N : ℕ) :
    ((2 : ℤ) ^ N ∣ x ^ 2 - 1 ∨ (2 : ℤ) ^ N ∣ x ^ 2 + 1) ↔
      ((2 : ℤ) ^ (N - 1) ∣ x - 1 ∨ (2 : ℤ) ^ (N - 1) ∣ x + 1) := by
  obtain ⟨k, rfl⟩ := hx
  rcases N with _ | _ | n
  · simp
  · simp only [pow_one, Nat.sub_self, pow_zero, one_dvd, or_true, iff_true]
    left
    exact ⟨2 * k ^ 2 + 2 * k, by ring⟩
  · rw [show n + 1 + 1 - 1 = n + 1 by omega]
    constructor
    · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
      · have h4 : (4 : ℤ) * (k * (k + 1)) = 4 * (2 ^ n * c) := by
          linear_combination hc
        have hkk : k * (k + 1) = 2 ^ n * c := mul_left_cancel₀ (by norm_num) h4
        rcases Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
        · have hcop : IsCoprime ((2 : ℤ) ^ n) (k + 1) := by
            apply IsCoprime.pow_left
            exact ⟨-r, 1, by rw [hr]; ring⟩
          obtain ⟨d, hd⟩ := hcop.dvd_of_dvd_mul_right ⟨c, hkk⟩
          left
          exact ⟨d, by linear_combination 2 * hd⟩
        · have hcop : IsCoprime ((2 : ℤ) ^ n) k := by
            apply IsCoprime.pow_left
            exact ⟨-r, 1, by rw [hr]; ring⟩
          obtain ⟨d, hd⟩ := hcop.dvd_of_dvd_mul_left ⟨c, hkk⟩
          right
          exact ⟨d, by linear_combination 2 * hd⟩
      · have h : (2 : ℤ) * (2 * (2 ^ n * c - k ^ 2 - k)) = 2 * 1 := by
          linear_combination (-1 : ℤ) * hc
        omega
    · rintro (⟨d, hd⟩ | ⟨d, hd⟩)
      · left
        exact ⟨d + 2 ^ n * d ^ 2, by linear_combination (2 * k + 2 ^ (n + 1) * d + 2) * hd⟩
      · left
        exact ⟨-d + 2 ^ n * d ^ 2, by linear_combination (2 * k + 2 + 2 ^ (n + 1) * d - 2) * hd⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => intro N`. Simplify using the standard rewrite rules. Consider the case `succ j ih`. Introduce `N`.

Rewrite using `[pow_succ, pow_mul, two_pow_dvd_sq_pm_one_iff_of_odd _ hx.pow N, ih (N - 1), show N - 1 - j = N - (j + 1) by omega]`.
-/
private theorem two_pow_dvd_pow_two_pow_pm_one_iff_of_odd (x : ℤ) (hx : Odd x) (j : ℕ) : ∀ N : ℕ,
    ((2 : ℤ) ^ N ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ N ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ (N - j) ∣ x - 1 ∨ (2 : ℤ) ^ (N - j) ∣ x + 1) := by
  induction j with
  | zero => intro N; simp
  | succ j ih =>
    intro N
    rw [pow_succ, pow_mul, two_pow_dvd_sq_pm_one_iff_of_odd _ hx.pow N, ih (N - 1), show N - 1 - j = N - (j + 1) by omega]

/- English proof (translation)
Establish `e : ((2 ^ M : ℕ) : ℤ) = (2 : ℤ) ^ M` using `by norm_num`. Establish `h1 : (a : ZMod (2 ^ M)) = 1 ↔ (2 : ℤ) ^ M ∣ a - 1`. Rewrite using `[show (1 : ZMod (2 ^ M)) = ((1 : ℤ) : ZMod (2 ^ M)) from Int.cast_one.symm, ZMod.intCast_eq_intCast_iff_dvd_sub, e, dvd_sub_comm]`. Establish `h2 : (a : ZMod (2 ^ M)) = -1 ↔ (2 : ℤ) ^ M ∣ a + 1`. Rewrite using `[show (-1 : ZMod (2 ^ M)) = ((-1 : ℤ) : ZMod (2 ^ M)) by simp, ZMod.intCast_eq_intCast_iff_dvd_sub, e, show (-1 : ℤ) - a = -(a + 1) by ring, dvd_neg]`.

Rewrite using `[h1, h2]`.
-/
private theorem intCast_eq_pm_one_zmod_two_pow_iff (M : ℕ) (a : ℤ) :
    ((a : ZMod (2 ^ M)) = 1 ∨ (a : ZMod (2 ^ M)) = -1) ↔
      ((2 : ℤ) ^ M ∣ a - 1 ∨ (2 : ℤ) ^ M ∣ a + 1) := by
  have e : ((2 ^ M : ℕ) : ℤ) = (2 : ℤ) ^ M := by norm_num
  have h1 : (a : ZMod (2 ^ M)) = 1 ↔ (2 : ℤ) ^ M ∣ a - 1 := by
    rw [show (1 : ZMod (2 ^ M)) = ((1 : ℤ) : ZMod (2 ^ M)) from Int.cast_one.symm,
      ZMod.intCast_eq_intCast_iff_dvd_sub, e, dvd_sub_comm]
  have h2 : (a : ZMod (2 ^ M)) = -1 ↔ (2 : ℤ) ^ M ∣ a + 1 := by
    rw [show (-1 : ZMod (2 ^ M)) = ((-1 : ℤ) : ZMod (2 ^ M)) by simp,
      ZMod.intCast_eq_intCast_iff_dvd_sub, e, show (-1 : ℤ) - a = -(a + 1) by ring, dvd_neg]
  rw [h1, h2]

/- English proof (translation)
Rewrite using `[Subgroup.mem_zpowers_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Break down `Int.even_or_odd k with hk | hk` into its components or cases. Use `left`.

Conclude with `hk.neg_one_zpow`. Use `right`. Conclude with `hk.neg_one_zpow`. Introduce and unpack `(rfl | rfl)`. Conclude with `⟨0, zpow_zero _⟩`.

Conclude with `⟨1, zpow_one _⟩`.
-/
private theorem mem_zpowers_neg_one_iff_eq_one_or_neg_one (N : ℕ) (x : (ZMod N)ˣ) :
    x ∈ Subgroup.zpowers (-1 : (ZMod N)ˣ) ↔ x = 1 ∨ x = -1 := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with hk | hk
    · left
      exact hk.neg_one_zpow
    · right
      exact hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

/- English proof (translation)
Establish `h : addOrderOf x ∣ 2 ^ e`. Apply `addOrderOf_dvd_of_nsmul_eq_zero` to reduce the goal to its premises. Rewrite using `[nsmul_eq_mul, ZMod.natCast_self, zero_mul]`. Conclude with `(Nat.dvd_prime_pow Nat.prime_two).mp h`.
-/
private theorem exists_addOrderOf_eq_two_pow_of_zmod_two_pow (e : ℕ) (x : ZMod (2 ^ e)) : ∃ k ≤ e, addOrderOf x = 2 ^ k := by
  have h : addOrderOf x ∣ 2 ^ e := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  exact (Nat.dvd_prime_pow Nat.prime_two).mp h

/- English proof (translation)
Establish `hmod : l % 2 = 1`. Break down `Nat.mod_two_eq_zero_or_one l with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h2 : 2 ∣ Nat.gcd l 2` using `Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) (dvd_refl 2)`. Rewrite `h2` using `[Nat.Coprime.gcd_eq_one hl]`.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hodd : Odd (l : ℤ)`. Use `⟨((l / 2 : ℕ) : ℤ), ?_⟩` and prove the remaining obligations. Establish `h` using `Nat.div_add_mod l 2`.

Rewrite `h` using `[hmod]`. Conclude with `h.symm` after adjusting the coercions. Take `⟨k, -, hk⟩` from `exists_addOrderOf_eq_two_pow_of_zmod_two_pow e (hOf e l)`. Establish `hord` using `hOf_ord e l hl`. Unfold `ordH at hord`.

Rewrite `hord` using `[hk]`. Unfold `ordH`. Rewrite using `[hk, Nat.pow_le_pow_iff_right (by norm_num : 1 < 2), ← Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2), hord, orderOf_dvd_iff_pow_eq_one]`. Unfold `hcl`. Rewrite using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_zpowers_neg_one_iff_eq_one_or_neg_one]`.

Simplify using `only [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, Units.val_neg]`. Establish `h1` using `intCast_eq_pm_one_zmod_two_pow_iff (e + 2) ((l : ℤ) ^ (2 ^ j))`. Establish `h2` using `intCast_eq_pm_one_zmod_two_pow_iff (e + 2 - j) (l : ℤ)`. Move the coercions through the operations in `at h1 h2`. Rewrite using `[h1, h2]`.

Conclude with `two_pow_dvd_pow_two_pow_pm_one_iff_of_odd (l : ℤ) hodd j (e + 2)`.
-/
theorem ord_le_iff (e l j : ℕ) (hl : Nat.Coprime l 2) :
    ordH (hOf e l) ≤ 2 ^ j ↔
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1) := by
  have hmod : l % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one l with h | h
    · exfalso
      have h2 : 2 ∣ Nat.gcd l 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) (dvd_refl 2)
      rw [Nat.Coprime.gcd_eq_one hl] at h2
      omega
    · exact h
  have hodd : Odd (l : ℤ) := by
    refine ⟨((l / 2 : ℕ) : ℤ), ?_⟩
    have h := Nat.div_add_mod l 2
    rw [hmod] at h
    exact_mod_cast h.symm
  obtain ⟨k, -, hk⟩ := exists_addOrderOf_eq_two_pow_of_zmod_two_pow e (hOf e l)
  have hord := hOf_ord e l hl
  unfold ordH at hord
  rw [hk] at hord
  unfold ordH
  rw [hk, Nat.pow_le_pow_iff_right (by norm_num : 1 < 2), ← Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2), hord,
    orderOf_dvd_iff_pow_eq_one]
  unfold hcl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_zpowers_neg_one_iff_eq_one_or_neg_one]
  simp only [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, Units.val_neg]
  have h1 := intCast_eq_pm_one_zmod_two_pow_iff (e + 2) ((l : ℤ) ^ (2 ^ j))
  have h2 := intCast_eq_pm_one_zmod_two_pow_iff (e + 2 - j) (l : ℤ)
  push_cast at h1 h2
  rw [h1, h2]
  exact two_pow_dvd_pow_two_pow_pm_one_iff_of_odd (l : ℤ) hodd j (e + 2)

/- English proof (translation)
Take `⟨k, -, hk'⟩` from `exists_addOrderOf_eq_two_pow_of_zmod_two_pow e (hOf e l)`. Unfold `ordH`. Rewrite using `[← addOrderOf_dvd_iff_nsmul_eq_zero, hk', Nat.pow_dvd_pow_iff_le_right (by norm_num), Nat.pow_le_pow_iff_right (by norm_num)]`.
-/
theorem nsmul_iff (e l j : ℕ) (hl : Nat.Coprime l 2) :
    (2 ^ j : ℕ) • hOf e l = 0 ↔ ordH (hOf e l) ≤ 2 ^ j := by
  obtain ⟨k, -, hk'⟩ := exists_addOrderOf_eq_two_pow_of_zmod_two_pow e (hOf e l)
  unfold ordH
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hk', Nat.pow_dvd_pow_iff_le_right (by norm_num),
    Nat.pow_le_pow_iff_right (by norm_num)]

/- English proof (translation)
Establish `h : addOrderOf x ∣ 2 ^ e`. Apply `addOrderOf_dvd_of_nsmul_eq_zero` to reduce the goal to its premises. Rewrite using `[nsmul_eq_mul, ZMod.natCast_self, zero_mul]`. Take `⟨k, hk, hk'⟩` from `(Nat.dvd_prime_pow Nat.prime_two).mp h`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations.

Unfold `ordH`. Conclude with `hk'`.
-/
theorem ord_pow (e : ℕ) (x : ZMod (2 ^ e)) : ∃ k ≤ e, ordH x = 2 ^ k := by
  have h : addOrderOf x ∣ 2 ^ e := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  refine ⟨k, hk, ?_⟩
  unfold ordH
  exact hk'

/- English proof (translation)
Break down `h with h | h` into its components or cases. Use `left`. Establish `h' : ((l : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m)` using `by rw [h, Nat.cast_one]`. Rewrite `h'` using `[ZMod.natCast_eq_natCast_iff']`. Rewrite using `[h', Nat.mod_eq_of_lt (by omega : 1 < m)]`.

Use `right`. Establish `h' : ((l + 1 : ℕ) : ZMod m) = ((0 : ℕ) : ZMod m)`. Use `push_cast`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h'` using `[ZMod.natCast_eq_natCast_iff']`. Rewrite using `[h', Nat.zero_mod]`.
-/
theorem mod_form (m l : ℕ) (hm : 4 ≤ m) (h : (l : ZMod m) = 1 ∨ (l : ZMod m) = -1) :
    l % m = 1 ∨ (l + 1) % m = 0 := by
  rcases h with h | h
  · left
    have h' : ((l : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by rw [h, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [h', Nat.mod_eq_of_lt (by omega : 1 < m)]
  · right
    have h' : ((l + 1 : ℕ) : ZMod m) = ((0 : ℕ) : ZMod m) := by
      push_cast
      rw [h]
      ring
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [h', Nat.zero_mod]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Break down `h with h | h` into its components or cases. Rewrite `h` using `[Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.

Rewrite `h` using `[Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_of_form (m l : ℕ) (hl : 2 ≤ l) (h : l % m = 1 ∨ (l + 1) % m = 0) : m ≤ l + 1 := by
  by_contra hc
  push_neg at hc
  rcases h with h | h
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/- English proof (translation)
Use `set K := Nat.findGreatest (fun k => (2 : ℝ) ^ k ≤ J) e with hK`. Establish `hKe : K ≤ e` using `Nat.findGreatest_le e`. Establish `hKJ : (2 : ℝ) ^ K ≤ J` using `Nat.findGreatest_spec (P := fun k => (2 : ℝ) ^ k ≤ J) (Nat.zero_le e) (by simpa using hJ)`. Establish `hm4 : 4 ≤ 2 ^ (e + 2 - K)`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨2 ^ (e + 2 - K), hm4, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ((2 ^ (e + 2 - K) : ℕ) : ℝ) * (2 : ℝ) ^ K = 4 * ((2 ^ e : ℕ) : ℝ)`. Use `push_cast`. Rewrite using `[← pow_add, show e + 2 - K + K = e + 2 by omega]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (0 : ℝ) ≤ ((2 ^ (e + 2 - K) : ℕ) : ℝ)` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hKJ h2]`. Introduce `l hl h2 hord`. Take `⟨k, hk, hk'⟩` from `ord_pow e (hOf e l)`.

Establish `hkJ : (2 : ℝ) ^ k ≤ J`. Rewrite `hord` using `[hk']`. Conclude with `hord` after adjusting the coercions. Establish `hkK : k ≤ K` using `Nat.le_findGreatest (P := fun k => (2 : ℝ) ^ k ≤ J) hk hkJ`. Establish `hle : ordH (hOf e l) ≤ 2 ^ K`.

Rewrite using `[hk']`. Conclude with `Nat.pow_le_pow_right (by norm_num) hkK`. Conclude with `mod_form _ l hm4 ((ord_le_iff e l K (coprime_two hl h2)).mp hle)`.
-/
theorem modulus (e : ℕ) (J : ℝ) (hJ : 1 ≤ J) :
    ∃ m : ℕ, 4 ≤ m ∧ m ≤ 4 * 2 ^ e ∧ 4 * ((2 ^ e : ℕ) : ℝ) ≤ m * J ∧
      ∀ l : ℕ, l.Prime → l ≠ 2 → (ordH (hOf e l) : ℝ) ≤ J →
        (l % m = 1 ∨ (l + 1) % m = 0) := by
  classical
  set K := Nat.findGreatest (fun k => (2 : ℝ) ^ k ≤ J) e with hK
  have hKe : K ≤ e := Nat.findGreatest_le e
  have hKJ : (2 : ℝ) ^ K ≤ J :=
    Nat.findGreatest_spec (P := fun k => (2 : ℝ) ^ k ≤ J) (Nat.zero_le e) (by simpa using hJ)
  have hm4 : 4 ≤ 2 ^ (e + 2 - K) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e + 2 - K) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨2 ^ (e + 2 - K), hm4, ?_, ?_, ?_⟩
  · calc 2 ^ (e + 2 - K) ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 * 2 ^ e := by ring
  · have h1 : ((2 ^ (e + 2 - K) : ℕ) : ℝ) * (2 : ℝ) ^ K = 4 * ((2 ^ e : ℕ) : ℝ) := by
      push_cast
      rw [← pow_add, show e + 2 - K + K = e + 2 by omega]
      ring
    have h2 : (0 : ℝ) ≤ ((2 ^ (e + 2 - K) : ℕ) : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hKJ h2]
  · intro l hl h2 hord
    obtain ⟨k, hk, hk'⟩ := ord_pow e (hOf e l)
    have hkJ : (2 : ℝ) ^ k ≤ J := by
      rw [hk'] at hord
      exact_mod_cast hord
    have hkK : k ≤ K := Nat.le_findGreatest (P := fun k => (2 : ℝ) ^ k ≤ J) hk hkJ
    have hle : ordH (hOf e l) ≤ 2 ^ K := by
      rw [hk']
      exact Nat.pow_le_pow_right (by norm_num) hkK
    exact mod_form _ l hm4 ((ord_le_iff e l K (coprime_two hl h2)).mp hle)

/- English proof (translation)
Establish `h4 : (4 : ℝ) ≤ ((2 ^ e : ℕ) : ℝ)`. Establish `: 4 ≤ 2 ^ e`. Combine the equalities or inequalities in the displayed calculation. Conclude with `this` after adjusting the coercions. Establish `h1 : Real.log 4 = 2 * Real.log 2`.

Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Evaluate the numerical expressions. Rewrite using `[← h1]`. Conclude with `Real.log_le_log (by norm_num) h4`.
-/
theorem log_n_ge (e : ℕ) (he : 2 ≤ e) :
    2 * Real.log 2 ≤ Real.log ((2 ^ e : ℕ) : ℝ) := by
  have h4 : (4 : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := by
    have : 4 ≤ 2 ^ e := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    exact_mod_cast this
  have h1 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [← h1]
  exact Real.log_le_log (by norm_num) h4

/- English proof (translation)
Use `set n : ℝ := ((2 ^ e : ℕ) : ℝ) with hn`. Establish `hn4 : (4 : ℝ) ≤ n`. Establish `: 4 ≤ 2 ^ e`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hn]`.

Conclude with `this` after adjusting the coercions. Establish `hm' : (4 : ℝ) ≤ m` using `by exact_mod_cast hm4`. Establish `hm0 : (0 : ℝ) < m` using `by linarith`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hLn` using `log_n_ge e he`.

Rewrite `hLn` using `[← hn]`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hL1 : 1 ≤ Real.log n` using `by linarith`. Establish `hmle' : (m : ℝ) ≤ 4 * n`. Rewrite using `[hn]`.

Conclude with `hmle` after adjusting the coercions. Establish `hlm : Real.log m ≤ 2 * Real.log 2 + Real.log n`. Establish `h1 : Real.log m ≤ Real.log (4 * n)` using `Real.log_le_log hm0 hmle'`. Establish `h2 : Real.log (4 * n) = Real.log 4 + Real.log n` using `Real.log_mul (by norm_num) hn0.ne'`. Establish `h3 : Real.log 4 = 2 * Real.log 2`.

Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK : (Real.log 2 + Real.log m) * 2 + 2 ≤ 7 * Real.log n` using `by linarith`. Establish `hmJ2 : 16 * n ^ 2 ≤ (m : ℝ) ^ 2 * J ^ 2`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hmJ) (sub_nonneg.mpr hmJ), mul_nonneg (sub_nonneg.mpr hmJ) hn0.le]`. Rewrite using `[show (2 : ℝ) * (16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) * 2 + 2)) = (32 / 9 * ((Real.log 2 + Real.log m) * 2 + 2)) / (m : ℝ) ^ 2 by ring]`. Rewrite using `[le_div_iff₀ (pow_pos hn0 2), div_mul_eq_mul_div, div_le_iff₀ (pow_pos hm0 2)]`. Establish `hLn0 : 0 ≤ Real.log n` using `by linarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hK (sq_nonneg n), mul_nonneg hLn0 (sub_nonneg.mpr hmJ2), mul_nonneg hLn0 (mul_nonneg (sq_nonneg (m : ℝ)) (sq_nonneg J))]`.
-/
theorem square_term_le (e : ℕ) (he : 2 ≤ e) (m : ℕ) (hm4 : 4 ≤ m) (hmle : m ≤ 4 * 2 ^ e) (J : ℝ)
    (hJ : 1 ≤ J) (hmJ : 4 * ((2 ^ e : ℕ) : ℝ) ≤ m * J) :
    2 * (16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) * 2 + 2)) ≤
      100 * J ^ 2 * Real.log ((2 ^ e : ℕ) : ℝ) / (((2 ^ e : ℕ) : ℝ)) ^ 2 := by
  set n : ℝ := ((2 ^ e : ℕ) : ℝ) with hn
  have hn4 : (4 : ℝ) ≤ n := by
    have : 4 ≤ 2 ^ e := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    rw [hn]
    exact_mod_cast this
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) < m := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hLn := log_n_ge e he
  rw [← hn] at hLn
  have hl2 := Real.log_two_gt_d9
  have hL1 : 1 ≤ Real.log n := by linarith
  have hmle' : (m : ℝ) ≤ 4 * n := by
    rw [hn]
    exact_mod_cast hmle
  have hlm : Real.log m ≤ 2 * Real.log 2 + Real.log n := by
    have h1 : Real.log m ≤ Real.log (4 * n) := Real.log_le_log hm0 hmle'
    have h2 : Real.log (4 * n) = Real.log 4 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
    have h3 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hK : (Real.log 2 + Real.log m) * 2 + 2 ≤ 7 * Real.log n := by linarith
  have hmJ2 : 16 * n ^ 2 ≤ (m : ℝ) ^ 2 * J ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmJ) (sub_nonneg.mpr hmJ), mul_nonneg (sub_nonneg.mpr hmJ) hn0.le]
  rw [show (2 : ℝ) * (16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) * 2 + 2))
      = (32 / 9 * ((Real.log 2 + Real.log m) * 2 + 2)) / (m : ℝ) ^ 2 by ring]
  rw [le_div_iff₀ (pow_pos hn0 2), div_mul_eq_mul_div, div_le_iff₀ (pow_pos hm0 2)]
  have hLn0 : 0 ≤ Real.log n := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg n), mul_nonneg hLn0 (sub_nonneg.mpr hmJ2),
    mul_nonneg hLn0 (mul_nonneg (sq_nonneg (m : ℝ)) (sq_nonneg J))]

/- English proof (translation)
Use `set n : ℝ := ((2 ^ e : ℕ) : ℝ) with hn`. Establish `hn4 : (4 : ℝ) ≤ n`. Establish `: 4 ≤ 2 ^ e`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hn]`.

Conclude with `this` after adjusting the coercions. Establish `hm' : (4 : ℝ) ≤ m` using `by exact_mod_cast hm4`. Establish `hm0 : (0 : ℝ) < m` using `by linarith`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hLn` using `log_n_ge e he`.

Rewrite `hLn` using `[← hn]`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hy0 : 0 ≤ Real.log Y` using `Real.log_nonneg (by linarith)`. Establish `hM : Real.log (n * Y) = Real.log n + Real.log Y` using `Real.log_mul hn0.ne' hY0.ne'`.

Establish `hyM : Real.log Y ≤ Real.log (n * Y)` using `by linarith`. Establish `hM1 : 1 ≤ Real.log (n * Y)` using `by linarith`. Establish `hq : Real.log Y * (1 + Real.log Y) ≤ 2 * Real.log (n * Y) ^ 2`. Use polynomial arithmetic with `[mul_le_mul hyM hyM hy0 (by linarith), mul_le_mul_of_nonneg_left hM1 (by linarith : (0 : ℝ) ≤ Real.log (n * Y))]`. Rewrite using `[show (2 : ℝ) * (4 / 3 * Real.log Y / (m : ℝ) * (1 + Real.log Y)) = (8 / 3 * (Real.log Y * (1 + Real.log Y))) / (m : ℝ) by ring]`.

Rewrite using `[le_div_iff₀ hn0, div_mul_eq_mul_div, div_le_iff₀ hm0]`. Establish `hM0 : 0 ≤ Real.log (n * Y) ^ 2` using `sq_nonneg _`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hq hn0.le, mul_nonneg hM0 (sub_nonneg.mpr hmJ), mul_nonneg hM0 (mul_nonneg hm0.le (by linarith : (0 : ℝ) ≤ J))]`.
-/
theorem linear_term_le (e : ℕ) (he : 2 ≤ e) (m : ℕ) (hm4 : 4 ≤ m) (J Y : ℝ)
    (hJ : 1 ≤ J) (hY : 3 ≤ Y) (hmJ : 4 * ((2 ^ e : ℕ) : ℝ) ≤ m * J) :
    2 * (4 / 3 * Real.log Y / (m : ℝ) * (1 + Real.log Y)) ≤
      100 * J * Real.log (((2 ^ e : ℕ) : ℝ) * Y) ^ 2 / ((2 ^ e : ℕ) : ℝ) := by
  set n : ℝ := ((2 ^ e : ℕ) : ℝ) with hn
  have hn4 : (4 : ℝ) ≤ n := by
    have : 4 ≤ 2 ^ e := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    rw [hn]
    exact_mod_cast this
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) < m := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hLn := log_n_ge e he
  rw [← hn] at hLn
  have hl2 := Real.log_two_gt_d9
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hM : Real.log (n * Y) = Real.log n + Real.log Y := Real.log_mul hn0.ne' hY0.ne'
  have hyM : Real.log Y ≤ Real.log (n * Y) := by linarith
  have hM1 : 1 ≤ Real.log (n * Y) := by linarith
  have hq : Real.log Y * (1 + Real.log Y) ≤ 2 * Real.log (n * Y) ^ 2 := by
    nlinarith [mul_le_mul hyM hyM hy0 (by linarith), mul_le_mul_of_nonneg_left hM1 (by linarith : (0 : ℝ) ≤ Real.log (n * Y))]
  rw [show (2 : ℝ) * (4 / 3 * Real.log Y / (m : ℝ) * (1 + Real.log Y))
      = (8 / 3 * (Real.log Y * (1 + Real.log Y))) / (m : ℝ) by ring]
  rw [le_div_iff₀ hn0, div_mul_eq_mul_div, div_le_iff₀ hm0]
  have hM0 : 0 ≤ Real.log (n * Y) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hq hn0.le, mul_nonneg hM0 (sub_nonneg.mpr hmJ),
    mul_nonneg hM0 (mul_nonneg hm0.le (by linarith : (0 : ℝ) ≤ J))]

end PrimeReciprocalSums

open PrimeReciprocalSums

open Classical in

/- English proof (translation)
Substitute `hn` using the available equality. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl h2 j hj`. Establish `hc` using `coprime_two hl h2`. Establish `hm : 4 * 2 ^ e / 2 ^ j = 2 ^ (e + 2 - j)`.

Rewrite using `[show 4 * 2 ^ e = 2 ^ (e + 2) by ring, Nat.pow_div (by omega) (by norm_num)]`. Rewrite using `[hm, nsmul_iff e l j hc, ord_le_iff e l j hc]`. Introduce `J hJ l hl h2 hord`. Take `⟨m, hm4, -, hmJ, hmod⟩` from `modulus e J hJ`. Establish `h1` using `le_of_form m l hl.two_le (hmod l hl h2 hord)`.

Establish `h1' : (m : ℝ) ≤ l + 1` using `by exact_mod_cast h1`. Establish `hJ0 : 0 < J` using `by linarith`. Rewrite using `[sub_le_iff_le_add, div_le_iff₀ hJ0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h1' hJ0.le]`. Introduce `J hJ S hS`.

Take `⟨m, hm4, hmle, hmJ, hmod⟩` from `modulus e J hJ`. Establish `h1` using `sum_sq_bound m hm4 S (fun l hl => ⟨(hS l hl).1.two_le, hmod l (hS l hl).1 (hS l hl).2.1 (hS l hl).2.2⟩)`. Conclude with `le_trans h1 (square_term_le e he m hm4 hmle J hJ hmJ)`. Introduce `J hJ Y`. Take `⟨m, hm4, hmle, hmJ, hmod⟩` from `modulus e J hJ`.

Break down `lt_or_ge Y 3 with hY | hY` into its components or cases. Establish `h0 : ∑ l ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf e l) : ℝ) ≤ J), Real.log l / (l : ℝ) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l hl`. Rewrite `hl` using `[Finset.mem_filter, Finset.mem_range]`.

Establish `hfl : ⌊Y⌋₊ < 3`. Rewrite using `[Nat.floor_lt' (by norm_num)]`. Conclude with `hY` after adjusting the coercions. Establish `h2` using `hl.2.1.two_le`. Establish `: l = 2` using `by omega`.

Conclude with `absurd this hl.2.2.1`. Rewrite using `[h0]`. Establish `hn0 : (0 : ℝ) < ((2 ^ e : ℕ) : ℝ)` using `by positivity`. Apply `div_nonneg _ hn0.le` to reduce the goal to its premises. Conclude with `mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg _)`.

Establish `hN : 1 ≤ ⌊Y⌋₊`. Rewrite using `[Nat.one_le_floor_iff]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hNY : (⌊Y⌋₊ : ℝ) ≤ Y` using `Nat.floor_le (by linarith)`. Establish `h1` using `sum_lin_bound m hm4 ((Finset.range (⌊Y⌋₊ + 1)).filter (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf e l) : ℝ) ≤ J)) ⌊Y⌋₊ Y hN hNY (fun l hl => by`.

Rewrite `hl` using `[Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨hl.2.1.two_le, by omega, hmod l hl.2.1 hl.2.2.1 hl.2.2.2⟩)`. Conclude with `le_trans h1 (linear_term_le e he m hm4 J Y hJ hY hmJ)`.
-/
private theorem small_order_prime_bounds (e : ℕ) (he : 2 ≤ e) (n : ℕ) (hn : n = 2 ^ e) :
  (∀ l : ℕ, l.Prime → l ≠ 2 → ∀ j : ℕ, j ≤ e →
    ((2 ^ j : ℕ) • hOf e l = 0 ↔
      ((l : ZMod (4 * n / 2 ^ j)) = 1 ∨ (l : ZMod (4 * n / 2 ^ j)) = -1))) ∧
  (∀ J : ℝ, 1 ≤ J → ∀ l : ℕ, l.Prime → l ≠ 2 → (ordH (hOf e l) : ℝ) ≤ J →
    4 * (n : ℝ) / J - 1 ≤ l) ∧
  (∀ J : ℝ, 1 ≤ J → ∀ S : Finset ℕ,
    (∀ l ∈ S, l.Prime ∧ l ≠ 2 ∧ (ordH (hOf e l) : ℝ) ≤ J) →
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤ 100 * J ^ 2 * Real.log n / (n : ℝ) ^ 2) ∧
  (∀ J : ℝ, 1 ≤ J → ∀ Y : ℝ,
    ∑ l ∈ (Finset.range (⌊Y⌋₊ + 1)).filter
        (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf e l) : ℝ) ≤ J),
      Real.log l / (l : ℝ) ≤ 100 * J * Real.log ((n : ℝ) * Y) ^ 2 / n) := by
  subst hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl h2 j hj
    have hc := coprime_two hl h2
    have hm : 4 * 2 ^ e / 2 ^ j = 2 ^ (e + 2 - j) := by
      rw [show 4 * 2 ^ e = 2 ^ (e + 2) by ring, Nat.pow_div (by omega) (by norm_num)]
    rw [hm, nsmul_iff e l j hc, ord_le_iff e l j hc]
  · intro J hJ l hl h2 hord
    obtain ⟨m, hm4, -, hmJ, hmod⟩ := modulus e J hJ
    have h1 := le_of_form m l hl.two_le (hmod l hl h2 hord)
    have h1' : (m : ℝ) ≤ l + 1 := by exact_mod_cast h1
    have hJ0 : 0 < J := by linarith
    rw [sub_le_iff_le_add, div_le_iff₀ hJ0]
    nlinarith [mul_le_mul_of_nonneg_right h1' hJ0.le]
  · intro J hJ S hS
    obtain ⟨m, hm4, hmle, hmJ, hmod⟩ := modulus e J hJ
    have h1 := sum_sq_bound m hm4 S
      (fun l hl => ⟨(hS l hl).1.two_le, hmod l (hS l hl).1 (hS l hl).2.1 (hS l hl).2.2⟩)
    exact le_trans h1 (square_term_le e he m hm4 hmle J hJ hmJ)
  · intro J hJ Y
    obtain ⟨m, hm4, hmle, hmJ, hmod⟩ := modulus e J hJ
    rcases lt_or_ge Y 3 with hY | hY
    · have h0 : ∑ l ∈ (Finset.range (⌊Y⌋₊ + 1)).filter
          (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf e l) : ℝ) ≤ J), Real.log l / (l : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro l hl
        rw [Finset.mem_filter, Finset.mem_range] at hl
        have hfl : ⌊Y⌋₊ < 3 := by
          rw [Nat.floor_lt' (by norm_num)]
          exact_mod_cast hY
        have h2 := hl.2.1.two_le
        have : l = 2 := by omega
        exact absurd this hl.2.2.1
      rw [h0]
      have hn0 : (0 : ℝ) < ((2 ^ e : ℕ) : ℝ) := by positivity
      apply div_nonneg _ hn0.le
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg _)
    · have hN : 1 ≤ ⌊Y⌋₊ := by
        rw [Nat.one_le_floor_iff]
        linarith
      have hNY : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
      have h1 := sum_lin_bound m hm4 ((Finset.range (⌊Y⌋₊ + 1)).filter
          (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf e l) : ℝ) ≤ J)) ⌊Y⌋₊ Y hN hNY (fun l hl => by
        rw [Finset.mem_filter, Finset.mem_range] at hl
        exact ⟨hl.2.1.two_le, by omega, hmod l hl.2.1 hl.2.2.1 hl.2.2.2⟩)
      exact le_trans h1 (linear_term_le e he m hm4 J Y hJ hY hmJ)

/- English proof (translation)
The claim follows from `small_order_prime_bounds D.R.e D.host.two_le_e (2 ^ D.R.e) rfl`.
-/
theorem generic_frames_letters (D : D7) : Conclusion4 D 100 :=
  small_order_prime_bounds D.R.e D.host.two_le_e (2 ^ D.R.e) rfl

end Formalism.MainNotions.UnusedSlot33

end
