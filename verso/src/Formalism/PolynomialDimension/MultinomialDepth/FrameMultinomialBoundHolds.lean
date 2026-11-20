import Formalism.PolynomialDimension.StatementNum

noncomputable section

open scoped BigOperators
open Finset Real

namespace Formalism.CountingSumsFrames

/- English proof (translation)
Unfold `weylDim`. Rewrite using `[Fin.prod_univ_succ]`. Use `congr 1`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, lt_self_iff_false, if_false, one_mul, Fin.succ_pos, if_true, Fin.val_succ, Fin.val_zero]`.

Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_succ]`.

Simplify using `only [Fin.cons_succ, Fin.cons_zero, Fin.not_lt_zero, if_false, one_mul, Fin.succ_lt_succ_iff, Fin.val_succ]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Use `push_cast`. Apply the tactic sequence `congr 1 <;> ring`.

Both sides reduce to the same expression.
-/
theorem gram_weylDim_cons (n : ℕ) (A : ℤ) (μ : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons A μ : Fin (n + 1) → ℤ) =
      (∏ j : Fin n, ((((A - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n μ := by
  unfold weylDim
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, lt_self_iff_false, if_false, one_mul, Fin.succ_pos, if_true,
      Fin.val_succ, Fin.val_zero]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast
    ring
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_succ, Fin.cons_zero, Fin.not_lt_zero, if_false, one_mul, Fin.succ_lt_succ_iff,
      Fin.val_succ]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    split_ifs
    · push_cast
      congr 1 <;> ring
    · rfl

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Fin.prod_univ_castSucc]`.

Simplify using `only [Fin.val_castSucc, Fin.val_last]`. Rewrite using `[← ih]`. Establish `h` using `Nat.add_one_mul_choose_eq (a' + n) n`. Establish `h' : ((a' + n : ℝ) + 1) * (((a' + n).choose n : ℕ) : ℝ) = (((a' + n + 1).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1)` using `by exact_mod_cast h`. Rewrite using `[show a' + (n + 1) = a' + n + 1 by ring]`.

Establish `hn : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Rewrite using `[mul_div_assoc', eq_div_iff hn.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gram_choose_prod (a' : ℕ) : ∀ n : ℕ,
    (((a' + n).choose n : ℕ) : ℝ) = ∏ j : Fin n, ((a' : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    have h := Nat.add_one_mul_choose_eq (a' + n) n
    have h' : ((a' + n : ℝ) + 1) * (((a' + n).choose n : ℕ) : ℝ) =
        (((a' + n + 1).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast h
    rw [show a' + (n + 1) = a' + n + 1 by ring]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [mul_div_assoc', eq_div_iff hn.ne']
    linarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem gram_prod_le (m : ℕ) (f g : Fin m → ℝ) (t : ℝ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ (1 + t) * g j) :
    ∏ j, f j ≤ (1 + t) ^ m * ∏ j, g j := by
  calc ∏ j, f j ≤ ∏ j, ((1 + t) * g j) := Finset.prod_le_prod (fun j _ => hf j) (fun j _ => hfg j)
    _ = (1 + t) ^ m * ∏ j, g j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Establish `hp : 0 ≤ (1 + x) ^ n` using `by positivity`. Distinguish the cases in `h : 1 - y ≤ 0`. Use the polynomial consequences of the given equalities and inequalities. Rewrite `h` using `[not_le]`. Establish `e1 : 1 - y ≤ Real.exp (-y)` using `by linarith [Real.add_one_le_exp (-y)]`.

Establish `e2 : (1 + x) ^ n ≤ Real.exp (n * x)`. Rewrite using `[Real.exp_nat_mul]`. Conclude with `pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gram_key (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : (n : ℝ) * x ≤ y) :
    (1 - y) * (1 + x) ^ n ≤ 1 := by
  have hp : 0 ≤ (1 + x) ^ n := by positivity
  by_cases h : 1 - y ≤ 0
  · nlinarith
  · rw [not_le] at h
    have e1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have e2 : (1 + x) ^ n ≤ Real.exp (n * x) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
    calc (1 - y) * (1 + x) ^ n ≤ Real.exp (-y) * Real.exp (n * x) :=
          mul_le_mul e1 e2 hp (Real.exp_pos _).le
      _ = Real.exp (n * x - y) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero

/- English proof (translation)
Unfold `weylDim`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `j _`.

Use `split_ifs with h`. Establish `h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ)` using `by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)`. Establish `h2 : μ j ≤ μ i` using `hμ h.le`. Establish `h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ)` using `by exact_mod_cast h2`. Use `push_cast`.

Apply the tactic sequence `apply div_pos <;> linarith`. Conclude with `one_pos`.
-/
theorem gram_weylDim_pos (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by
  unfold weylDim
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j _
  split_ifs with h
  · have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)
    have h2 : μ j ≤ μ i := hμ h.le
    have h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ) := by exact_mod_cast h2
    push_cast
    apply div_pos <;> linarith
  · exact one_pos

/- English proof (translation)
Establish `hPW : 0 ≤ P * W` using `mul_nonneg hP0 hW`. Establish `hCW : 0 ≤ C * W` using `mul_nonneg hC hW`. Distinguish the cases in `h : 1 - y ≤ 0`. Use the polynomial consequences of the given equalities and inequalities. Rewrite `h` using `[not_le]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_sub_mul_mul_le (y P W C x : ℝ) (n : ℕ) (hW : 0 ≤ W) (hP0 : 0 ≤ P) (hC : 0 ≤ C)
    (hPle : P ≤ (1 + x) ^ n * C) (hkey : (1 - y) * (1 + x) ^ n ≤ 1) : (1 - y) * (P * W) ≤ C * W := by
  have hPW : 0 ≤ P * W := mul_nonneg hP0 hW
  have hCW : 0 ≤ C * W := mul_nonneg hC hW
  by_cases h : 1 - y ≤ 0
  · nlinarith
  · rw [not_le] at h
    calc (1 - y) * (P * W) ≤ (1 - y) * (((1 + x) ^ n * C) * W) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPle hW) h.le
      _ = ((1 - y) * (1 + x) ^ n) * (C * W) := by ring
      _ ≤ 1 * (C * W) := mul_le_mul_of_nonneg_right hkey hCW
      _ = C * W := one_mul _

end Formalism.CountingSumsFrames
