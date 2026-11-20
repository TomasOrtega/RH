import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `e1 : 6 ^ (m + 1) * (m + 1).factorial = 6 * (m + 1) * (6 ^ m * m.factorial)`. Rewrite using `[pow_succ, Nat.factorial_succ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (2 * (m + 1) + 1).factorial = (2 * m + 1 + 1 + 1) * (2 * m + 1 + 1) * (2 * m + 1).factorial`. Establish `h : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1` using `by ring`. Rewrite using `[h, Nat.factorial_succ, Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2]`. Combine the equalities or inequalities in the displayed calculation. Apply `Nat.mul_le_mul_right` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem six_pow_mul_factorial_le_factorial_two_mul_add_one (k : ℕ) :
    6 ^ k * k.factorial ≤ (2 * k + 1).factorial := by
  induction k with
  | zero => simp
  | succ m ih =>
    have e1 : 6 ^ (m + 1) * (m + 1).factorial = 6 * (m + 1) * (6 ^ m * m.factorial) := by
      rw [pow_succ, Nat.factorial_succ]; ring
    have e2 : (2 * (m + 1) + 1).factorial
        = (2 * m + 1 + 1 + 1) * (2 * m + 1 + 1) * (2 * m + 1).factorial := by
      have h : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]; ring
    rw [e1, e2]
    calc 6 * (m + 1) * (6 ^ m * m.factorial) ≤ 6 * (m + 1) * (2 * m + 1).factorial :=
          Nat.mul_le_mul_left _ ih
      _ ≤ (2 * m + 1 + 1 + 1) * (2 * m + 1 + 1) * (2 * m + 1).factorial := by
          apply Nat.mul_le_mul_right
          nlinarith

/- English proof (translation)
Establish `hn : ((6 : ℝ) ^ k * (k.factorial : ℝ)) ≤ ((2 * k + 1).factorial : ℝ)`. Conclude with `six_pow_mul_factorial_le_factorial_two_mul_add_one k` after adjusting the coercions. Rewrite using `[div_pow, div_div]`. Conclude with `div_le_div_of_nonneg_left (by positivity) (by positivity) hn`.
-/
private theorem sq_pow_div_odd_factorial_le_sq_div_six_pow_div_factorial (u : ℝ) (k : ℕ) :
    (u ^ 2) ^ k / ((2 * k + 1).factorial : ℝ) ≤ (u ^ 2 / 6) ^ k / (k.factorial : ℝ) := by
  have hn : ((6 : ℝ) ^ k * (k.factorial : ℝ)) ≤ ((2 * k + 1).factorial : ℝ) := by
    exact_mod_cast six_pow_mul_factorial_le_factorial_two_mul_add_one k
  rw [div_pow, div_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hn

/- English proof (translation)
Distinguish the cases in `hu : u = 0`. Substitute `hu` using the available equality. Simplify using `[shc]`. Establish `hs : HasSum (fun k : ℕ => (u ^ 2) ^ k / ((2 * k + 1).factorial : ℝ)) (shc u)`. Establish `h` using `(Real.hasSum_sinh u).div_const u`.

Rewrite using `[shc, if_neg hu]`. Establish `hfun : (fun k : ℕ => (u ^ 2) ^ k / ((2 * k + 1).factorial : ℝ)) = fun k : ℕ => u ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) / u`. Use function extensionality and compare the values at `k`. Establish `hF : ((2 * k + 1).factorial : ℝ) ≠ 0` using `by positivity`. Rewrite using `[← pow_mul, pow_succ]`.

Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`. Rewrite using `[hfun]`. Conclude with `h`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `le_hasSum hs 0 (fun j _ => by positivity)`. Simplify using `using h`. Use `hasSum_le_of_sum_le hs (fun s => ?_)` and prove the remaining obligations. Establish `hsub : s ⊆ Finset.range (s.sup id + 1)` using `fun i hi => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))`.

Combine the equalities or inequalities in the displayed calculation. Establish `hc : HasSum (fun k : ℕ => u ^ (2 * k) / ((2 * k).factorial : ℝ)) (Real.cosh u)` using `Real.hasSum_cosh u`. Establish `h1 : shc u ≤ Real.cosh u` using `hasSum_le (fun k => by`. Rewrite using `[pow_mul]`. Conclude with `div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast Nat.factorial_le (show 2 * k ≤ 2 * k + 1 by omega))) hs hc`.

Establish `h2 : Real.cosh u ≤ Real.exp |u|`. Rewrite using `[← Real.cosh_abs, Real.cosh_eq]`. Establish `: Real.exp (-|u|) ≤ Real.exp |u|` using `Real.exp_le_exp.2 (by linarith [abs_nonneg u])`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h1.trans h2`.
-/
theorem shc_bounds (u : ℝ) : 1 ≤ shc u ∧ shc u ≤ Real.exp (u ^ 2 / 6) ∧ shc u ≤ Real.exp |u| := by
  by_cases hu : u = 0
  · subst hu
    simp [shc]
  have hs : HasSum (fun k : ℕ => (u ^ 2) ^ k / ((2 * k + 1).factorial : ℝ)) (shc u) := by
    have h := (Real.hasSum_sinh u).div_const u
    rw [shc, if_neg hu]
    have hfun : (fun k : ℕ => (u ^ 2) ^ k / ((2 * k + 1).factorial : ℝ))
        = fun k : ℕ => u ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) / u := by
      funext k
      have hF : ((2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
      rw [← pow_mul, pow_succ]
      first
        | (field_simp; done)
        | (field_simp; ring)
    rw [hfun]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · have h := le_hasSum hs 0 (fun j _ => by positivity)
    simpa using h
  · refine hasSum_le_of_sum_le hs (fun s => ?_)
    have hsub : s ⊆ Finset.range (s.sup id + 1) := fun i hi =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    calc ∑ k ∈ s, (u ^ 2) ^ k / ((2 * k + 1).factorial : ℝ)
        ≤ ∑ k ∈ Finset.range (s.sup id + 1), (u ^ 2) ^ k / ((2 * k + 1).factorial : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ ≤ ∑ k ∈ Finset.range (s.sup id + 1), (u ^ 2 / 6) ^ k / (k.factorial : ℝ) :=
          Finset.sum_le_sum (fun k _ => sq_pow_div_odd_factorial_le_sq_div_six_pow_div_factorial u k)
      _ ≤ Real.exp (u ^ 2 / 6) := Real.sum_le_exp_of_nonneg (by positivity) _
  · have hc : HasSum (fun k : ℕ => u ^ (2 * k) / ((2 * k).factorial : ℝ)) (Real.cosh u) :=
      Real.hasSum_cosh u
    have h1 : shc u ≤ Real.cosh u := hasSum_le (fun k => by
        rw [pow_mul]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by exact_mod_cast Nat.factorial_le (show 2 * k ≤ 2 * k + 1 by omega))) hs hc
    have h2 : Real.cosh u ≤ Real.exp |u| := by
      rw [← Real.cosh_abs, Real.cosh_eq]
      have : Real.exp (-|u|) ≤ Real.exp |u| := Real.exp_le_exp.2 (by linarith [abs_nonneg u])
      linarith
    exact h1.trans h2

/- English proof (translation)
Unfold `Jac`. Rewrite using `[Real.exp_sum]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `a _`. Conclude with `Finset.prod_nonneg (fun b _ => le_trans zero_le_one (shc_bounds _).1)`.

Introduce `a _`. Rewrite using `[Real.exp_sum]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `b _`. Conclude with `le_trans zero_le_one (shc_bounds _).1`.

Introduce `b _`. Conclude with `hf _`.
-/
theorem jacobian_le_exp {ε : Fin n → Bool} (z : PCoord ε → ℂ) (f : ℝ → ℝ)
    (hf : ∀ u, shc u ≤ Real.exp (f u)) :
    Jac z ≤ Real.exp (∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b),
      f (pev z a - pev z b)) := by
  unfold Jac
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro a _
    exact Finset.prod_nonneg (fun b _ => le_trans zero_le_one (shc_bounds _).1)
  · intro a _
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro b _
      exact le_trans zero_le_one (shc_bounds _).1
    · intro b _
      exact hf _

/- English proof (translation)
Unfold `Jac`. Establish `h : ∀ a : Fin n, 1 ≤ ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (pev z a - pev z b)`. Introduce `a`. Establish `h1 : ∏ _b ∈ univ.filter (fun b : Fin n => a < b), (1 : ℝ) ≤ ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (pev z a - pev z b)` using `Finset.prod_le_prod (fun _ _ => zero_le_one) (fun b _ => (shc_bounds _).1)`. Simplify using `using h1`.

Establish `h2 : ∏ _a : Fin n, (1 : ℝ) ≤ ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (pev z a - pev z b)` using `Finset.prod_le_prod (fun _ _ => zero_le_one) (fun a _ => h a)`. Simplify using `using h2`.
-/
theorem jac_ge_one {ε : Fin n → Bool} (z : PCoord ε → ℂ) : 1 ≤ Jac z := by
  unfold Jac
  have h : ∀ a : Fin n,
      1 ≤ ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (pev z a - pev z b) := by
    intro a
    have h1 : ∏ _b ∈ univ.filter (fun b : Fin n => a < b), (1 : ℝ)
        ≤ ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (pev z a - pev z b) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) (fun b _ => (shc_bounds _).1)
    simpa using h1
  have h2 : ∏ _a : Fin n, (1 : ℝ)
      ≤ ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (pev z a - pev z b) :=
    Finset.prod_le_prod (fun _ _ => zero_le_one) (fun a _ => h a)
  simpa using h2

/- English proof (translation)
Establish `hA` using `pmat_isHermitian z`. Establish `hpev : ∀ a, pev z a = hA.eigenvalues a` using `fun a => rfl`. Use `set A := pmat z with hAdef`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef`. Use `set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef`.

Establish `hspec : A = U * D * star U`. Establish `h0` using `hA.spectral_theorem`. Rewrite `h0` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `h0`. Establish `hU : star U * U = 1` using `Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2`.

Establish `hAA2 : (A * A).trace = (D * D).trace`. Establish `e : A * A = U * (D * D) * star U`. Rewrite using `[hspec]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = U * (D * D) * star U := by rw [hU]; simp only [mul_one, mul_assoc]`. Rewrite using `[e, Matrix.trace_mul_comm, ← mul_assoc, hU, one_mul]`. Establish `hD : (D * D).trace = ∑ a : Fin n, (RCLike.ofReal (hA.eigenvalues a) : ℂ) ^ 2`. Rewrite using `[hDdef, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]`. Simplify using `only [Function.comp_apply, sq]`.

Establish `hAA : (A * A).trace = ∑ i : Fin n, ∑ j : Fin n, A i j * star (A i j)`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Rewrite using `[hA.apply j i]`. Establish `hmain : ∑ a : Fin n, (RCLike.ofReal (hA.eigenvalues a) : ℂ) ^ 2 = ∑ i : Fin n, ∑ j : Fin n, A i j * star (A i j)`.

Rewrite using `[← hAA, hAA2, hD]`. Establish `hre` using `congrArg (fun w : ℂ => RCLike.re w) hmain`. Simplify using `only [map_sum, RCLike.star_def, RCLike.mul_conj] at hre`. Simplify using `only [← RCLike.ofReal_pow, RCLike.ofReal_re] at hre`. Simplify using `only [hpev]`.

Unfold `S7.hs`. Conclude with `le_of_eq hre`.
-/
private theorem sum_pev_sq_le_hs_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∑ a : Fin n, pev z a ^ 2 ≤ hs (pmat z) := by
  have hA := pmat_isHermitian z
  have hpev : ∀ a, pev z a = hA.eigenvalues a := fun a => rfl
  set A := pmat z with hAdef
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  have hspec : A = U * D * star U := by
    have h0 := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h0
    exact h0
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hAA2 : (A * A).trace = (D * D).trace := by
    have e : A * A = U * (D * D) * star U := by
      rw [hspec]
      calc U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by
            simp only [mul_assoc]
        _ = U * (D * D) * star U := by rw [hU]; simp only [mul_one, mul_assoc]
    rw [e, Matrix.trace_mul_comm, ← mul_assoc, hU, one_mul]
  have hD : (D * D).trace = ∑ a : Fin n, (RCLike.ofReal (hA.eigenvalues a) : ℂ) ^ 2 := by
    rw [hDdef, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp only [Function.comp_apply, sq]
  have hAA : (A * A).trace = ∑ i : Fin n, ∑ j : Fin n, A i j * star (A i j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hA.apply j i]
  have hmain : ∑ a : Fin n, (RCLike.ofReal (hA.eigenvalues a) : ℂ) ^ 2
      = ∑ i : Fin n, ∑ j : Fin n, A i j * star (A i j) := by
    rw [← hAA, hAA2, hD]
  have hre := congrArg (fun w : ℂ => RCLike.re w) hmain
  simp only [map_sum, RCLike.star_def, RCLike.mul_conj] at hre
  simp only [← RCLike.ofReal_pow, RCLike.ofReal_re] at hre
  simp only [hpev]
  unfold S7.hs
  exact le_of_eq hre

/- English proof (translation)
Establish `h1 : ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x a - x b| ≤ ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), (|x a| + |x b|)` using `Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => by`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [le_abs_self (x a), le_abs_self (x b), neg_abs_le (x a), neg_abs_le (x b)]))`. Establish `e1 : ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), (|x a| + |x b|) = ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x a| + ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x b|`. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib)`. Establish `hsym : ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x b| = ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => b < a), |x a|`. Simplify using `only [Finset.sum_filter]`. Rewrite using `[Finset.sum_comm]`. Establish `hcount : ∀ a : Fin n, ∑ b : Fin n, ((if a < b then |x a| else 0) + (if b < a then |x a| else 0)) = ((n : ℝ) - 1) * |x a|`.

Introduce `a`. Establish `hpt : ∀ b : Fin n, (if a < b then |x a| else 0) + (if b < a then |x a| else 0) = |x a| - (if b = a then |x a| else 0)`. Introduce `b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, h.ne', not_lt.2 h.le]`.

Simplify using `[h]`. Simplify using `[h, h.ne, not_lt.2 h.le]`. Rewrite using `[Finset.sum_congr rfl (fun b _ => hpt b)]`. Use `first`. Consider the case `(simp [Finset.sum_sub_distrib]; done)`.

Consider the case `(simp [Finset.sum_sub_distrib]; ring)`. Establish `e2 : ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x a| + ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => b < a), |x a| = ((n : ℝ) - 1) * ∑ a : Fin n, |x a|`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]`.

Conclude with `hcount a`. Combine the linear relations using `[h1, e1, hsym, e2]`.
-/
private theorem sum_pairs_abs_sub_le_pred_mul_sum_abs (x : Fin n → ℝ) :
    ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x a - x b|
      ≤ ((n : ℝ) - 1) * ∑ a : Fin n, |x a| := by
  have h1 : ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x a - x b|
      ≤ ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), (|x a| + |x b|) :=
    Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => by
      rw [abs_le]
      constructor <;> linarith [le_abs_self (x a), le_abs_self (x b), neg_abs_le (x a),
        neg_abs_le (x b)]))
  have e1 : ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), (|x a| + |x b|)
      = ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x a|
        + ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x b| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib)
  have hsym : ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x b|
      = ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => b < a), |x a| := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  have hcount : ∀ a : Fin n,
      ∑ b : Fin n, ((if a < b then |x a| else 0) + (if b < a then |x a| else 0))
        = ((n : ℝ) - 1) * |x a| := by
    intro a
    have hpt : ∀ b : Fin n, (if a < b then |x a| else 0) + (if b < a then |x a| else 0)
        = |x a| - (if b = a then |x a| else 0) := by
      intro b
      rcases lt_trichotomy a b with h | h | h
      · simp [h, h.ne', not_lt.2 h.le]
      · simp [h]
      · simp [h, h.ne, not_lt.2 h.le]
    rw [Finset.sum_congr rfl (fun b _ => hpt b)]
    first
      | (simp [Finset.sum_sub_distrib]; done)
      | (simp [Finset.sum_sub_distrib]; ring)
  have e2 : ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |x a|
        + ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => b < a), |x a|
      = ((n : ℝ) - 1) * ∑ a : Fin n, |x a| := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    exact hcount a
  linarith [h1, e1, hsym, e2]

/- English proof (translation)
Unfold `pmat`. Simplify using `[h]`.
-/
private theorem pmat_eq_zero_of_sign_eq {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a b : Fin n)
    (h : ε a = ε b) : pmat z a b = 0 := by
  unfold pmat
  simp [h]

/- English proof (translation)
Unfold `Matrix.rank`. Establish `hle : LinearMap.range (P + Q).mulVecLin ≤ LinearMap.range P.mulVecLin ⊔ LinearMap.range Q.mulVecLin`. Introduce and unpack `_ ⟨v, rfl⟩`. Establish `e : (P + Q).mulVecLin v = P.mulVecLin v + Q.mulVecLin v`. Simplify using `[Matrix.mulVecLin_apply, Matrix.add_mulVec]`.

Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ v)`. Conclude with `(Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)`.
-/
private theorem matrix_rank_add_le' (P Q : Matrix (Fin n) (Fin n) ℂ) :
    (P + Q).rank ≤ P.rank + Q.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (P + Q).mulVecLin
      ≤ LinearMap.range P.mulVecLin ⊔ LinearMap.range Q.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    have e : (P + Q).mulVecLin v = P.mulVecLin v + Q.mulVecLin v := by
      simp [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ v)
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

/- English proof (translation)
Use `set dT : Fin n → ℂ := fun a => if ε a = true then 1 else 0 with hdT`. Use `set dF : Fin n → ℂ := fun a => if ε a = false then 1 else 0 with hdF`. Establish `hsplit : pmat z = diagonal dT * pmat z * diagonal dF + diagonal dF * pmat z * diagonal dT`. Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hdT, hdF]`.

Distinguish the cases in `h : ε a = ε b`. Rewrite using `[pmat_eq_zero_of_sign_eq z a b h]`. Simplify using the standard rewrite rules. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all`. Establish `hT : (diagonal dT).rank = pOf ε`.

Rewrite using `[Matrix.rank_diagonal, Fintype.card_subtype]`. Unfold `pOf`. Use `congr 1`. Use extensionality with `a`. Apply the tactic sequence `by_cases hε : ε a = true <;> simp [hdT, hε]`.

Establish `hF : (diagonal dF).rank = qOf ε`. Rewrite using `[Matrix.rank_diagonal, Fintype.card_subtype]`. Unfold `qOf`. Use `congr 1`. Use extensionality with `a`.

Apply the tactic sequence `by_cases hε : ε a = false <;> simp [hdF, hε]`. Establish `h1 : (diagonal dT * pmat z * diagonal dF).rank ≤ q0 ε`. Unfold `S7.q0`. Use `le_min ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (diagonal dF * pmat z * diagonal dT).rank ≤ q0 ε`. Unfold `S7.q0`. Use `le_min ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hsplit]`. Use `_ ≤ _ := matrix_rank_add_le' _ _`. Use `_ ≤ q0 ε + q0 ε := Nat.add_le_add h1 h2`.

Use `_ = 2 * q0 ε := by ring`.
-/
private theorem rank_pmat_le_two_mul_q0_count {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    (pmat z).rank ≤ 2 * q0 ε := by
  set dT : Fin n → ℂ := fun a => if ε a = true then 1 else 0 with hdT
  set dF : Fin n → ℂ := fun a => if ε a = false then 1 else 0 with hdF
  have hsplit : pmat z
      = diagonal dT * pmat z * diagonal dF + diagonal dF * pmat z * diagonal dT := by
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hdT, hdF]
    by_cases h : ε a = ε b
    · rw [pmat_eq_zero_of_sign_eq z a b h]; simp
    · cases ha : ε a <;> cases hb : ε b <;> simp_all
  have hT : (diagonal dT).rank = pOf ε := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    unfold pOf
    congr 1
    ext a
    by_cases hε : ε a = true <;> simp [hdT, hε]
  have hF : (diagonal dF).rank = qOf ε := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    unfold qOf
    congr 1
    ext a
    by_cases hε : ε a = false <;> simp [hdF, hε]
  have h1 : (diagonal dT * pmat z * diagonal dF).rank ≤ q0 ε := by
    unfold S7.q0
    refine le_min ?_ ?_
    · calc _ ≤ (diagonal dT * pmat z).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (diagonal dT).rank := Matrix.rank_mul_le_left _ _
        _ = pOf ε := hT
    · calc _ ≤ (diagonal dF).rank := Matrix.rank_mul_le_right _ _
        _ = qOf ε := hF
  have h2 : (diagonal dF * pmat z * diagonal dT).rank ≤ q0 ε := by
    unfold S7.q0
    refine le_min ?_ ?_
    · calc _ ≤ (diagonal dT).rank := Matrix.rank_mul_le_right _ _
        _ = pOf ε := hT
    · calc _ ≤ (diagonal dF * pmat z).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (diagonal dF).rank := Matrix.rank_mul_le_left _ _
        _ = qOf ε := hF
  calc (pmat z).rank
      = (diagonal dT * pmat z * diagonal dF + diagonal dF * pmat z * diagonal dT).rank := by
        rw [← hsplit]
    _ ≤ _ := matrix_rank_add_le' _ _
    _ ≤ q0 ε + q0 ε := Nat.add_le_add h1 h2
    _ = 2 * q0 ε := by ring

/- English proof (translation)
Establish `hA` using `pmat_isHermitian z`. Establish `hcard : ((univ.filter (fun a : Fin n => pev z a ≠ 0)).card : ℝ) ≤ 2 * (q0 ε : ℝ)`. Establish `h1` using `hA.rank_eq_card_non_zero_eigs`. Establish `h2` using `rank_pmat_le_two_mul_q0_count z`. Rewrite `h2` using `[h1, Fintype.card_subtype]`.

Conclude with `h2` after adjusting the coercions. Establish `hcs` using `Finset.sum_mul_sq_le_sq_mul_sq univ (fun a : Fin n => if pev z a ≠ 0 then (1 : ℝ) else 0) (fun a => |pev z a|)`. Establish `e1 : ∑ a : Fin n, (if pev z a ≠ 0 then (1 : ℝ) else 0) * |pev z a| = ∑ a : Fin n, |pev z a|`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : pev z a = 0 <;> simp [h]`.

Establish `e2 : ∑ a : Fin n, (if pev z a ≠ 0 then (1 : ℝ) else 0) ^ 2 = ((univ.filter (fun a : Fin n => pev z a ≠ 0)).card : ℝ)`. Rewrite using `[Finset.card_filter]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : pev z a = 0 <;> simp [h]`.

Establish `e3 : ∑ a : Fin n, |pev z a| ^ 2 = ∑ a : Fin n, pev z a ^ 2`. Simplify using `only [sq_abs]`. Rewrite `hcs` using `[e1, e2, e3]`. Establish `hsq` using `sum_pev_sq_le_hs_pmat z`. Establish `hq : (0 : ℝ) ≤ 2 * (q0 ε : ℝ)` using `by positivity`.

Establish `hs0 : (0 : ℝ) ≤ ∑ a : Fin n, pev z a ^ 2` using `Finset.sum_nonneg (fun a _ => sq_nonneg _)`. Establish `hfin : (∑ a : Fin n, |pev z a|) ^ 2 ≤ 2 * (q0 ε : ℝ) * hs (pmat z)` using `hcs.trans (mul_le_mul hcard hsq hs0 hq)`. Rewrite using `[← Real.sqrt_mul hq]`. Conclude with `(le_abs_self _).trans (Real.abs_le_sqrt hfin)`.
-/
private theorem sum_abs_pev_le_sqrt_two_q0_mul_sqrt_hs {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∑ a : Fin n, |pev z a| ≤ Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (hs (pmat z)) := by
  have hA := pmat_isHermitian z
  have hcard : ((univ.filter (fun a : Fin n => pev z a ≠ 0)).card : ℝ) ≤ 2 * (q0 ε : ℝ) := by
    have h1 := hA.rank_eq_card_non_zero_eigs
    have h2 := rank_pmat_le_two_mul_q0_count z
    rw [h1, Fintype.card_subtype] at h2
    exact_mod_cast h2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun a : Fin n => if pev z a ≠ 0 then (1 : ℝ) else 0) (fun a => |pev z a|)
  have e1 : ∑ a : Fin n, (if pev z a ≠ 0 then (1 : ℝ) else 0) * |pev z a|
      = ∑ a : Fin n, |pev z a| := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : pev z a = 0 <;> simp [h]
  have e2 : ∑ a : Fin n, (if pev z a ≠ 0 then (1 : ℝ) else 0) ^ 2
      = ((univ.filter (fun a : Fin n => pev z a ≠ 0)).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : pev z a = 0 <;> simp [h]
  have e3 : ∑ a : Fin n, |pev z a| ^ 2 = ∑ a : Fin n, pev z a ^ 2 := by
    simp only [sq_abs]
  rw [e1, e2, e3] at hcs
  have hsq := sum_pev_sq_le_hs_pmat z
  have hq : (0 : ℝ) ≤ 2 * (q0 ε : ℝ) := by positivity
  have hs0 : (0 : ℝ) ≤ ∑ a : Fin n, pev z a ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hfin : (∑ a : Fin n, |pev z a|) ^ 2 ≤ 2 * (q0 ε : ℝ) * hs (pmat z) :=
    hcs.trans (mul_le_mul hcard hsq hs0 hq)
  rw [← Real.sqrt_mul hq]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hfin)

/- English proof (translation)
Establish `h` using `jacobian_le_exp z (fun u => |u|) (fun u => (shc_bounds u).2.2)`. Establish `hpos : 0 < Jac z` using `lt_of_lt_of_le zero_lt_one (jac_ge_one z)`. Rewrite using `[Real.log_le_iff_le_exp hpos]`. Use `h.trans (Real.exp_le_exp.2 ?_)` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases.

Substitute `hn` using the available equality. Simplify using `[rhoP, S7.hs]`. Establish `hn1 : (0 : ℝ) ≤ (n : ℝ) - 1`. Establish `: (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_jac_le_rho {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    Real.log (Jac z) ≤ ((n : ℝ) - 1) * rhoP z := by
  have h := jacobian_le_exp z (fun u => |u|) (fun u => (shc_bounds u).2.2)
  have hpos : 0 < Jac z := lt_of_lt_of_le zero_lt_one (jac_ge_one z)
  rw [Real.log_le_iff_le_exp hpos]
  refine h.trans (Real.exp_le_exp.2 ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [rhoP, S7.hs]
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc ∑ a : Fin n, ∑ b ∈ univ.filter (fun b : Fin n => a < b), |pev z a - pev z b|
      ≤ ((n : ℝ) - 1) * ∑ a : Fin n, |pev z a| := sum_pairs_abs_sub_le_pred_mul_sum_abs (pev z)
    _ ≤ ((n : ℝ) - 1) * rhoP z := mul_le_mul_of_nonneg_left (sum_abs_pev_le_sqrt_two_q0_mul_sqrt_hs z) hn1

end ReciprocityTheory.ChartRestriction.DS
