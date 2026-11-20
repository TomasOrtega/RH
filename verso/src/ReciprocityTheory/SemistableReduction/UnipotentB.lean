import ReciprocityTheory.SemistableReduction.LatSemiSt

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ', ← Matrix.mulVec_mulVec, pow_succ']`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unip_normSq_pow_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (u : Fin r → ℂ) :
    normSq ((A ^ n) *ᵥ u) ≤ c ^ n * normSq u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ']
    calc normSq (A *ᵥ (A ^ n *ᵥ u)) ≤ c * normSq (A ^ n *ᵥ u) := hA _
      _ ≤ c * (c ^ n * normSq u) := mul_le_mul_of_nonneg_left ih hc
      _ = c * c ^ n * normSq u := by ring

/- English proof (translation)
Unfold `normSq`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem unip_normSq_col {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    normSq (M *ᵥ Pi.single j 1) = ∑ i, ‖M i j‖ ^ 2 := by
  unfold normSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_single_one]
  rfl

/- English proof (translation)
Unfold `normSq`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem unip_normSq_single {r : ℕ} (j : Fin r) : normSq (Pi.single j (1 : ℂ)) = 1 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/- English proof (translation)
Establish `h1` using `unip_normSq_pow_le A c hc hA n (Pi.single i 1)`. Rewrite `h1` using `[unip_normSq_col, unip_normSq_single, mul_one]`. Use `le_trans ?_ h1` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun k => ‖(A ^ n) k i‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)`.
-/
theorem unip_diag_sq_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (i : Fin r) :
    ‖(A ^ n) i i‖ ^ 2 ≤ c ^ n := by
  have h1 := unip_normSq_pow_le A c hc hA n (Pi.single i 1)
  rw [unip_normSq_col, unip_normSq_single, mul_one] at h1
  refine le_trans ?_ h1
  exact Finset.single_le_sum (f := fun k => ‖(A ^ n) k i‖ ^ 2) (fun k _ => by positivity)
    (Finset.mem_univ i)

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Establish `h` using `hA (Pi.single b 1)`. Rewrite `h` using `[unip_normSq_single, mul_one]`. Then use the resulting hypothesis.

Use `_ = r * c := by simp`.
-/
theorem unip_hs_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) :
    ∑ a, ∑ b, ‖A a b‖ ^ 2 ≤ r * c := by
  rw [Finset.sum_comm]
  calc ∑ b, ∑ a, ‖A a b‖ ^ 2 = ∑ b : Fin r, normSq (A *ᵥ Pi.single b 1) :=
        Finset.sum_congr rfl fun b _ => (unip_normSq_col A b).symm
    _ ≤ ∑ _b : Fin r, c := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h := hA (Pi.single b 1)
        rwa [unip_normSq_single, mul_one] at h
    _ = r * c := by simp

/- English proof (translation)
Establish `key : ∀ a b, ‖(A - 1) a b‖ ^ 2 = ‖A a b‖ ^ 2 - (if a = b then 2 * (A a b).re - 1 else 0)`. Introduce `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `only [Matrix.sub_apply, Matrix.one_apply_eq, if_true, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.sub_apply, Matrix.one_apply_ne h, h]`. Repeatedly rewrite using `[key, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Matrix.trace, Complex.re_sum]`. Simplify using `[Finset.sum_sub_distrib, Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem unip_hs_sub_one {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ∑ a, ∑ b, ‖(A - 1) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 - 2 * A.trace.re + r := by
  have key : ∀ a b, ‖(A - 1) a b‖ ^ 2 =
      ‖A a b‖ ^ 2 - (if a = b then 2 * (A a b).re - 1 else 0) := by
    intro a b
    by_cases h : a = b
    · subst h
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, if_true, Complex.sq_norm,
        Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    · simp [Matrix.sub_apply, Matrix.one_apply_ne h, h]
  simp_rw [key, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Matrix.trace, Complex.re_sum]
  simp [Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/- English proof (translation)
Establish `hr' : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hx0 : 0 < 2 / (3 * (r : ℝ))` using `by positivity`. Use `set x : ℝ := 2 / (3 * (r : ℝ)) with hx`. Establish `hxr : (r : ℝ) * x = 2 / 3` using `by rw [hx]; field_simp`. Establish `hx1 : x ≤ 2 / 3` using `by nlinarith`.

Establish `hb` using `Real.exp_bound (x := x) (by rw [abs_of_pos hx0]; linarith) (n := 4) (by norm_num)`. Rewrite `hb` using `[abs_of_pos hx0]`. Establish `hup` using `(abs_le.mp hb).2`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hup`. Evaluate the numerical expressions using `at hup`.

Establish `hmain : Real.exp x - 1 < 3 / 2 * x`. Use polynomial arithmetic with `[pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4, mul_le_mul_of_nonneg_left hx1 (le_of_lt (pow_pos hx0 3))]`. Establish `hr0 : (0 : ℝ) < r` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unip_exp_bound (r : ℕ) (hr : 1 ≤ r) : (r : ℝ) * (Real.exp (2 / (3 * r)) - 1) < 1 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : 0 < 2 / (3 * (r : ℝ)) := by positivity
  set x : ℝ := 2 / (3 * (r : ℝ)) with hx
  have hxr : (r : ℝ) * x = 2 / 3 := by rw [hx]; field_simp
  have hx1 : x ≤ 2 / 3 := by nlinarith
  have hb := Real.exp_bound (x := x) (by rw [abs_of_pos hx0]; linarith) (n := 4) (by norm_num)
  rw [abs_of_pos hx0] at hb
  have hup := (abs_le.mp hb).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hup
  norm_num at hup
  have hmain : Real.exp x - 1 < 3 / 2 * x := by
    nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4, mul_le_mul_of_nonneg_left hx1 (le_of_lt (pow_pos hx0 3))]
  have hr0 : (0 : ℝ) < r := by linarith
  calc (r : ℝ) * (Real.exp x - 1) < r * (3 / 2 * x) := mul_lt_mul_of_pos_left hmain hr0
    _ = 1 := by rw [show (r : ℝ) * (3 / 2 * x) = 3 / 2 * (r * x) by ring, hxr]; norm_num

end ReciprocityTheory.MultiplicativeHeights
