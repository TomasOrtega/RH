import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation

open Polynomial Finset

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) h.ne` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, max_eq_right h.le]`. Then use the resulting hypothesis.
-/
theorem norm_eq_of_norm_sub_lt' {a b : ℂ_[l]} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) h.ne
  rwa [sub_add_cancel, max_eq_right h.le] at this

/- English proof (translation)
Establish `hsplit : (P.roots.map fun a => X - C a).prod = P` using `prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP IsAlgClosed.card_roots_eq_natDegree`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `key : ∀ s : Multiset ℂ_[l], (∀ a ∈ s, 1 ≤ ‖x - a‖) → 1 ≤ ‖((s.map fun a => X - C a).prod).eval x‖`. Introduce `s`.

Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => intro _`. Simplify using the standard rewrite rules. Consider the case `cons a s ih`. Introduce `hs`.

Rewrite using `[Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul]`. Simplify using `only [eval_sub, eval_X, eval_C]`. Conclude with `one_le_mul_of_one_le_of_one_le (hs a (Multiset.mem_cons_self _ _)) (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))`. Use `key P.roots (fun a ha => hcon a ((mem_roots hP.ne_zero).1 ha))` as an intermediate fact. Rewrite `this` using `[hsplit]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_root_near (P : ℂ_[l][X]) (hP : P.Monic) (x : ℂ_[l]) (h : ‖P.eval x‖ < 1) :
    ∃ a, P.IsRoot a ∧ ‖x - a‖ < 1 := by
  have hsplit : (P.roots.map fun a => X - C a).prod = P :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP IsAlgClosed.card_roots_eq_natDegree
  by_contra hcon
  push Not at hcon
  have key : ∀ s : Multiset ℂ_[l], (∀ a ∈ s, 1 ≤ ‖x - a‖) →
      1 ≤ ‖((s.map fun a => X - C a).prod).eval x‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul]
      simp only [eval_sub, eval_X, eval_C]
      exact one_le_mul_of_one_le_of_one_le (hs a (Multiset.mem_cons_self _ _))
        (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))
  have := key P.roots (fun a ha => hcon a ((mem_roots hP.ne_zero).1 ha))
  rw [hsplit] at this
  linarith

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1)` using `by ring`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)` and prove the remaining obligations. Rewrite using `[norm_mul, hy, one_mul]`. Conclude with `ih`.
-/
theorem norm_pow_sub_one_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) : ‖y ^ k - 1‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hy, one_mul]
    exact ih

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : (∑ i ∈ range (k + 1), y ^ i) - ((k + 1 : ℕ) : ℂ_[l]) = ((∑ i ∈ range k, y ^ i) - k) + (y ^ k - 1)`. Rewrite using `[sum_range_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (norm_pow_sub_one_le l hy k))`.
-/
theorem norm_geom_sum_sub_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) :
    ‖(∑ i ∈ range k, y ^ i) - k‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (∑ i ∈ range (k + 1), y ^ i) - ((k + 1 : ℕ) : ℂ_[l]) =
        ((∑ i ∈ range k, y ^ i) - k) + (y ^ k - 1) := by
      rw [sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (norm_pow_sub_one_le l hy k))

/- English proof (translation)
Establish `hy1 : ‖y‖ = 1`. Use `norm_eq_of_norm_sub_lt' l (a := y) (b := 1) (by rwa [norm_one])` as an intermediate fact. Rewrite `this` using `[norm_one]`. Then use the resulting hypothesis. Use `norm_geom_sum_sub_le l hy1 m` as an intermediate fact. Rewrite using `[← hm]`.

Conclude with `norm_eq_of_norm_sub_lt' l (by rw [hm]; exact lt_of_le_of_lt this hy)`.
-/
theorem norm_geom_sum_eq_one {y : ℂ_[l]} (hy : ‖y - 1‖ < 1) {m : ℕ} (hm : ‖(m : ℂ_[l])‖ = 1) :
    ‖∑ i ∈ range m, y ^ i‖ = 1 := by
  have hy1 : ‖y‖ = 1 := by
    have := norm_eq_of_norm_sub_lt' l (a := y) (b := 1) (by rwa [norm_one])
    rwa [norm_one] at this
  have := norm_geom_sum_sub_le l hy1 m
  rw [← hm]
  exact norm_eq_of_norm_sub_lt' l (by rw [hm]; exact lt_of_le_of_lt this hy)

end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
