import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe14.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : η ^ (n + 1) - 1 = (η ^ n - 1) * (η - 1) + ((η ^ n - 1) + (η - 1))` using `by ring`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ih h.le`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih h)`.
-/
private lemma UpperTheory.Reformulated.B.Qe14.pow_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖η ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : η ^ (n + 1) - 1 = (η ^ n - 1) * (η - 1) + ((η ^ n - 1) + (η - 1)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ih h.le
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih h)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : ∑ i ∈ Finset.range (n + 1), η ^ i - ((n + 1 : ℕ) : K) = (∑ i ∈ Finset.range n, η ^ i - (n : K)) + (η ^ n - 1)`. Rewrite using `[Finset.sum_range_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (UpperTheory.Reformulated.B.Qe14.pow_close h n))`.
-/
private lemma UpperTheory.Reformulated.B.Qe14.sum_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖∑ i ∈ Finset.range n, η ^ i - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∑ i ∈ Finset.range (n + 1), η ^ i - ((n + 1 : ℕ) : K)
        = (∑ i ∈ Finset.range n, η ^ i - (n : K)) + (η ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt ih (UpperTheory.Reformulated.B.Qe14.pow_close h n))

/- English proof (translation)
Introduce `v inst m hm η hη h`. Assume the negation of the conclusion as `hne`. Establish `h1 : (∑ i ∈ Finset.range m, η ^ i) * (η - 1) = 0`. Rewrite using `[geom_sum_mul, hη, sub_self]`. Establish `h2 : ∑ i ∈ Finset.range m, η ^ i = 0` using `(mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)`.

Establish `h3` using `UpperTheory.Reformulated.B.Qe14.sum_close h m`. Rewrite `h3` using `[h2, zero_sub, norm_neg]`. Establish `h4 : ((m : ℕ) : PadicAlgCl v) = algebraMap ℚ_[v] (PadicAlgCl v) (m : ℚ_[v])`. Simplify using the standard rewrite rules. Establish `h5 : ‖((m : ℕ) : PadicAlgCl v)‖ = ‖(m : ℚ_[v])‖`.

Rewrite using `[h4]`. Conclude with `PadicAlgCl.norm_extends v _`. Rewrite `h3` using `[h5, Padic.norm_natCast_lt_one_iff]`. Conclude with `hm h3`.
-/
theorem UpperTheory.Reformulated.B.Qe14.root_eq_one :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {m : ℕ},
      ¬v ∣ m →
        ∀ {η : UpperTheory.Reformulated.B.Qe14.Om v},
          η ^ m = (1 : UpperTheory.Reformulated.B.Qe14.Om v) →
            ‖η - (1 : UpperTheory.Reformulated.B.Qe14.Om v)‖ < (1 : ℝ) → η = (1 : UpperTheory.Reformulated.B.Qe14.Om v) := by
  intro v inst m hm η hη h
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, η ^ i) * (η - 1) = 0 := by
    rw [geom_sum_mul, hη, sub_self]
  have h2 : ∑ i ∈ Finset.range m, η ^ i = 0 :=
    (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)
  have h3 := UpperTheory.Reformulated.B.Qe14.sum_close h m
  rw [h2, zero_sub, norm_neg] at h3
  have h4 : ((m : ℕ) : PadicAlgCl v) = algebraMap ℚ_[v] (PadicAlgCl v) (m : ℚ_[v]) := by
    simp
  have h5 : ‖((m : ℕ) : PadicAlgCl v)‖ = ‖(m : ℚ_[v])‖ := by
    rw [h4]; exact PadicAlgCl.norm_extends v _
  rw [h5, Padic.norm_natCast_lt_one_iff] at h3
  exact hm h3
