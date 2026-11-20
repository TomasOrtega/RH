import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec

open Finset

noncomputable section

namespace PI.ET

/- English proof (translation)
Introduce `n a b`. Establish `hA : 0 ≤ ∑ i, a i ^ 2` using `Finset.sum_nonneg fun i _ => sq_nonneg _`. Establish `hB : 0 ≤ ∑ i, b i ^ 2` using `Finset.sum_nonneg fun i _ => sq_nonneg _`. Establish `hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)` using `Real.sum_mul_le_sqrt_mul_sqrt _ _ _`. Rewrite using `[Real.sqrt_le_left (by positivity)]`.

Establish `e : ∑ i, (a i + b i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2`. Simplify using `only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]`. Use `congr 1`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem euclTri : EuclTri := by
  intro n a b
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  rw [Real.sqrt_le_left (by positivity)]
  have e : ∑ i, (a i + b i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro _ _ t _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `ha hc t ht`. Establish `ih'` using `ih (fun i j hij hj => ha i j hij (by omega)) (fun k hk => hc k (by omega)) (a n) (fun i hi => ha i n hi.le (by omega))`. Establish `hS : 0 ≤ ∑ i ∈ range (n + 1), c i` using `hc (n + 1) le_rfl`. Establish `htn : t ≤ a n` using `ht n (by omega)`. Rewrite `hS`, the goal using `[Finset.sum_range_succ]`.

Rewrite using `[Finset.sum_range_succ]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem abel_nat (a c : ℕ → ℝ) : ∀ (n : ℕ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    (∀ k ≤ n, 0 ≤ ∑ i ∈ range k, c i) → ∀ t : ℝ, (∀ i < n, t ≤ a i) →
    t * ∑ i ∈ range n, c i ≤ ∑ i ∈ range n, a i * c i := by
  intro n
  induction n with
  | zero => intro _ _ t _; simp
  | succ n ih =>
    intro ha hc t ht
    have ih' := ih (fun i j hij hj => ha i j hij (by omega)) (fun k hk => hc k (by omega)) (a n)
      (fun i hi => ha i n hi.le (by omega))
    have hS : 0 ≤ ∑ i ∈ range (n + 1), c i := hc (n + 1) le_rfl
    have htn : t ≤ a n := ht n (by omega)
    rw [Finset.sum_range_succ] at hS ⊢
    rw [Finset.sum_range_succ]
    nlinarith

/- English proof (translation)
Unfold `psum`. Rewrite using `[Finset.sum_filter]`. Establish `h1 : ∑ i : Fin n, (if i.val < k then f i else 0) = ∑ i : Fin n, (fun m => if m < k then (if h : m < n then f ⟨m, h⟩ else 0) else 0) i.val`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Simplify using `[i.isLt]`. Rewrite using `[h1, Fin.sum_univ_eq_sum_range (fun m => if m < k then (if h : m < n then f ⟨m, h⟩ else 0) else 0) n, ← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `m`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem psum_eq_range {n : ℕ} (f : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    psum f k = ∑ i ∈ range k, (fun m => if h : m < n then f ⟨m, h⟩ else 0) i := by
  unfold psum
  rw [Finset.sum_filter]
  have h1 : ∑ i : Fin n, (if i.val < k then f i else 0) =
      ∑ i : Fin n, (fun m => if m < k then (if h : m < n then f ⟨m, h⟩ else 0) else 0) i.val := by
    apply Finset.sum_congr rfl; intro i _; simp [i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range (fun m => if m < k then (if h : m < n then f ⟨m, h⟩ else 0) else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega

/- English proof (translation)
Rewrite using `[← Fin.sum_univ_eq_sum_range]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Simplify using `[i.isLt]`.
-/
theorem sum_eq_range {n : ℕ} (f : Fin n → ℝ) :
    ∑ i, f i = ∑ i ∈ range n, (fun m => if h : m < n then f ⟨m, h⟩ else 0) i := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl; intro i _; simp [i.isLt]

/- English proof (translation)
Introduce `n a b ha hk htot`. Use `set a' : ℕ → ℝ := fun m => if h : m < n then a ⟨m, h⟩ else 0 with ha'`. Use `set c' : ℕ → ℝ := fun m => if h : m < n then (b ⟨m, h⟩ - a ⟨m, h⟩) else 0 with hc'`. Establish `hc : ∀ k ≤ n, 0 ≤ ∑ i ∈ range k, c' i`. Introduce `k hkn`.

Use `hk k hkn` as an intermediate fact. Rewrite `this` using `[psum_eq_range a k hkn, psum_eq_range b k hkn]`. Establish `e : ∑ i ∈ range k, c' i = ∑ i ∈ range k, (fun m => if h : m < n then b ⟨m, h⟩ else 0) i - ∑ i ∈ range k, (fun m => if h : m < n then a ⟨m, h⟩ else 0) i`. Rewrite using `[← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `m _`. Apply the tactic sequence `simp only [hc']; split_ifs <;> simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmono : ∀ i j, i ≤ j → j < n → a' j ≤ a' i`. Introduce `i j hij hj`.

Simplify using `only [ha', dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]`. Conclude with `ha (show (⟨i, lt_of_le_of_lt hij hj⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)`. Use `set t : ℝ := -∑ i ∈ range n, |a' i| with ht`. Establish `htle : ∀ i < n, t ≤ a' i`. Introduce `i hi`.

Establish `: |a' i| ≤ ∑ i ∈ range n, |a' i|` using `Finset.single_le_sum (f := fun i => |a' i|) (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hi)`. Use `neg_abs_le (a' i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `abel_nat a' c' n hmono hc t htle`. Establish `hc0 : ∑ i ∈ range n, c' i = 0`.

Establish `e1 : ∑ i, (b i - a i) = 0` using `by rw [Finset.sum_sub_distrib, htot]; ring`. Rewrite `e1` using `[sum_eq_range (fun i => b i - a i)]`. Rewrite using `[← e1]`. Rewrite `key` using `[hc0, mul_zero]`. Establish `hab : 0 ≤ ∑ i, a i * (b i - a i)`.

Rewrite using `[sum_eq_range (fun i => a i * (b i - a i))]`. Use `key using 2 with m` and compare the differences between its conclusion and the goal. Apply the tactic sequence `simp only [ha', hc']; split_ifs <;> simp`. Establish `h1 : ∑ i, a i ^ 2 ≤ ∑ i, a i * b i`. Establish `: ∑ i, a i * (b i - a i) = ∑ i, a i * b i - ∑ i, a i ^ 2`.

Rewrite using `[← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)` using `Real.sum_mul_le_sqrt_mul_sqrt _ _ _`. Establish `hA : 0 ≤ ∑ i, a i ^ 2` using `Finset.sum_nonneg fun i _ => sq_nonneg _`. Establish `hB : 0 ≤ ∑ i, b i ^ 2` using `Finset.sum_nonneg fun i _ => sq_nonneg _`. Establish `x0` using `Real.sqrt_nonneg (∑ i, a i ^ 2)`. Establish `y0` using `Real.sqrt_nonneg (∑ i, b i ^ 2)`.

Establish `hx` using `Real.sq_sqrt hA`. Establish `hy` using `Real.sq_sqrt hB`. Use polynomial arithmetic with `[sq_nonneg (Real.sqrt (∑ i, a i ^ 2) - Real.sqrt (∑ i, b i ^ 2)), mul_nonneg x0 y0]`.
-/
theorem abelSq : AbelSq := by
  intro n a b ha hk htot

  set a' : ℕ → ℝ := fun m => if h : m < n then a ⟨m, h⟩ else 0 with ha'
  set c' : ℕ → ℝ := fun m => if h : m < n then (b ⟨m, h⟩ - a ⟨m, h⟩) else 0 with hc'
  have hc : ∀ k ≤ n, 0 ≤ ∑ i ∈ range k, c' i := by
    intro k hkn
    have := hk k hkn
    rw [psum_eq_range a k hkn, psum_eq_range b k hkn] at this
    have e : ∑ i ∈ range k, c' i = ∑ i ∈ range k, (fun m => if h : m < n then b ⟨m, h⟩ else 0) i -
        ∑ i ∈ range k, (fun m => if h : m < n then a ⟨m, h⟩ else 0) i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro m _
      simp only [hc']; split_ifs <;> simp
    linarith
  have hmono : ∀ i j, i ≤ j → j < n → a' j ≤ a' i := by
    intro i j hij hj
    simp only [ha', dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
    exact ha (show (⟨i, lt_of_le_of_lt hij hj⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  set t : ℝ := -∑ i ∈ range n, |a' i| with ht
  have htle : ∀ i < n, t ≤ a' i := by
    intro i hi
    have : |a' i| ≤ ∑ i ∈ range n, |a' i| :=
      Finset.single_le_sum (f := fun i => |a' i|) (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hi)
    have := neg_abs_le (a' i)
    linarith
  have key := abel_nat a' c' n hmono hc t htle
  have hc0 : ∑ i ∈ range n, c' i = 0 := by
    have e1 : ∑ i, (b i - a i) = 0 := by rw [Finset.sum_sub_distrib, htot]; ring
    rw [sum_eq_range (fun i => b i - a i)] at e1
    rw [← e1]
  rw [hc0, mul_zero] at key
  have hab : 0 ≤ ∑ i, a i * (b i - a i) := by
    rw [sum_eq_range (fun i => a i * (b i - a i))]
    convert key using 2 with m
    simp only [ha', hc']; split_ifs <;> simp
  have h1 : ∑ i, a i ^ 2 ≤ ∑ i, a i * b i := by
    have : ∑ i, a i * (b i - a i) = ∑ i, a i * b i - ∑ i, a i ^ 2 := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    linarith
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have x0 := Real.sqrt_nonneg (∑ i, a i ^ 2)
  have y0 := Real.sqrt_nonneg (∑ i, b i ^ 2)
  have hx := Real.sq_sqrt hA
  have hy := Real.sq_sqrt hB
  nlinarith [sq_nonneg (Real.sqrt (∑ i, a i ^ 2) - Real.sqrt (∑ i, b i ^ 2)),
    mul_nonneg x0 y0]

end PI.ET
