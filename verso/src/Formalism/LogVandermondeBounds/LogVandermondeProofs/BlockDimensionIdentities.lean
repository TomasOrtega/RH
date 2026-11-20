import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

/- English proof (translation)
Establish `h : ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = ∑ j ∈ range n, j`. Rewrite using `[Finset.card_filter, Finset.sum_product_right]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[← Finset.card_filter]`. Establish `e : (range n).filter (fun i => i < j) = range j`.

Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range] at hj ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `[e]`. Rewrite using `[h, mul_comm, Finset.sum_range_id_mul_two]`.
-/
lemma two_mul_card_lt_pairs (n : ℕ) :
    2 * ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = n * (n - 1) := by
  have h : ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = ∑ j ∈ range n, j := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.card_filter]
    have e : (range n).filter (fun i => i < j) = range j := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
    simp [e]
  rw [h, mul_comm, Finset.sum_range_id_mul_two]

/- English proof (translation)
Use `Finset.card_nbij' (fun p => (p.1 - a, p.2 - a)) (fun p => (p.1 + a, p.2 + a)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `p hp`.

Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `p hp`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp`. Apply the tactic sequence `ext <;> simp <;> omega`.

Introduce `p hp`. Apply the tactic sequence `ext <;> simp`.
-/
private lemma card_ordered_pairs_in_shifted_interval (a n N : ℕ) (h : a + n ≤ N) :
    ((range N ×ˢ range N).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ a ≤ p.1 ∧ p.2 < a + n)).card =
      ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
  refine Finset.card_nbij' (fun p => (p.1 - a, p.2 - a)) (fun p => (p.1 + a, p.2 + a)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp
    ext <;> simp <;> omega
  · intro p hp
    ext <;> simp

/- English proof (translation)
Introduce `k m rS r hm hme hrS hr blockOf dimN`. Establish `hm2 : m = 2 * rS + 2` using `by obtain ⟨t, ht⟩ := hme; omega`. Establish `hsame : ∀ i j, i < j → j < r → (blockOf i = blockOf j ↔ rS ≤ i ∧ j < rS + (k + 1))`. Introduce `i j hij hj`. Simplify using `only [blockOf]`.

Apply the tactic sequence `split_ifs <;> omega`. Establish `hA` using `two_mul_card_lt_pairs r`. Establish `hB` using `card_ordered_pairs_in_shifted_interval rS (k + 1) r (by omega)`. Establish `hC` using `two_mul_card_lt_pairs (k + 1)`. Simplify using `only [Nat.add_sub_cancel] at hC`.

Establish `hsplit : (((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).filter (fun p : ℕ × ℕ => blockOf p.1 = blockOf p.2)).card + (((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).filter (fun p : ℕ × ℕ => ¬ blockOf p.1 = blockOf p.2)).card = ((range r ×ˢ range r).filter …` using `by first`. Consider the case `exact Finset.filter_card_add_filter_neg_card_eq_card _`. Consider the case `exact Finset.card_filter_add_card_filter_not _`. Consider the case `exact Finset.card_filter_add_card_filter_neg _`. Consider the case `(rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _), Finset.filter_union_filter_neg_eq])`.

Rewrite `hsplit` using `[Finset.filter_filter, Finset.filter_filter]`. Establish `e1 : (range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ blockOf p.1 = blockOf p.2) = (range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ rS ≤ p.1 ∧ p.2 < rS + (k + 1))`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.mem_product, Finset.mem_range] at hp`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, (hsame _ _ h1 hp.2).1 h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, (hsame _ _ h1 hp.2).2 h2⟩`.

Establish `e2 : dimN = ((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ ¬ blockOf p.1 = blockOf p.2)).card` using `rfl`. Rewrite `hsplit` using `[e1, hB, ← e2]`. Establish `hdim : 2 * dimN + (k + 1) * k = r * (r - 1)` using `by omega`. Establish `hdZ : 2 * (dimN : ℤ) = (r : ℤ) * ((r : ℤ) - 1) - ((k : ℤ) + 1) * k`. Use `congrArg (Nat.cast : ℕ → ℤ) hdim` as an intermediate fact.

Move the coercions through the operations in `[Nat.cast_sub (show 1 ≤ r by omega)] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrZ : (r : ℤ) = k + 1 + 2 * rS` using `by exact_mod_cast hr`. Establish `hmZ : (m : ℤ) = 2 * rS + 2` using `by exact_mod_cast hm2`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hrZ, hmZ]`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `hdZ - hrZ`. Take the linear combination `-hdZ + hrZ`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hrZ, hmZ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem blockDimensionIdentities : BlockDimensionIdentities := by
  intro k m rS r hm hme hrS hr blockOf dimN
  have hm2 : m = 2 * rS + 2 := by obtain ⟨t, ht⟩ := hme; omega
  have hsame : ∀ i j, i < j → j < r → (blockOf i = blockOf j ↔ rS ≤ i ∧ j < rS + (k + 1)) := by
    intro i j hij hj
    simp only [blockOf]
    split_ifs <;> omega
  have hA := two_mul_card_lt_pairs r
  have hB := card_ordered_pairs_in_shifted_interval rS (k + 1) r (by omega)
  have hC := two_mul_card_lt_pairs (k + 1)
  simp only [Nat.add_sub_cancel] at hC
  have hsplit : (((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).filter
      (fun p : ℕ × ℕ => blockOf p.1 = blockOf p.2)).card +
      (((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).filter
      (fun p : ℕ × ℕ => ¬ blockOf p.1 = blockOf p.2)).card =
      ((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    first
      | exact Finset.filter_card_add_filter_neg_card_eq_card _
      | exact Finset.card_filter_add_card_filter_not _
      | exact Finset.card_filter_add_card_filter_neg _
      | (rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
          Finset.filter_union_filter_neg_eq])
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have e1 : (range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ blockOf p.1 = blockOf p.2) =
      (range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ rS ≤ p.1 ∧ p.2 < rS + (k + 1)) := by
    apply Finset.filter_congr
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hsame _ _ h1 hp.2).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hsame _ _ h1 hp.2).2 h2⟩
  have e2 : dimN = ((range r ×ˢ range r).filter
      (fun p : ℕ × ℕ => p.1 < p.2 ∧ ¬ blockOf p.1 = blockOf p.2)).card := rfl
  rw [e1, hB, ← e2] at hsplit
  have hdim : 2 * dimN + (k + 1) * k = r * (r - 1) := by omega
  have hdZ : 2 * (dimN : ℤ) = (r : ℤ) * ((r : ℤ) - 1) - ((k : ℤ) + 1) * k := by
    have := congrArg (Nat.cast : ℕ → ℤ) hdim
    push_cast [Nat.cast_sub (show 1 ≤ r by omega)] at this
    linarith
  have hrZ : (r : ℤ) = k + 1 + 2 * rS := by exact_mod_cast hr
  have hmZ : (m : ℤ) = 2 * rS + 2 := by exact_mod_cast hm2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hrZ, hmZ]; ring
  · linear_combination hdZ - hrZ
  · linear_combination -hdZ + hrZ
  · ring
  · rw [hrZ, hmZ]; ring

/- English proof (translation)
Introduce `k r hkr`. Proceed by induction on `r, hkr using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ r hkr ih`. Rewrite using `[Finset.prod_Ico_succ_top (by omega : k + 1 ≤ r + 1), Finset.prod_range_succ, ← ih]`.

Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prodFactorialShift : ProdFactorialShift := by
  intro k r hkr
  induction r, hkr using Nat.le_induction with
  | base => simp
  | succ r hkr ih =>
    rw [Finset.prod_Ico_succ_top (by omega : k + 1 ≤ r + 1), Finset.prod_range_succ, ← ih]
    simp only [Nat.add_sub_cancel]
    ring

/- English proof (translation)
Simplify using `only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd]`.
-/
lemma castAdd_lt_castAdd_iff' {a m : ℕ} (i j : Fin a) :
    Fin.castAdd m i < Fin.castAdd m j ↔ i < j := by
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd]

/- English proof (translation)
Use `i.2` as an intermediate fact. Simplify using `only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]`. Use linear arithmetic over natural numbers and integers.
-/
lemma castAdd_lt_natAdd' {a m : ℕ} (i : Fin a) (j : Fin m) :
    Fin.castAdd m i < Fin.natAdd a j := by
  have := i.2
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]
  omega

/- English proof (translation)
Use `j.2` as an intermediate fact. Simplify using `only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]`. Use linear arithmetic over natural numbers and integers.
-/
lemma not_natAdd_lt_castAdd' {a m : ℕ} (i : Fin m) (j : Fin a) :
    ¬ Fin.natAdd a i < Fin.castAdd m j := by
  have := j.2
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]
  omega

/- English proof (translation)
Simplify using `only [Fin.lt_iff_val_lt_val, Fin.coe_natAdd]`. Use linear arithmetic over natural numbers and integers.
-/
lemma natAdd_lt_natAdd_iff' {a m : ℕ} (i j : Fin m) :
    Fin.natAdd a i < Fin.natAdd a j ↔ i < j := by
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_natAdd]
  omega

/- English proof (translation)
Introduce `R _ a m v b`. Simplify using `only [Finset.prod_filter]`. Rewrite using `[Fin.prod_univ_add]`. Simplify using `only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, castAdd_lt_castAdd_iff', castAdd_lt_natAdd', not_natAdd_lt_castAdd', natAdd_lt_natAdd_iff', if_true, if_false, Finset.prod_const_one, mul_one, one_mul, sub_neg_eq_add, neg_sub_neg, neg_add_eq_sub, Finset.prod_mul_distrib …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vandermondeAppendNeg : VandermondeAppendNeg := by
  intro R _ a m v b
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_add]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, castAdd_lt_castAdd_iff',
    castAdd_lt_natAdd', not_natAdd_lt_castAdd', natAdd_lt_natAdd_iff', if_true, if_false,
    Finset.prod_const_one, mul_one, one_mul, sub_neg_eq_add, neg_sub_neg, neg_add_eq_sub, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Introduce `q hq n`. Use `set x := q⁻¹ with hx`. Establish `hx0 : 0 < x` using `inv_pos.mpr (by linarith)`. Establish `hxq : x * q = 1` using `inv_mul_cancel₀ (by linarith)`. Establish `hx3 : x ≤ 1 / 3` using `by nlinarith`.

Establish `hx1 : x ≤ 1` using `by linarith`. Establish `key : ∀ n : ℕ, 1 - 2 * x + x ^ (n + 1) ≤ (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ n ih`. Rewrite using `[Finset.prod_range_succ, ← mul_assoc]`. Use `set y := x ^ (n + 1) with hy`. Establish `hy0 : 0 ≤ y` using `pow_nonneg hx0.le _`.

Establish `hyx : y ≤ x` using `pow_le_of_le_one hx0.le hx1 (by omega)`. Establish `hc : 0 ≤ 1 - y` using `by have : y ≤ 1 := pow_le_one₀ hx0.le hx1; linarith`. Establish `h1` using `mul_le_mul_of_nonneg_right ih hc`. Establish `h2 : y * y ≤ y * x` using `mul_le_mul_of_nonneg_left hyx hy0`. Establish `e : x ^ (n + 1 + 1) = y * x` using `by rw [hy, pow_succ]`.

Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hfac : ∀ i ∈ range n, 0 ≤ 1 - x ^ (i + 1) ∧ 1 - x ^ (i + 1) ≤ 1`. Introduce `i _`. Conclude with `⟨by have : x ^ (i + 1) ≤ 1 := pow_le_one₀ hx0.le hx1; linarith, by have : 0 ≤ x ^ (i + 1) := pow_nonneg hx0.le _; linarith⟩`.

Use `⟨?_, Finset.prod_le_one (fun i hi => (hfac i hi).1) (fun i hi => (hfac i hi).2)⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h1 : (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) < (1 - x) * (1 / 2)` using `mul_lt_mul_of_pos_left hlt (by linarith)`. Use `key n` as an intermediate fact.

Use `pow_pos hx0 (n + 1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eulerProductBounds : EulerProductBounds := by
  intro q hq n
  set x := q⁻¹ with hx
  have hx0 : 0 < x := inv_pos.mpr (by linarith)
  have hxq : x * q = 1 := inv_mul_cancel₀ (by linarith)
  have hx3 : x ≤ 1 / 3 := by nlinarith
  have hx1 : x ≤ 1 := by linarith
  have key : ∀ n : ℕ, 1 - 2 * x + x ^ (n + 1) ≤ (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) := by
    intro n
    induction n with
    | zero => simp; linarith
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc]
      set y := x ^ (n + 1) with hy
      have hy0 : 0 ≤ y := pow_nonneg hx0.le _
      have hyx : y ≤ x := pow_le_of_le_one hx0.le hx1 (by omega)
      have hc : 0 ≤ 1 - y := by have : y ≤ 1 := pow_le_one₀ hx0.le hx1; linarith
      have h1 := mul_le_mul_of_nonneg_right ih hc
      have h2 : y * y ≤ y * x := mul_le_mul_of_nonneg_left hyx hy0
      have e : x ^ (n + 1 + 1) = y * x := by rw [hy, pow_succ]
      rw [e]
      nlinarith
  have hfac : ∀ i ∈ range n, 0 ≤ 1 - x ^ (i + 1) ∧ 1 - x ^ (i + 1) ≤ 1 := by
    intro i _
    exact ⟨by have : x ^ (i + 1) ≤ 1 := pow_le_one₀ hx0.le hx1; linarith,
      by have : 0 ≤ x ^ (i + 1) := pow_nonneg hx0.le _; linarith⟩
  refine ⟨?_, Finset.prod_le_one (fun i hi => (hfac i hi).1) (fun i hi => (hfac i hi).2)⟩
  by_contra hlt
  push_neg at hlt
  have h1 : (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) < (1 - x) * (1 / 2) :=
    mul_lt_mul_of_pos_left hlt (by linarith)
  have := key n
  have := pow_pos hx0 (n + 1)
  linarith

end Formalism.LogVandermondeBounds.StandardLattice
