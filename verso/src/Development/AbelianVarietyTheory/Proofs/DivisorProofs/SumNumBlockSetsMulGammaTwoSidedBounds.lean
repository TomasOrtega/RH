import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

/- English proof (translation)
Unfold `splitDoublingNBlock`. Rewrite using `[Finset.card_eq_one]`. Use `⟨∅, ?_⟩` and prove the remaining obligations. Use extensionality with `J`. Simplify using `only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Rewrite using `[Finset.eq_empty_iff_forall_notMem]`. Introduce `x hx`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 (h1 hx)`.

Establish `: i ∈ Finset.univ.filter fun i => b i ∈ J` using `by simp [hx]`. Rewrite `this` using `[h2]`. Simplify using `at this`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules.
-/
theorem numBlockSetsOfTotalSize_zero {r : ℕ} (b : Fin r → ℕ) : splitDoublingNBlock b 0 = 1 := by
  unfold splitDoublingNBlock
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext J
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (h1 hx)
    have : i ∈ Finset.univ.filter fun i => b i ∈ J := by simp [hx]
    rw [h2] at this
    simp at this
  · rintro rfl
    simp

/- English proof (translation)
Unfold `splitDoublingNBlock`. Establish `h : r.choose j = (Finset.powersetCard j (Finset.univ : Finset (Fin r))).card` using `by simp`. Rewrite using `[h]`. Use `Finset.card_le_card_of_injOn (fun J => Finset.univ.filter fun i => b i ∈ J) ?_ ?_` and prove the remaining obligations. Introduce `J hJ`.

Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq] at hJ`. Simplify using `only [Finset.mem_coe, Finset.mem_powersetCard]`. Conclude with `⟨Finset.subset_univ _, hJ.2⟩`. Introduce `J hJ K hK hJK`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hJ hK`.

Establish `key : ∀ i, b i ∈ J ↔ b i ∈ K` using `fun i => by`. Use `Finset.ext_iff.1 hJK i` as an intermediate fact. Simplify using `using this`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 (hJ.1 hx)`. Conclude with `(key i).1 hx`. Introduce `hx`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 (hK.1 hx)`.

Conclude with `(key i).2 hx`.
-/
theorem numBlockSetsOfTotalSize_le_choose {r : ℕ} (b : Fin r → ℕ) (j : ℕ) : splitDoublingNBlock b j ≤ r.choose j := by
  unfold splitDoublingNBlock
  have h : r.choose j = (Finset.powersetCard j (Finset.univ : Finset (Fin r))).card := by simp
  rw [h]
  refine Finset.card_le_card_of_injOn (fun J => Finset.univ.filter fun i => b i ∈ J) ?_ ?_
  · intro J hJ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hJ
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hJ.2⟩
  · intro J hJ K hK hJK
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hJ hK
    have key : ∀ i, b i ∈ J ↔ b i ∈ K := fun i => by
      have := Finset.ext_iff.1 hJK i
      simpa using this
    ext x
    constructor
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hJ.1 hx)
      exact (key i).1 hx
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hK.1 hx)
      exact (key i).2 hx

/- English proof (translation)
Unfold `gam`. Use `split_ifs with h`. Simplify using `[h]`. Conclude with `Nat.sub_le _ _`.
-/
theorem gam_le_pow (q l : ℕ) : gam q l ≤ q ^ l := by
  unfold gam
  split_ifs with h
  · simp [h]
  · exact Nat.sub_le _ _

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Establish `hq0 : (q : ℝ) ≠ 0` using `by positivity`. Unfold `gam`. Rewrite using `[if_neg (by omega), Nat.add_sub_cancel, Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gam_cast {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) :
    (gam q k : ℝ) = (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold gam
  rw [if_neg (by omega), Nat.add_sub_cancel, Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  field_simp
  ring

/- English proof (translation)
Establish `h0 : 0 ≤ (r : ℝ) * x` using `by positivity`. Establish `h1 : (1 + x) ^ r ≤ Real.exp x ^ r` using `pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) r`. Rewrite `h1` using `[← Real.exp_nat_mul]`. Establish `h2` using `Real.abs_exp_sub_one_le (x := r * x) (by rwa [abs_of_nonneg h0])`. Rewrite `h2` using `[abs_of_nonneg h0]`.

Combine the linear relations using `[(abs_le.1 h2).2]`.
-/
theorem one_add_pow_le_two_mul {x : ℝ} (hx : 0 ≤ x) {r : ℕ} (h : (r : ℝ) * x ≤ 1) :
    (1 + x) ^ r ≤ 1 + 2 * (r * x) := by
  have h0 : 0 ≤ (r : ℝ) * x := by positivity
  have h1 : (1 + x) ^ r ≤ Real.exp x ^ r :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) r
  rw [← Real.exp_nat_mul] at h1
  have h2 := Real.abs_exp_sub_one_le (x := r * x) (by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg h0] at h2
  linarith [(abs_le.1 h2).2]

/- English proof (translation)
Establish `h1 : ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j ≤ ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j` using `Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) (fun _ _ _ => by positivity)`. Establish `h2 : ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * x ^ j = ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j`. Use `Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_` and prove the remaining obligations. Introduce `j _ hj`. Rewrite using `[Nat.choose_eq_zero_of_lt (by simpa using hj)]`.

Simplify using the standard rewrite rules. Rewrite using `[add_comm 1 x, add_pow]`. Use `h1.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← h2]`. Conclude with `Finset.sum_congr rfl fun j _ => by simp [mul_comm]`.
-/
theorem sum_choose_mul_pow_le {x : ℝ} (hx : 0 ≤ x) (r k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j ≤ (1 + x) ^ r := by
  have h1 : ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j
      ≤ ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun _ _ _ => by positivity)
  have h2 : ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * x ^ j
      = ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (by simpa using hj)]
    simp
  rw [add_comm 1 x, add_pow]
  refine h1.trans (le_of_eq ?_)
  rw [← h2]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

/- English proof (translation)
Introduce `r k q b hk hr hrq hq`. Establish `hq0 : (0 : ℝ) < q` using `by positivity`. Establish `hg` using `gam_cast (q := q) (k := k) (by omega) hk`. Rewrite using `[Finset.sum_range_succ', numBlockSetsOfTotalSize_zero, one_mul, Nat.sub_zero]`. Use `push_cast`.

Rewrite using `[hg]`. Prove the components needed by the constructor for the conclusion. Establish `: 0 ≤ ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ)` using `Finset.sum_nonneg fun _ _ => by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx : (0 : ℝ) ≤ 1 / q` using `by positivity`.

Establish `h1` using `sum_choose_mul_pow_le hx r k`. Establish `h2` using `one_add_pow_le_two_mul hx (r := r) (by`. Rewrite using `[mul_one_div, div_le_one hq0]`. Conclude with `hrq)` after adjusting the coercions. Rewrite `h1` using `[Finset.sum_range_succ']`.

Simplify using `only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h1`. Establish `h3 : ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ) ≤ (q : ℝ) ^ k * ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j + 1 ≤ k` using `by simpa using hj`.

Establish `e : (q : ℝ) ^ k * ((r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1)) = (r.choose (j + 1) : ℝ) * (q : ℝ) ^ (k - (j + 1))` using `by conv_lhs => rw [← Nat.sub_add_cancel hj', pow_add]`. Rewrite using `[one_div_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `Nat.mul_le_mul (numBlockSetsOfTotalSize_le_choose b _) (gam_le_pow _ _)` after adjusting the coercions.

Establish `h4 : ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1) ≤ 2 * (r * (1 / (q : ℝ)))` using `by linarith`. Establish `h5` using `mul_le_mul_of_nonneg_left h4 (pow_nonneg hq0.le k)`. Establish `e : (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ)) = (q : ℝ) ^ k * (2 * (r * (1 / (q : ℝ)))) + (q : ℝ) ^ k * (1 - 1 / (q : ℝ))` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_numBlockSets_mul_gamma_two_sided_bounds : ∀ (r k q : ℕ) (b : Fin r → ℕ), 1 ≤ k → 1 ≤ r → r ≤ q → 2 ≤ q → (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) ≤ ((∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam q (k - j) : ℕ) : ℝ) ∧ ((∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam q (k - j) : ℕ) : ℝ) ≤ (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ)) := by
  intro r k q b hk hr hrq hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hg := gam_cast (q := q) (k := k) (by omega) hk
  rw [Finset.sum_range_succ', numBlockSetsOfTotalSize_zero, one_mul, Nat.sub_zero]
  push_cast
  rw [hg]
  constructor
  · have : 0 ≤ ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith
  · have hx : (0 : ℝ) ≤ 1 / q := by positivity
    have h1 := sum_choose_mul_pow_le hx r k
    have h2 := one_add_pow_le_two_mul hx (r := r) (by
      rw [mul_one_div, div_le_one hq0]; exact_mod_cast hrq)
    rw [Finset.sum_range_succ'] at h1
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h1
    have h3 : ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ)
        ≤ (q : ℝ) ^ k * ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j + 1 ≤ k := by simpa using hj
      have e : (q : ℝ) ^ k * ((r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1))
          = (r.choose (j + 1) : ℝ) * (q : ℝ) ^ (k - (j + 1)) := by
        conv_lhs => rw [← Nat.sub_add_cancel hj', pow_add]
        rw [one_div_pow]
        field_simp
      rw [e]
      exact_mod_cast Nat.mul_le_mul (numBlockSetsOfTotalSize_le_choose b _) (gam_le_pow _ _)
    have h4 : ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1)
        ≤ 2 * (r * (1 / (q : ℝ))) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (pow_nonneg hq0.le k)
    have e : (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ))
        = (q : ℝ) ^ k * (2 * (r * (1 / (q : ℝ)))) + (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) := by ring
    rw [e]
    linarith

end GlobalTheory.FinGL
