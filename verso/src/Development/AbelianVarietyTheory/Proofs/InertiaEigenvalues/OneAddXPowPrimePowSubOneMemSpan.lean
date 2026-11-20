import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hl⟩`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `Nat.exists_eq_succ_of_ne_zero hk0`. Take `⟨m, hm⟩ : ∃ m, l ^ b = m + 1` from `Nat.exists_eq_succ_of_ne_zero (pow_pos hl.pos b).ne'`. Establish `hkb : j + 1 ≤ l ^ b` using `le_trans hk.le (Nat.pow_le_pow_right hl.pos (Nat.sub_le b 1))`. Establish `hC : (l ^ b).choose (j + 1) ≠ 0` using `(Nat.choose_pos hkb).ne'`.

Establish `hid : l ^ b * m.choose j = (l ^ b).choose (j + 1) * (j + 1)`. Rewrite using `[hm]`. Conclude with `Nat.add_one_mul_choose_eq m j`. Establish `hv : padicValNat l (j + 1) < b - 1`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `h1 : l ^ padicValNat l (j + 1) ≤ j + 1` using `Nat.le_of_dvd (Nat.succ_pos j) pow_padicValNat_dvd`. Establish `h2 : l ^ (b - 1) ≤ l ^ padicValNat l (j + 1)` using `Nat.pow_le_pow_right hl.pos hcon`. Use linear arithmetic over natural numbers and integers. Establish `hdiv : l ^ b ∣ (l ^ b).choose (j + 1) * (j + 1)`.

Rewrite using `[← hid]`. Conclude with `dvd_mul_right _ _`. Establish `hne : (l ^ b).choose (j + 1) * (j + 1) ≠ 0` using `mul_ne_zero hC (Nat.succ_ne_zero j)`. Rewrite `hdiv` using `[padicValNat_dvd_iff_le hne, padicValNat.mul hC (by omega : j + 1 ≠ 0)]`. Conclude with `(padicValNat_dvd_iff_le hC).mpr (by omega)`.
-/
theorem sq_dvd_choose_prime_pow (l : ℕ) (hl : l.Prime) (b k : ℕ) (hb : 1 ≤ b) (hk0 : k ≠ 0)
    (hk : k < l ^ (b - 1)) : l ^ 2 ∣ (l ^ b).choose k := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨m, hm⟩ : ∃ m, l ^ b = m + 1 := Nat.exists_eq_succ_of_ne_zero (pow_pos hl.pos b).ne'
  have hkb : j + 1 ≤ l ^ b := le_trans hk.le (Nat.pow_le_pow_right hl.pos (Nat.sub_le b 1))
  have hC : (l ^ b).choose (j + 1) ≠ 0 := (Nat.choose_pos hkb).ne'

  have hid : l ^ b * m.choose j = (l ^ b).choose (j + 1) * (j + 1) := by
    rw [hm]; exact Nat.add_one_mul_choose_eq m j

  have hv : padicValNat l (j + 1) < b - 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : l ^ padicValNat l (j + 1) ≤ j + 1 :=
      Nat.le_of_dvd (Nat.succ_pos j) pow_padicValNat_dvd
    have h2 : l ^ (b - 1) ≤ l ^ padicValNat l (j + 1) := Nat.pow_le_pow_right hl.pos hcon
    omega
  have hdiv : l ^ b ∣ (l ^ b).choose (j + 1) * (j + 1) := by
    rw [← hid]; exact dvd_mul_right _ _
  have hne : (l ^ b).choose (j + 1) * (j + 1) ≠ 0 := mul_ne_zero hC (Nat.succ_ne_zero j)
  rw [padicValNat_dvd_iff_le hne, padicValNat.mul hC (by omega : j + 1 ≠ 0)] at hdiv
  exact (padicValNat_dvd_iff_le hC).mpr (by omega)

/- English proof (translation)
Establish `key : ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) = ∑ i ∈ Finset.range (l ^ b), Polynomial.X ^ (i + 1) * (((l ^ b).choose (i + 1) : ℕ) : Polynomial ℤ)`. Rewrite using `[add_comm, add_pow, Finset.sum_range_succ']`. Simplify using the standard rewrite rules. Rewrite using `[key]`. Use `Ideal.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hi : i + 1 < l ^ (b - 1)`. Take `⟨c, hc⟩` from `sq_dvd_choose_prime_pow l (Fact.out) b (i + 1) hb (Nat.succ_ne_zero i) hi`. Rewrite using `[hc, Nat.cast_mul, Nat.cast_pow, mul_left_comm]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))`. Use `push_neg at hi`.

Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hi`. Rewrite using `[hd, pow_add, mul_assoc]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))`.
-/
theorem one_add_X_pow_prime_pow_sub_one_mem_span (l : ℕ) [Fact l.Prime] (b : ℕ) (hb : 1 ≤ b) :
    ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) ∈
      Ideal.span {((l : Polynomial ℤ)) ^ 2, Polynomial.X ^ (l ^ (b - 1))} := by

  have key : ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) =
      ∑ i ∈ Finset.range (l ^ b),
        Polynomial.X ^ (i + 1) * (((l ^ b).choose (i + 1) : ℕ) : Polynomial ℤ) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  by_cases hi : i + 1 < l ^ (b - 1)
  ·
    obtain ⟨c, hc⟩ := sq_dvd_choose_prime_pow l (Fact.out) b (i + 1) hb (Nat.succ_ne_zero i) hi
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_left_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  ·
    push_neg at hi
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    rw [hd, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end GlobalTheory
