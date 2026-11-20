import Mathlib

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Use polynomial arithmetic with `[ih, Nat.zero_le (m a * ∑ i ∈ s, m i)]`.
-/
theorem sq_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) : ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith [ih, Nat.zero_le (m a * ∑ i ∈ s, m i)]

/- English proof (translation)
Take `⟨a, ha⟩` from `Finset.card_pos.mp (show 0 < s.card by omega)`. Establish `hne : (s.erase a).Nonempty`. Rewrite using `[← Finset.card_pos, Finset.card_erase_of_mem ha]`. Use linear arithmetic over natural numbers and integers. Take `⟨b, hb⟩` from `hne`.

Establish `hM : 1 ≤ ∑ i ∈ s.erase a, m i` using `(hm b (Finset.mem_of_mem_erase hb)).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)`. Establish `ih` using `sq_sum_le (s.erase a) m`. Rewrite using `[← Finset.add_sum_erase s _ ha, ← Finset.add_sum_erase s _ ha]`. Use `hm a ha` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sq_sum_lt {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) (h : 1 < s.card) :
    ∑ i ∈ s, m i ^ 2 < (∑ i ∈ s, m i) ^ 2 := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have hne : (s.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := hne
  have hM : 1 ≤ ∑ i ∈ s.erase a, m i :=
    (hm b (Finset.mem_of_mem_erase hb)).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)
  have ih := sq_sum_le (s.erase a) m
  rw [← Finset.add_sum_erase s _ ha, ← Finset.add_sum_erase s _ ha]
  have := hm a ha
  nlinarith

/- English proof (translation)
Establish `hMn : ∑ i ∈ s, m i ≤ n`. Establish `: (∑ i ∈ s, m i) * dF ≤ n * dF`. Rewrite using `[hsum, Finset.sum_mul]`. Conclude with `Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (hd i hi)`. Conclude with `Nat.le_of_mul_le_mul_right this hdF`.

Establish `h1` using `sq_sum_le s m`. Establish `h2 : (∑ i ∈ s, m i) ^ 2 ≤ n ^ 2` using `Nat.pow_le_pow_left hMn 2`. Use `⟨h1.trans h2, fun heq hne i hi => ?_⟩` and prove the remaining obligations. Establish `hcard : s.card = 1`. Assume the negation of the conclusion as `hc`.

Use `sq_sum_lt s m hm (by have := hne.card_pos; omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨a, rfl⟩` from `Finset.card_eq_one.mp hcard`. Rewrite `hi` using `[Finset.mem_singleton]`. Substitute `hi` using the available equality.

Use `⟨rfl, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_singleton] at heq hsum`. Establish `hn : m i = n`. Use `(Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) heq` as an intermediate fact. Conclude with `this`.

Rewrite `hsum` using `[← hn]`. Use `hm i (Finset.mem_singleton_self i)` as an intermediate fact. Establish `: dF = dE i` using `Nat.eq_of_mul_eq_mul_left (by omega) hsum`. Use linear arithmetic over natural numbers and integers.
-/
theorem num_fib {ι : Type*} [DecidableEq ι] (s : Finset ι) (m dE : ι → ℕ) (n dF : ℕ) (hdF : 0 < dF)
    (hm : ∀ i ∈ s, 1 ≤ m i) (hd : ∀ i ∈ s, dF ≤ dE i) (hsum : n * dF = ∑ i ∈ s, m i * dE i) :
    ∑ i ∈ s, m i ^ 2 ≤ n ^ 2 ∧ (∑ i ∈ s, m i ^ 2 = n ^ 2 → s.Nonempty → ∀ i ∈ s, s = {i} ∧ dE i ≤ dF) := by
  have hMn : ∑ i ∈ s, m i ≤ n := by
    have : (∑ i ∈ s, m i) * dF ≤ n * dF := by
      rw [hsum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (hd i hi)
    exact Nat.le_of_mul_le_mul_right this hdF
  have h1 := sq_sum_le s m
  have h2 : (∑ i ∈ s, m i) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hMn 2
  refine ⟨h1.trans h2, fun heq hne i hi => ?_⟩
  have hcard : s.card = 1 := by
    by_contra hc
    have := sq_sum_lt s m hm (by have := hne.card_pos; omega)
    omega
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.mem_singleton] at hi; subst hi
  refine ⟨rfl, ?_⟩
  simp only [Finset.sum_singleton] at heq hsum
  have hn : m i = n := by
    have := (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) heq
    exact this
  rw [← hn] at hsum
  have := hm i (Finset.mem_singleton_self i)
  have : dF = dE i := Nat.eq_of_mul_eq_mul_left (by omega) hsum
  omega

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
