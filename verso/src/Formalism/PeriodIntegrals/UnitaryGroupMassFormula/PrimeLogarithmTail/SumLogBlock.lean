import Mathlib

namespace PI.TailWork

open Finset

/- English proof (translation)
Establish `hdvd : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ∣ Nat.centralBinom n`. Apply `Finset.prod_primes_dvd` to reduce the goal to its premises. Introduce `p hp`. Conclude with `(Finset.mem_filter.1 hp).2.prime`. Introduce `p hp`.

Take `⟨hI, hpr⟩` from `Finset.mem_filter.1 hp`. Take `⟨h1, h2⟩` from `Finset.mem_Ioc.1 hI`. Rewrite using `[Nat.centralBinom_eq_two_mul_choose, two_mul]`. Conclude with `hpr.dvd_choose_add h1 h1 (by omega)`. Establish `hle : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ≤ 4 ^ n` using `(Nat.le_of_dvd (Nat.centralBinom_pos n) hdvd).trans (Nat.centralBinom_le_four_pow n)`.

Establish `hpos : ∀ p ∈ (Ioc n (2 * n)).filter Nat.Prime, ((p : ℕ) : ℝ) ≠ 0`. Introduce `p hp`. Conclude with `(Finset.mem_filter.1 hp).2.ne_zero` after adjusting the coercions. Rewrite using `[← Real.log_prod hpos, ← Real.log_pow]`. Apply `Real.log_le_log` to reduce the goal to its premises.

Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `p hp`. Conclude with `(Finset.mem_filter.1 hp).2.pos` after adjusting the coercions. Establish `: ((∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p : ℕ) : ℝ) ≤ ((4 ^ n : ℕ) : ℝ)`. Conclude with `hle` after adjusting the coercions.

Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem sum_log_block (n : ℕ) :
    ∑ p ∈ (Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ) ≤ (n : ℝ) * Real.log 4 := by
  classical
  have hdvd : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ∣ Nat.centralBinom n := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Finset.mem_filter.1 hp).2.prime
    · intro p hp
      obtain ⟨hI, hpr⟩ := Finset.mem_filter.1 hp
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hI
      rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
      exact hpr.dvd_choose_add h1 h1 (by omega)
  have hle : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ≤ 4 ^ n :=
    (Nat.le_of_dvd (Nat.centralBinom_pos n) hdvd).trans (Nat.centralBinom_le_four_pow n)
  have hpos : ∀ p ∈ (Ioc n (2 * n)).filter Nat.Prime, ((p : ℕ) : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
  rw [← Real.log_prod hpos, ← Real.log_pow]
  apply Real.log_le_log
  · apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.pos
  · have : ((∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p : ℕ) : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hle
    push_cast at this
    exact this

noncomputable def g (n : ℕ) : ℝ := 1 / ((n : ℝ) * ((n : ℝ) - 1))

noncomputable def h (n : ℕ) : ℝ := 1 / ((n : ℝ) - 1) + 1 / (n : ℝ)

/- English proof (translation)
Proceed by induction on `b, hab using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ b hab ih`. Rewrite using `[Finset.sum_Ico_succ_top hab, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_Ico_tele (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

/- English proof (translation)
Unfold `g`. Establish `h1 : (2 : ℝ) ≤ n` using `by exact_mod_cast hn`. Use `push_cast`. Rewrite using `[sub_nonneg]`. Apply `one_div_le_one_div_of_le` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem w_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ g n - g (n + 1) := by
  unfold g
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le
  · nlinarith
  · nlinarith

/- English proof (translation)
Unfold `g h`. Establish `h1 : (2 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `h2 : (n : ℝ) - 1 ≠ 0` using `by linarith`. Establish `h3 : (n : ℝ) ≠ 0` using `by linarith`. Establish `h4 : (n : ℝ) + 1 ≠ 0` using `by linarith`.

Use `push_cast`. Simplify using `only [add_sub_cancel_right]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem w_mul (n : ℕ) (hn : 2 ≤ n) : (g n - g (n + 1)) * (n : ℝ) = h n - h (n + 1) := by
  unfold g h
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (n : ℝ) ≠ 0 := by linarith
  have h4 : (n : ℝ) + 1 ≠ 0 := by linarith
  push_cast
  simp only [add_sub_cancel_right]
  field_simp
  ring

/- English proof (translation)
Use `set N := k + 1 + Q.sup id + 1 with hN`. Establish `hw : ∀ p ∈ Q, g ((p + 1) / 2) - g p = ∑ m ∈ Ico ((p + 1) / 2) p, (g m - g (m + 1))`. Introduce `p hp`. Use `(hQ p hp).2` as an intermediate fact. Rewrite using `[sum_Ico_tele g _ _ (by omega)]`.

Establish `hL : ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) = ∑ m ∈ Ico (k + 1) N, (g m - g (m + 1)) * ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)`. Rewrite using `[Finset.sum_congr rfl (fun p hp => by rw [hw p hp, Finset.mul_sum])]`. Rewrite using `[Finset.sum_comm' (t' := Ico (k + 1) N) (s' := fun m => Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p))]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl (fun p _ => mul_comm _ _)`. Introduce `p m`. Simplify using `only [Finset.mem_filter, Finset.mem_Ico]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hp, h1, h2⟩`.

Use `(hQ p hp).2` as an intermediate fact. Establish `hs : p ≤ Q.sup id` using `Finset.le_sup (f := id) hp`. Conclude with `⟨⟨hp, h1, h2⟩, by omega, by omega⟩`. Introduce and unpack `⟨⟨hp, h1, h2⟩, _, _⟩`. Conclude with `⟨hp, h1, h2⟩`.

Rewrite using `[hL]`. Establish `hb : ∀ m ∈ Ico (k + 1) N, (g m - g (m + 1)) * ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ) ≤ Real.log 4 * (h m - h (m + 1))`. Introduce `m hm`. Establish `hm2 : 2 ≤ m` using `by simp only [Finset.mem_Ico] at hm; omega`. Establish `hin : ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ) ≤ (m : ℝ) * Real.log 4`.

Use `le_trans ?_ (sum_log_block m)` and prove the remaining obligations. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢`. Conclude with `⟨⟨hp.2.2, by omega⟩, (hQ p hp.1).1⟩`.

Introduce `p _ _`. Conclude with `Real.log_natCast_nonneg p`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_le_sum hb).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, sum_Ico_tele h _ _ (by omega)]`.

Establish `hk1 : h (k + 1) = 1 / (k : ℝ) + 1 / ((k : ℝ) + 1)`. Unfold `h`. Use `push_cast`. Rewrite using `[add_sub_cancel_right]`. Establish `hN2 : (2 : ℝ) ≤ N` using `by exact_mod_cast (show 2 ≤ N by omega)`.

Establish `hN0 : 0 ≤ h N`. Unfold `h`. Conclude with `add_nonneg (one_div_nonneg.2 (by linarith)) (one_div_nonneg.2 (by linarith))`. Establish `hl : 0 ≤ Real.log 4` using `Real.log_nonneg (by norm_num)`. Rewrite using `[hk1]`.

Conclude with `mul_le_mul_of_nonneg_left (by linarith) hl`.
-/
theorem weighted (k : ℕ) (hk : 1 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)
      ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) := by
  classical
  set N := k + 1 + Q.sup id + 1 with hN
  have hw : ∀ p ∈ Q, g ((p + 1) / 2) - g p = ∑ m ∈ Ico ((p + 1) / 2) p, (g m - g (m + 1)) := by
    intro p hp
    have := (hQ p hp).2
    rw [sum_Ico_tele g _ _ (by omega)]
  have hL : ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)
      = ∑ m ∈ Ico (k + 1) N, (g m - g (m + 1)) *
          ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ) := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [hw p hp, Finset.mul_sum])]
    rw [Finset.sum_comm' (t' := Ico (k + 1) N)
      (s' := fun m => Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p))]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)
    · intro p m
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨hp, h1, h2⟩
        have := (hQ p hp).2
        have hs : p ≤ Q.sup id := Finset.le_sup (f := id) hp
        exact ⟨⟨hp, h1, h2⟩, by omega, by omega⟩
      · rintro ⟨⟨hp, h1, h2⟩, _, _⟩
        exact ⟨hp, h1, h2⟩
  rw [hL]
  have hb : ∀ m ∈ Ico (k + 1) N, (g m - g (m + 1)) *
      ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)
        ≤ Real.log 4 * (h m - h (m + 1)) := by
    intro m hm
    have hm2 : 2 ≤ m := by simp only [Finset.mem_Ico] at hm; omega
    have hin : ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)
        ≤ (m : ℝ) * Real.log 4 := by
      refine le_trans ?_ (sum_log_block m)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
        exact ⟨⟨hp.2.2, by omega⟩, (hQ p hp.1).1⟩
      · intro p _ _
        exact Real.log_natCast_nonneg p
    calc _ ≤ (g m - g (m + 1)) * ((m : ℝ) * Real.log 4) :=
          mul_le_mul_of_nonneg_left hin (w_nonneg m hm2)
      _ = Real.log 4 * ((g m - g (m + 1)) * m) := by ring
      _ = _ := by rw [w_mul m hm2]
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum, sum_Ico_tele h _ _ (by omega)]
  have hk1 : h (k + 1) = 1 / (k : ℝ) + 1 / ((k : ℝ) + 1) := by
    unfold h
    push_cast
    rw [add_sub_cancel_right]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hN0 : 0 ≤ h N := by
    unfold h
    exact add_nonneg (one_div_nonneg.2 (by linarith)) (one_div_nonneg.2 (by linarith))
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [hk1]
  exact mul_le_mul_of_nonneg_left (by linarith) hl

/- English proof (translation)
Establish `h2` using `Real.log_two_lt_d9`. Establish `h4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Evaluate the numerical expressions. Rewrite using `[h4]`.

Evaluate the numerical expressions using `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_four_lt : Real.log 4 < 1.3863 := by
  have h2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  norm_num at h2 ⊢
  linarith

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, p = 2 * j + 1` from `⟨p / 2, by omega⟩`. Establish `hq : (2 * j + 1 + 1) / 2 = j + 1` using `by omega`. Rewrite using `[hq]`. Establish `hjk : k ≤ j` using `by omega`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`.

Establish `hj' : (k : ℝ) ≤ j` using `by exact_mod_cast hjk`. Establish `hj1 : (1 : ℝ) ≤ j` using `le_trans hk' hj'`. Unfold `g`. Use `push_cast`. Simplify using `only [add_sub_cancel_right]`.

Establish `hmid : 3 - 1 / (2 * (k : ℝ) + 1) ≤ 3 - 1 / (2 * (j : ℝ) + 1)`. Establish `: 1 / (2 * (j : ℝ) + 1) ≤ 1 / (2 * (k : ℝ) + 1)` using `one_div_le_one_div_of_le (by positivity) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : 1 / (((j : ℝ) + 1) * j) - 1 / ((2 * (j : ℝ) + 1) * (2 * j)) - (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2 = (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1)))`. Establish `: (j : ℝ) ≠ 0` using `by linarith`.

Establish `: (j : ℝ) + 1 ≠ 0` using `by linarith`. Establish `: 2 * (j : ℝ) + 1 ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 ≤ (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1)))` using `by positivity`.

Establish `hstep : (3 - 1 / (2 * (k : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2 ≤ (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2` using `div_le_div_of_nonneg_right hmid (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weight_ge (k p : ℕ) (hk : 1 ≤ k) (hp : 2 * k + 1 ≤ p) (hodd : p % 2 = 1) :
    (3 - 1 / (2 * (k : ℝ) + 1)) / (p : ℝ) ^ 2 ≤ g ((p + 1) / 2) - g p := by
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 := ⟨p / 2, by omega⟩
  have hq : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  rw [hq]
  have hjk : k ≤ j := by omega
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (k : ℝ) ≤ j := by exact_mod_cast hjk
  have hj1 : (1 : ℝ) ≤ j := le_trans hk' hj'
  unfold g
  push_cast
  simp only [add_sub_cancel_right]
  have hmid : 3 - 1 / (2 * (k : ℝ) + 1) ≤ 3 - 1 / (2 * (j : ℝ) + 1) := by
    have : 1 / (2 * (j : ℝ) + 1) ≤ 1 / (2 * (k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have key : 1 / (((j : ℝ) + 1) * j) - 1 / ((2 * (j : ℝ) + 1) * (2 * j))
      - (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2
      = (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1))) := by
    have : (j : ℝ) ≠ 0 := by linarith
    have : (j : ℝ) + 1 ≠ 0 := by linarith
    have : 2 * (j : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 ≤ (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1))) := by positivity
  have hstep : (3 - 1 / (2 * (k : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2
      ≤ (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2 :=
    div_le_div_of_nonneg_right hmid (by positivity)
  linarith

/- English proof (translation)
Establish `hk1 : 1 ≤ k` using `by omega`. Establish `hW` using `weighted k hk1 Q hQ`. Establish `hkR : (3 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hcpos : 0 < 3 - 1 / (2 * (k : ℝ) + 1)`. Establish `: 1 / (2 * (k : ℝ) + 1) ≤ 1`.

Rewrite using `[div_le_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1))`. Introduce `p hp`.

Take `⟨hpr, hpk⟩` from `hQ p hp`. Establish `hodd : p % 2 = 1`. Break down `hpr.eq_two_or_odd with h2 | h2` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `h2`.

Establish `hwg` using `weight_ge k p hk1 hpk hodd`. Establish `hlog : 0 ≤ Real.log (p : ℝ)` using `Real.log_natCast_nonneg p`. Rewrite using `[le_div_iff₀ hcpos]`. Combine the equalities or inequalities in the displayed calculation. Establish `hl` using `log_four_lt`.

Establish `hl0 : 0 ≤ Real.log 4` using `Real.log_nonneg (by norm_num)`. Establish `e : Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1)) = Real.log 4 * (2 * (k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2))`. Establish `: (k : ℝ) ≠ 0` using `by linarith`. Establish `: (k : ℝ) + 1 ≠ 0` using `by linarith`. Establish `: 2 * (k : ℝ) + 1 ≠ 0` using `by linarith`.

Establish `: 6 * (k : ℝ) + 2 ≠ 0` using `by linarith`. Establish `hc : 3 - 1 / (2 * (k : ℝ) + 1) = (6 * (k : ℝ) + 2) / (2 * (k : ℝ) + 1)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `A : Real.log 4 * (2 * (k : ℝ) + 1) ^ 3 ≤ 1.3863 * (2 * (k : ℝ) + 1) ^ 3` using `mul_le_mul_of_nonneg_right hl.le (by positivity)`. Establish `hk3 : 0 ≤ (k : ℝ) - 3` using `by linarith`. Establish `B : 1.3863 * (2 * (k : ℝ) + 1) ^ 3 ≤ 2.04 * ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2))`.

Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hk3 hk3) hk3, mul_nonneg hk3 hk3, hk3]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_div]`. Use `_ ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1)) := div_le_div_of_nonneg_right hW hcpos.le`. Use `_ ≤ 2.04 / (2 * (k : ℝ) + 1) := by`.

Rewrite using `[e, div_le_div_iff₀ (by positivity) (by positivity)]`. Use polynomial arithmetic with `[A, B]`.
-/
theorem tail_odd (k : ℕ) (hk : 3 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := by
  have hk1 : 1 ≤ k := by omega
  have hW := weighted k hk1 Q hQ
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcpos : 0 < 3 - 1 / (2 * (k : ℝ) + 1) := by
    have : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hterm : ∀ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1)) := by
    intro p hp
    obtain ⟨hpr, hpk⟩ := hQ p hp
    have hodd : p % 2 = 1 := by
      rcases hpr.eq_two_or_odd with h2 | h2
      · omega
      · exact h2
    have hwg := weight_ge k p hk1 hpk hodd
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    rw [le_div_iff₀ hcpos]
    calc Real.log (p : ℝ) / (p : ℝ) ^ 2 * (3 - 1 / (2 * (k : ℝ) + 1))
        = Real.log (p : ℝ) * ((3 - 1 / (2 * (k : ℝ) + 1)) / (p : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwg hlog
  have hl := log_four_lt
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have e : Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1))
      = Real.log 4 * (2 * (k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2)) := by
    have : (k : ℝ) ≠ 0 := by linarith
    have : (k : ℝ) + 1 ≠ 0 := by linarith
    have : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
    have : 6 * (k : ℝ) + 2 ≠ 0 := by linarith
    have hc : 3 - 1 / (2 * (k : ℝ) + 1) = (6 * (k : ℝ) + 2) / (2 * (k : ℝ) + 1) := by
      field_simp
      ring
    rw [hc]
    field_simp
    ring
  have A : Real.log 4 * (2 * (k : ℝ) + 1) ^ 3 ≤ 1.3863 * (2 * (k : ℝ) + 1) ^ 3 :=
    mul_le_mul_of_nonneg_right hl.le (by positivity)
  have hk3 : 0 ≤ (k : ℝ) - 3 := by linarith
  have B : 1.3863 * (2 * (k : ℝ) + 1) ^ 3 ≤ 2.04 * ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2)) := by
    nlinarith [mul_nonneg (mul_nonneg hk3 hk3) hk3, mul_nonneg hk3 hk3, hk3]
  calc ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1)) :=
        Finset.sum_le_sum hterm
    _ = (∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)) / (3 - 1 / (2 * (k : ℝ) + 1)) := by
        rw [Finset.sum_div]
    _ ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hW hcpos.le
    _ ≤ 2.04 / (2 * (k : ℝ) + 1) := by
        rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [A, B]

end PI.TailWork
