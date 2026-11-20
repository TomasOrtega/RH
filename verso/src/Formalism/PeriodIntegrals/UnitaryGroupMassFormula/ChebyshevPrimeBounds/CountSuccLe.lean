import Mathlib
import Formalism.PeriodIntegrals.PrimeCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop

namespace PI.PC

open Real

/- English proof (translation)
Unfold `tst at h`. Rewrite `h` using `[Nat.blt_eq]`. Take `⟨q, hqdef⟩ : ∃ q, q = (3225600000000 * m - 1) / (c * 6931471808)` from `⟨_, rfl⟩`. Rewrite `h` using `[← hqdef]`. Establish `hm256 : 1 ≤ m ^ 256` using `Nat.one_le_pow 256 m hm`.

Establish `hcpos : 0 < c`. Break down `Nat.eq_zero_or_pos c with h0 | h0` into its components or cases. It suffices to derive a contradiction. Substitute `h0` using the available equality. Establish `hq0 : q = 0` using `by rw [hqdef]; simp`.

Rewrite `h` using `[hq0, pow_zero]`. Conclude with `absurd h (not_lt.mpr hm256)`. Conclude with `h0`. Establish `hmR : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hlogm : 0 ≤ log (m : ℝ)` using `Real.log_nonneg hmR`.

Establish `h1 : 256 * log (m : ℝ) < q * log 2`. Establish `hR : ((m : ℝ)) ^ 256 < (2 : ℝ) ^ q` using `by exact_mod_cast h`. Establish `hl` using `Real.log_lt_log (by positivity) hR`. Rewrite `hl` using `[Real.log_pow, Real.log_pow]`. Move the coercions through the operations in `at hl`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (q : ℝ) * c * 6931471808 < 3225600000000 * m`. Establish `hN : q * (c * 6931471808) ≤ 3225600000000 * m - 1`. Rewrite using `[hqdef]`. Conclude with `Nat.div_mul_le_self _ _`.

Establish `hpos : 0 < 3225600000000 * m` using `by positivity`. Establish `hN' : q * (c * 6931471808) < 3225600000000 * m` using `Nat.lt_of_le_of_lt hN (Nat.sub_lt hpos one_pos)`. Establish `hC : ((q * (c * 6931471808) : ℕ) : ℝ) < ((3225600000000 * m : ℕ) : ℝ)`. Conclude with `hN'` after adjusting the coercions. Move the coercions through the operations in `at hC`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : log 2 < 0.6931471808` using `Real.log_two_lt_d9`. Establish `hcR : (0 : ℝ) < c` using `by exact_mod_cast hcpos`. Establish `hqc : (0 : ℝ) ≤ q * c` using `by positivity`. Establish `h4 : (c : ℝ) * (256 * log m) < c * (q * log 2)` using `mul_lt_mul_of_pos_left h1 hcR`.

Establish `h5 : ((q : ℝ) * c) * log 2 ≤ (q * c) * 0.6931471808` using `mul_le_mul_of_nonneg_left h3.le hqc`. Establish `h6 : (c' : ℝ) * log m ≤ c * log m` using `mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlogm`. Use polynomial arithmetic with `[h4, h5, h6, h2]`.
-/
theorem tst_sound {m c c' : ℕ} (h : tst m c = true) (hc : c' ≤ c) (hm : 1 ≤ m) :
    (c' : ℝ) * log m < 1.26 * m := by
  unfold tst at h
  rw [Nat.blt_eq] at h
  obtain ⟨q, hqdef⟩ : ∃ q, q = (3225600000000 * m - 1) / (c * 6931471808) := ⟨_, rfl⟩
  rw [← hqdef] at h
  have hm256 : 1 ≤ m ^ 256 := Nat.one_le_pow 256 m hm
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      subst h0
      have hq0 : q = 0 := by rw [hqdef]; simp
      rw [hq0, pow_zero] at h
      exact absurd h (not_lt.mpr hm256)
    · exact h0
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 ≤ log (m : ℝ) := Real.log_nonneg hmR
  have h1 : 256 * log (m : ℝ) < q * log 2 := by
    have hR : ((m : ℝ)) ^ 256 < (2 : ℝ) ^ q := by exact_mod_cast h
    have hl := Real.log_lt_log (by positivity) hR
    rw [Real.log_pow, Real.log_pow] at hl
    push_cast at hl
    linarith
  have h2 : (q : ℝ) * c * 6931471808 < 3225600000000 * m := by
    have hN : q * (c * 6931471808) ≤ 3225600000000 * m - 1 := by
      rw [hqdef]; exact Nat.div_mul_le_self _ _
    have hpos : 0 < 3225600000000 * m := by positivity
    have hN' : q * (c * 6931471808) < 3225600000000 * m :=
      Nat.lt_of_le_of_lt hN (Nat.sub_lt hpos one_pos)
    have hC : ((q * (c * 6931471808) : ℕ) : ℝ) < ((3225600000000 * m : ℕ) : ℝ) := by
      exact_mod_cast hN'
    push_cast at hC
    linarith
  have h3 : log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hqc : (0 : ℝ) ≤ q * c := by positivity
  have h4 : (c : ℝ) * (256 * log m) < c * (q * log 2) := mul_lt_mul_of_pos_left h1 hcR
  have h5 : ((q : ℝ) * c) * log 2 ≤ (q * c) * 0.6931471808 := mul_le_mul_of_nonneg_left h3.le hqc
  have h6 : (c' : ℝ) * log m ≤ c * log m :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlogm
  nlinarith [h4, h5, h6, h2]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `n c Q _ _ _ _ m hnm hmk`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ k ih`. Introduce `n c Q hrun hn hcount hcop m hnm hmk`. Simplify using `only [loop, force_eq] at hrun`. Distinguish the cases in `hg : Nat.gcd n Q = 1`. Rewrite `hrun` using `[if_pos hg, Bool.and_eq_true]`.

Take `⟨hb, hrest⟩` from `hrun`. Establish `hc1 : Nat.count Nat.Prime (n + 1) ≤ c + 1`. Apply the tactic sequence `rw [Nat.count_succ]; split_ifs <;> omega`. Break down `Nat.eq_or_lt_of_le hnm with rfl | hlt` into its components or cases. Conclude with `⟨c + 1, hc1, hb⟩`.

Use `ih (n + 1) (c + 1) _ hrest (by omega) hc1 ?_ m hlt (by omega)` and prove the remaining obligations. Introduce `p hp hnp`. Use `split_ifs`. Conclude with `Nat.Coprime.mul_right (hcop p hp (by omega)) ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))`. Conclude with `hcop p hp (by omega)`.

Rewrite `hrun` using `[if_neg hg, Bool.and_eq_true]`. Take `⟨hb, hrest⟩` from `hrun`. Establish `hnp : ¬ n.Prime` using `fun hp => hg (hcop n hp le_rfl)`. Establish `hc0 : Nat.count Nat.Prime (n + 1) ≤ c`. Rewrite using `[Nat.count_succ, if_neg hnp]`.

Use linear arithmetic over natural numbers and integers. Break down `Nat.eq_or_lt_of_le hnm with rfl | hlt` into its components or cases. Conclude with `⟨c, hc0, hb⟩`. Conclude with `ih (n + 1) c Q hrest (by omega) hc0 (fun p hp hnp' => hcop p hp (by omega)) m hlt (by omega)`.
-/
theorem loop_sound (B : ℕ) : ∀ k n c Q : ℕ, loop B k n c Q = true → 1 ≤ n →
    Nat.count Nat.Prime n ≤ c → (∀ p, p.Prime → n ≤ p → Nat.Coprime p Q) →
    ∀ m, n ≤ m → m < n + k → ∃ c', Nat.count Nat.Prime (m + 1) ≤ c' ∧ tst m c' = true := by
  intro k
  induction k with
  | zero =>
    intro n c Q _ _ _ _ m hnm hmk
    omega
  | succ k ih =>
    intro n c Q hrun hn hcount hcop m hnm hmk
    simp only [loop, force_eq] at hrun
    by_cases hg : Nat.gcd n Q = 1
    · rw [if_pos hg, Bool.and_eq_true] at hrun
      obtain ⟨hb, hrest⟩ := hrun
      have hc1 : Nat.count Nat.Prime (n + 1) ≤ c + 1 := by
        rw [Nat.count_succ]; split_ifs <;> omega
      rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
      · exact ⟨c + 1, hc1, hb⟩
      · refine ih (n + 1) (c + 1) _ hrest (by omega) hc1 ?_ m hlt (by omega)
        intro p hp hnp
        split_ifs
        · exact Nat.Coprime.mul_right (hcop p hp (by omega))
            ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
        · exact hcop p hp (by omega)
    · rw [if_neg hg, Bool.and_eq_true] at hrun
      obtain ⟨hb, hrest⟩ := hrun
      have hnp : ¬ n.Prime := fun hp => hg (hcop n hp le_rfl)
      have hc0 : Nat.count Nat.Prime (n + 1) ≤ c := by
        rw [Nat.count_succ, if_neg hnp]; omega
      rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
      · exact ⟨c, hc0, hb⟩
      · exact ih (n + 1) c Q hrest (by omega) hc0 (fun p hp hnp' => hcop p hp (by omega)) m hlt
          (by omega)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [Nat.count_succ, Nat.not_prime_zero]`. Consider the case `succ n ih`. Rewrite using `[Nat.count_succ]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem count_succ_le (n : ℕ) : Nat.count Nat.Prime (n + 1) ≤ n := by
  induction n with
  | zero => simp [Nat.count_succ, Nat.not_prime_zero]
  | succ n ih =>
    rw [Nat.count_succ]
    split_ifs <;> omega

/- English proof (translation)
Break down `Nat.eq_or_lt_of_le h1 with rfl | h1'` into its components or cases. Evaluate the numerical expressions. Establish `hc2 : Nat.count Nat.Prime 2 ≤ 0` using `by show Nat.count Nat.Prime (0 + 1 + 1) ≤ 0`. Simplify using `[Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one]`. Take `⟨c', hc', hb⟩` from `loop_sound 362 131070 2 0 1 loop_run (by norm_num) hc2 (fun p _ _ => Nat.coprime_one_right p) m h1' (by omega)`.

Conclude with `tst_sound hb hc' h1`.
-/
theorem small_nat (m : ℕ) (h1 : 1 ≤ m) (h2 : m < 131072) :
    (Nat.count Nat.Prime (m + 1) : ℝ) * log m < 1.26 * m := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
  · norm_num
  · have hc2 : Nat.count Nat.Prime 2 ≤ 0 := by
      show Nat.count Nat.Prime (0 + 1 + 1) ≤ 0
      simp [Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one]
    obtain ⟨c', hc', hb⟩ := loop_sound 362 131070 2 0 1 loop_run (by norm_num) hc2
      (fun p _ _ => Nat.coprime_one_right p) m h1' (by omega)
    exact tst_sound hb hc' h1

/- English proof (translation)
Establish `hn' : (0 : ℝ) < n` using `Nat.cast_pos.mpr (by omega)`. Establish `hy0 : 0 < y` using `lt_of_lt_of_le hn' hy`. Establish `hkR : (k : ℝ) ≤ n` using `by exact_mod_cast hk`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hlog : log y - log n ≤ y / n - 1`.

Rewrite using `[← Real.log_div hy0.ne' hn'.ne']`. Conclude with `Real.log_le_sub_one_of_pos (div_pos hy0 hn')`. Establish `ht : 0 ≤ y / n - 1` using `sub_nonneg.mpr ((one_le_div hn').mpr hy)`. Establish `hnt : (n : ℝ) * (y / n - 1) = y - n`. Rewrite using `[mul_sub, mul_div_cancel₀ y hn'.ne', mul_one]`.

Establish `h1 : (k : ℝ) * (log y - log n) ≤ k * (y / n - 1)` using `mul_le_mul_of_nonneg_left hlog hk0`. Establish `h2 : (k : ℝ) * (y / n - 1) ≤ n * (y / n - 1)` using `mul_le_mul_of_nonneg_right hkR ht`. Use polynomial arithmetic with `[h, h1, h2, hnt, hy]`.
-/
theorem real_of_nat {n k : ℕ} {y : ℝ} (hn : 1 ≤ n) (hk : k ≤ n) (h : (k : ℝ) * log n < 1.26 * n)
    (hy : (n : ℝ) ≤ y) : (k : ℝ) * log y < 1.26 * y := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hy0 : 0 < y := lt_of_lt_of_le hn' hy
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog : log y - log n ≤ y / n - 1 := by
    rw [← Real.log_div hy0.ne' hn'.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hy0 hn')
  have ht : 0 ≤ y / n - 1 := sub_nonneg.mpr ((one_le_div hn').mpr hy)
  have hnt : (n : ℝ) * (y / n - 1) = y - n := by
    rw [mul_sub, mul_div_cancel₀ y hn'.ne', mul_one]
  have h1 : (k : ℝ) * (log y - log n) ≤ k * (y / n - 1) := mul_le_mul_of_nonneg_left hlog hk0
  have h2 : (k : ℝ) * (y / n - 1) ≤ n * (y / n - 1) := mul_le_mul_of_nonneg_right hkR ht
  nlinarith [h, h1, h2, hnt, hy]

/- English proof (translation)
Rewrite using `[Nat.count_eq_card_filter_range]`. Both sides reduce to the same expression.
-/
theorem pr_card (y : ℝ) : (pr y).card = Nat.count Nat.Prime (⌊y⌋₊ + 1) := by
  rw [Nat.count_eq_card_filter_range]
  rfl

/- English proof (translation)
Unfold `PCSmall`. Introduce `y hy1 hy2`. Establish `hy0 : 0 ≤ y` using `by linarith`. Establish `hm1 : 1 ≤ ⌊y⌋₊` using `Nat.le_floor (by exact_mod_cast hy1.le)`. Establish `hm2 : ⌊y⌋₊ < 131072` using `(Nat.floor_lt hy0).mpr (by exact_mod_cast hy2)`.

Establish `hfl : (⌊y⌋₊ : ℝ) ≤ y` using `Nat.floor_le hy0`. Establish `hA` using `small_nat _ hm1 hm2`. Establish `hB` using `real_of_nat hm1 (count_succ_le _) hA hfl`. Establish `hlog : 0 < log y` using `Real.log_pos hy1`. Rewrite using `[pr_card, lt_div_iff₀ hlog]`.

Conclude with `hB`.
-/
theorem pcSmall : PCSmall 131072 := by
  unfold PCSmall
  intro y hy1 hy2
  have hy0 : 0 ≤ y := by linarith
  have hm1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy1.le)
  have hm2 : ⌊y⌋₊ < 131072 := (Nat.floor_lt hy0).mpr (by exact_mod_cast hy2)
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hA := small_nat _ hm1 hm2
  have hB := real_of_nat hm1 (count_succ_le _) hA hfl
  have hlog : 0 < log y := Real.log_pos hy1
  rw [pr_card, lt_div_iff₀ hlog]
  exact hB

end PI.PC
