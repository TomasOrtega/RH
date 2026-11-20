import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.Uniq

/- English proof (translation)
Take `⟨m, hm⟩` from `hpos`. Establish `hbdd : ∃ b : ℤ, ∀ z : ℤ, d z < 0 → b ≤ z` using `⟨m, fun z hz => by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `hanti hc` as an intermediate fact.

Use the proof step `linarith⟩`. Take `⟨n₀, hn₀, hmin⟩` from `Int.exists_least_of_bdd hbdd hneg`. Establish `hafter : ∀ k, n₀ ≤ k → d k < 0` using `fun k hk => by`. Break down `hk.lt_or_eq with h | h` into its components or cases. Conclude with `(hanti h).trans hn₀`.

Rewrite using `[← h]`. Conclude with `hn₀`. Establish `hbefore : ∀ k, k < n₀ → 0 < d k` using `fun k hk => by`. Break down `lt_or_gt_of_ne (hne k) with h | h` into its components or cases. Conclude with `absurd (hmin k h) (not_le.2 hk)`.

Conclude with `h`. Establish `hfwd : ∀ k : ℕ, f (n₀ + k + 1) < f n₀`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Use `hd n₀` as an intermediate fact. Use `hafter n₀ le_rfl` as an intermediate fact. Simplify using `only [Nat.cast_zero, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ k ih`.

Rewrite using `[show n₀ + ((k + 1 : ℕ) : ℤ) + 1 = n₀ + k + 1 + 1 by push_cast; ring]`. Use `hd (n₀ + k + 1)` as an intermediate fact. Use `hafter (n₀ + k + 1) (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbwd : ∀ k : ℕ, f (n₀ - k - 1) < f n₀`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Use `hd (n₀ - 1)` as an intermediate fact. Use `hbefore (n₀ - 1) (by omega)` as an intermediate fact.

Simplify using `only [Nat.cast_zero, sub_zero]`. Rewrite `*` using `[sub_add_cancel]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ k ih`. Use `hd (n₀ - ((k + 1 : ℕ) : ℤ) - 1)` as an intermediate fact.

Use `hbefore (n₀ - ((k + 1 : ℕ) : ℤ) - 1) (by omega)` as an intermediate fact. Rewrite `*` using `[show n₀ - ((k + 1 : ℕ) : ℤ) - 1 + 1 = n₀ - k - 1 by push_cast; ring]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨n₀, fun n hn => ?_⟩` and prove the remaining obligations. Break down `lt_or_gt_of_ne hn with h | h` into its components or cases.

Use `hbwd (n₀ - n - 1).toNat` as an intermediate fact. Rewrite `this` using `[show n₀ - ((n₀ - n - 1).toNat : ℤ) - 1 = n by omega]`. Then use the resulting hypothesis. Use `hfwd (n - n₀ - 1).toNat` as an intermediate fact. Rewrite `this` using `[show n₀ + ((n - n₀ - 1).toNat : ℤ) + 1 = n by omega]`. Then use the resulting hypothesis.
-/
theorem exists_strict_max (f d : ℤ → ℝ) (hd : ∀ n, f (n + 1) = f n + d n) (hanti : StrictAnti d)
    (hne : ∀ n, d n ≠ 0) (hpos : ∃ m, 0 < d m) (hneg : ∃ m, d m < 0) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → f n < f n₀ := by
  obtain ⟨m, hm⟩ := hpos
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, d z < 0 → b ≤ z := ⟨m, fun z hz => by
    by_contra hc
    push_neg at hc
    have := hanti hc
    linarith⟩
  obtain ⟨n₀, hn₀, hmin⟩ := Int.exists_least_of_bdd hbdd hneg
  have hafter : ∀ k, n₀ ≤ k → d k < 0 := fun k hk => by
    rcases hk.lt_or_eq with h | h
    · exact (hanti h).trans hn₀
    · rw [← h]; exact hn₀
  have hbefore : ∀ k, k < n₀ → 0 < d k := fun k hk => by
    rcases lt_or_gt_of_ne (hne k) with h | h
    · exact absurd (hmin k h) (not_le.2 hk)
    · exact h
  have hfwd : ∀ k : ℕ, f (n₀ + k + 1) < f n₀ := by
    intro k
    induction k with
    | zero =>
      have := hd n₀
      have := hafter n₀ le_rfl
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ k ih =>
      rw [show n₀ + ((k + 1 : ℕ) : ℤ) + 1 = n₀ + k + 1 + 1 by push_cast; ring]
      have := hd (n₀ + k + 1)
      have := hafter (n₀ + k + 1) (by omega)
      linarith
  have hbwd : ∀ k : ℕ, f (n₀ - k - 1) < f n₀ := by
    intro k
    induction k with
    | zero =>
      have := hd (n₀ - 1)
      have := hbefore (n₀ - 1) (by omega)
      simp only [Nat.cast_zero, sub_zero]
      rw [sub_add_cancel] at *
      linarith
    | succ k ih =>
      have := hd (n₀ - ((k + 1 : ℕ) : ℤ) - 1)
      have := hbefore (n₀ - ((k + 1 : ℕ) : ℤ) - 1) (by omega)
      rw [show n₀ - ((k + 1 : ℕ) : ℤ) - 1 + 1 = n₀ - k - 1 by push_cast; ring] at *
      linarith
  refine ⟨n₀, fun n hn => ?_⟩
  rcases lt_or_gt_of_ne hn with h | h
  · have := hbwd (n₀ - n - 1).toNat
    rwa [show n₀ - ((n₀ - n - 1).toNat : ℤ) - 1 = n by omega] at this
  · have := hfwd (n - n₀ - 1).toNat
    rwa [show n₀ + ((n - n₀ - 1).toNat : ℤ) + 1 = n by omega] at this

end GlobalTheory.PSer.Uniq

namespace GlobalTheory.PSer.Uniq

/- English proof (translation)
Introduce `l _ h s hh hs0 hs1`. Establish `hlp : l.Prime` using `Fact.out`. Establish `hν1 : ‖(l : ℂ_[l])‖ < 1` using `GlobalTheory.RingBasics.norm_p_lt`. Establish `hν0 : 0 < ‖(l : ℂ_[l])‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 hlp.ne_zero)`. Use `set ν := ‖(l : ℂ_[l])‖ with hν`.

Establish `hL : (1 : ℝ) < l` using `by exact_mod_cast hlp.one_lt`. Establish `hL0 : (0 : ℝ) < l` using `by linarith`. Establish `hls : Real.log s < 0` using `Real.log_neg hs0 hs1`. Establish `hlν : Real.log ν < 0` using `Real.log_neg hν0 hν1`. Establish `hq : (1 : ℝ) < (l : ℝ) ^ h` using `one_lt_pow₀ hL (by omega)`.

Use `set c : ℝ := ((l : ℝ) ^ h - 1) * Real.log s with hc_def`. Establish `hc : c < 0` using `mul_neg_of_pos_of_neg (by linarith) hls`. Set `u : ℕ → ℤ → ℝ` to `fun j n => (l : ℝ) ^ (n * h + j : ℤ)`. Set `f : ℕ → ℤ → ℝ` to `fun j n => -(n : ℝ) * Real.log ν + u j n * Real.log s`. Set `d : ℕ → ℤ → ℝ` to `fun j n => -Real.log ν + u j n * c`.

Establish `hu_succ : ∀ j n, u j (n + 1) = u j n * (l : ℝ) ^ h` using `fun j n => by`. Simplify using `only [u]`. Rewrite using `[show ((n + 1) * (h : ℤ) + (j : ℤ)) = (n * h + j) + ((h : ℕ) : ℤ) by ring, zpow_add₀ hL0.ne', zpow_natCast]`. Establish `hd : ∀ j n, f j (n + 1) = f j n + d j n`. Introduce `j n`.

Simplify using `only [f, d, hc_def]`. Rewrite using `[hu_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmono : ∀ j, StrictMono (u j)` using `fun j a b hab => by`.

Simplify using `only [u]`. Apply `zpow_lt_zpow_right₀ hL` to reduce the goal to its premises. Establish `: (0 : ℤ) < (b - a) * h` using `mul_pos (by omega) (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hanti : ∀ j, StrictAnti (d j)` using `fun j a b hab => by`.

Simplify using `only [d]`. Use `mul_lt_mul_of_neg_right (hmono j hab) hc` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set B : ℝ := Real.log ν / c with hB_def`. Establish `hB : 0 < B` using `div_pos_of_neg_of_neg hlν hc`.

Establish `hBc : B * c = Real.log ν` using `div_mul_cancel₀ _ hc.ne`. Establish `hpos : ∀ j, ∃ m, 0 < d j m` using `fun j => by`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one hB (inv_lt_one_of_one_lt₀ hL)`. Use `⟨-((k : ℤ) + j), ?_⟩` and prove the remaining obligations. Establish `h1 : u j (-((k : ℤ) + j)) ≤ (l : ℝ) ^ (-(k : ℤ))`.

Simplify using `only [u]`. Apply `zpow_le_zpow_right₀ hL.le` to reduce the goal to its premises. Establish `: (0 : ℤ) ≤ ((k : ℤ) + j) * ((h : ℤ) - 1)` using `mul_nonneg (by omega) (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (l : ℝ) ^ (-(k : ℤ)) = ((l : ℝ)⁻¹) ^ k` using `by rw [zpow_neg, zpow_natCast, inv_pow]`.

Establish `h3 : u j (-((k : ℤ) + j)) < B` using `by rw [h2] at h1; exact h1.trans_lt hk`. Use `mul_lt_mul_of_neg_right h3 hc` as an intermediate fact. Simplify using `only [d]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hneg : ∀ j, ∃ m, d j m < 0` using `fun j => by`.

Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt B hL`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `h1 : (l : ℝ) ^ ((k : ℤ)) ≤ u j k`. Simplify using `only [u]`. Apply `zpow_le_zpow_right₀ hL.le` to reduce the goal to its premises.

Establish `: (0 : ℤ) ≤ (k : ℤ) * ((h : ℤ) - 1)` using `mul_nonneg (by omega) (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Rewrite `h1` using `[zpow_natCast]`. Use `mul_lt_mul_of_neg_right (hk.trans_le h1) hc` as an intermediate fact. Simplify using `only [d]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `htie : ∀ n n', d 0 n = 0 → d 1 n' = 0 → False`. Introduce `n n' h0 h1`. Establish `e1 : u 0 n * c = u 1 n' * c` using `by simp only [d] at h0 h1; linarith`. Establish `e2` using `(zpow_right_strictMono₀ hL).injective (mul_right_cancel₀ hc.ne e1)`.

Move the coercions through the operations in `at e2`. Establish `hdvd : (h : ℤ) ∣ 1` using `⟨n - n', by linear_combination -e2⟩`. Use `Int.eq_one_of_dvd_one (by positivity) hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hfin : ∀ j, (∀ n, d j n ≠ 0) → ∃ n₀ : ℤ, ∀ n, n ≠ n₀ → ν ^ (-n) * s ^ (u j n) < ν ^ (-n₀) * s ^ (u j n₀)`.

Introduce `j hne`. Take `⟨n₀, hn₀⟩` from `exists_strict_max (f j) (d j) (hd j) (hanti j) hne (hpos j) (hneg j)`. Use `⟨n₀, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hT : ∀ m, Real.log (ν ^ (-m) * s ^ (u j m)) = f j m` using `fun m => by`. Rewrite using `[Real.log_mul (zpow_pos hν0 _).ne' (Real.rpow_pos_of_pos hs0 _).ne', Real.log_zpow, Real.log_rpow hs0]`.

Simplify using `only [f]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Real.log_lt_log_iff (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _)) (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _)), hT, hT]`. Conclude with `hn₀ n hn`.

Distinguish the cases in `H : ∀ n, d 0 n ≠ 0`. Conclude with `⟨0, by norm_num, hfin 0 H⟩`. Use `push_neg at H`. Take `⟨n, hn⟩` from `H`. Conclude with `⟨1, by norm_num, hfin 1 fun n' hn' => htie n n' hn hn'⟩`.
-/
theorem exists_unique_max_term : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (s : ℝ), 2 ≤ h → 0 < s → s < 1 →
    ∃ j : ℕ, j < 2 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ →
      ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) <
        ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
  intro l _ h s hh hs0 hs1
  have hlp : l.Prime := Fact.out
  have hν1 : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hν0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hlp.ne_zero)
  set ν := ‖(l : ℂ_[l])‖ with hν
  have hL : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hL0 : (0 : ℝ) < l := by linarith
  have hls : Real.log s < 0 := Real.log_neg hs0 hs1
  have hlν : Real.log ν < 0 := Real.log_neg hν0 hν1
  have hq : (1 : ℝ) < (l : ℝ) ^ h := one_lt_pow₀ hL (by omega)
  set c : ℝ := ((l : ℝ) ^ h - 1) * Real.log s with hc_def
  have hc : c < 0 := mul_neg_of_pos_of_neg (by linarith) hls
  let u : ℕ → ℤ → ℝ := fun j n => (l : ℝ) ^ (n * h + j : ℤ)
  let f : ℕ → ℤ → ℝ := fun j n => -(n : ℝ) * Real.log ν + u j n * Real.log s
  let d : ℕ → ℤ → ℝ := fun j n => -Real.log ν + u j n * c
  have hu_succ : ∀ j n, u j (n + 1) = u j n * (l : ℝ) ^ h := fun j n => by
    simp only [u]
    rw [show ((n + 1) * (h : ℤ) + (j : ℤ)) = (n * h + j) + ((h : ℕ) : ℤ) by ring,
      zpow_add₀ hL0.ne', zpow_natCast]
  have hd : ∀ j n, f j (n + 1) = f j n + d j n := by
    intro j n
    simp only [f, d, hc_def]
    rw [hu_succ]
    push_cast
    ring
  have hmono : ∀ j, StrictMono (u j) := fun j a b hab => by
    simp only [u]
    apply zpow_lt_zpow_right₀ hL
    have : (0 : ℤ) < (b - a) * h := mul_pos (by omega) (by omega)
    linarith
  have hanti : ∀ j, StrictAnti (d j) := fun j a b hab => by
    simp only [d]
    have := mul_lt_mul_of_neg_right (hmono j hab) hc
    linarith
  set B : ℝ := Real.log ν / c with hB_def
  have hB : 0 < B := div_pos_of_neg_of_neg hlν hc
  have hBc : B * c = Real.log ν := div_mul_cancel₀ _ hc.ne
  have hpos : ∀ j, ∃ m, 0 < d j m := fun j => by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hB (inv_lt_one_of_one_lt₀ hL)
    refine ⟨-((k : ℤ) + j), ?_⟩
    have h1 : u j (-((k : ℤ) + j)) ≤ (l : ℝ) ^ (-(k : ℤ)) := by
      simp only [u]
      apply zpow_le_zpow_right₀ hL.le
      have : (0 : ℤ) ≤ ((k : ℤ) + j) * ((h : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
    have h2 : (l : ℝ) ^ (-(k : ℤ)) = ((l : ℝ)⁻¹) ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
    have h3 : u j (-((k : ℤ) + j)) < B := by rw [h2] at h1; exact h1.trans_lt hk
    have := mul_lt_mul_of_neg_right h3 hc
    simp only [d]
    linarith
  have hneg : ∀ j, ∃ m, d j m < 0 := fun j => by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hL
    refine ⟨k, ?_⟩
    have h1 : (l : ℝ) ^ ((k : ℤ)) ≤ u j k := by
      simp only [u]
      apply zpow_le_zpow_right₀ hL.le
      have : (0 : ℤ) ≤ (k : ℤ) * ((h : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
    rw [zpow_natCast] at h1
    have := mul_lt_mul_of_neg_right (hk.trans_le h1) hc
    simp only [d]
    linarith
  have htie : ∀ n n', d 0 n = 0 → d 1 n' = 0 → False := by
    intro n n' h0 h1
    have e1 : u 0 n * c = u 1 n' * c := by simp only [d] at h0 h1; linarith
    have e2 := (zpow_right_strictMono₀ hL).injective (mul_right_cancel₀ hc.ne e1)
    push_cast at e2
    have hdvd : (h : ℤ) ∣ 1 := ⟨n - n', by linear_combination -e2⟩
    have := Int.eq_one_of_dvd_one (by positivity) hdvd
    omega
  have hfin : ∀ j, (∀ n, d j n ≠ 0) → ∃ n₀ : ℤ, ∀ n, n ≠ n₀ →
      ν ^ (-n) * s ^ (u j n) < ν ^ (-n₀) * s ^ (u j n₀) := by
    intro j hne
    obtain ⟨n₀, hn₀⟩ := exists_strict_max (f j) (d j) (hd j) (hanti j) hne (hpos j) (hneg j)
    refine ⟨n₀, fun n hn => ?_⟩
    have hT : ∀ m, Real.log (ν ^ (-m) * s ^ (u j m)) = f j m := fun m => by
      rw [Real.log_mul (zpow_pos hν0 _).ne' (Real.rpow_pos_of_pos hs0 _).ne', Real.log_zpow,
        Real.log_rpow hs0]
      simp only [f]
      push_cast
      ring
    rw [← Real.log_lt_log_iff (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _))
      (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _)), hT, hT]
    exact hn₀ n hn
  by_cases H : ∀ n, d 0 n ≠ 0
  · exact ⟨0, by norm_num, hfin 0 H⟩
  · push_neg at H
    obtain ⟨n, hn⟩ := H
    exact ⟨1, by norm_num, hfin 1 fun n' hn' => htie n n' hn hn'⟩

end GlobalTheory.PSer.Uniq
