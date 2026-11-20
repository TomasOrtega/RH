import Mathlib

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def weightedPartialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n * ((x / n - 1 : ℝ) : ℂ)

def partialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n

/- English proof (translation)
Establish `h1 : ∀ m : ℕ, Icc 1 m = Ioc 0 m` using `fun m => by`. Use extensionality with `n`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ioc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, h1, Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]`.
-/
lemma sum_Icc_eq_add_sum_Ioc (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have h1 : ∀ m : ℕ, Icc 1 m = Ioc 0 m := fun m => by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h1, Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]

/- English proof (translation)
Unfold `weightedPartialSumUpTo partialSumUpTo`. Rewrite using `[sum_Icc_eq_add_sum_Ioc _ (Nat.floor_mono hyY)]`. Simplify using `only [mul_add, Finset.mul_sum]`. Rewrite using `[show ∀ a b c : ℂ, a + b - c = (a - c) + b from fun a b c => by ring, ← Finset.sum_sub_distrib]`. Use `congr 1`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `n _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma weightedSum_identity (f : ℕ → ℂ) {y Y : ℝ} (hyY : y ≤ Y) :
    (y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y
      = ((Y - y : ℝ) : ℂ) * partialSumUpTo f y
        + ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ) := by
  unfold weightedPartialSumUpTo partialSumUpTo
  rw [sum_Icc_eq_add_sum_Ioc _ (Nat.floor_mono hyY)]
  simp only [mul_add, Finset.mul_sum]
  rw [show ∀ a b c : ℂ, a + b - c = (a - c) + b from fun a b c => by ring, ← Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring

/- English proof (translation)
Establish `hY1 : 1 ≤ Y` using `le_trans hy hyY`. Establish `hterm : ∀ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ ≤ (Y - y) * Real.log Y`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Ioc]`. Establish `hn1 : y < (n : ℝ)`.

Use `Nat.lt_floor_add_one y` as an intermediate fact. Establish `h2 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ n` using `by exact_mod_cast hn.1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn2 : (n : ℝ) ≤ Y`. Use `Nat.floor_le (show 0 ≤ Y by linarith)` as an intermediate fact.

Establish `h2 : (n : ℝ) ≤ (⌊Y⌋₊ : ℝ)` using `by exact_mod_cast hn.2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnpos : (0:ℝ) < n` using `by linarith`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Establish `hA : 0 ≤ y * (Y / n - 1)`.

Apply `mul_nonneg (by linarith)` to reduce the goal to its premises. Rewrite using `[sub_nonneg, le_div_iff₀ hnpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : y * (Y / n - 1) ≤ Y - y`. Establish `e : y * (Y / n - 1) = (Y - n) * (y / n)` using `by field_simp`.

Rewrite using `[e]`. Establish `h3 : y / n ≤ 1` using `by rw [div_le_one hnpos]; linarith`. Establish `h4 : 0 ≤ Y - n` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[abs_of_nonneg hA]`.

Establish `hf' : ‖f n‖ ≤ Real.log Y`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`.

Use `_ ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by`. Apply `mul_le_mul_of_nonneg_right _ (mul_nonneg (by linarith) (Real.log_nonneg hY1))` to reduce the goal to its premises. Rewrite using `[Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hyY)]`. Establish `h1` using `Nat.floor_le (show 0 ≤ Y by linarith)`. Establish `h2` using `Nat.lt_floor_add_one y`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_sum_Ioc_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  have hY1 : 1 ≤ Y := le_trans hy hyY
  have hterm : ∀ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊,
      ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ ≤ (Y - y) * Real.log Y := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : y < (n : ℝ) := by
      have := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
      linarith
    have hn2 : (n : ℝ) ≤ Y := by
      have := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 : (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn.2
      linarith
    have hnpos : (0:ℝ) < n := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hA : 0 ≤ y * (Y / n - 1) := by
      apply mul_nonneg (by linarith)
      rw [sub_nonneg, le_div_iff₀ hnpos]; linarith
    have hB : y * (Y / n - 1) ≤ Y - y := by
      have e : y * (Y / n - 1) = (Y - n) * (y / n) := by field_simp
      rw [e]
      have h3 : y / n ≤ 1 := by rw [div_le_one hnpos]; linarith
      have h4 : 0 ≤ Y - n := by linarith
      nlinarith
    rw [abs_of_nonneg hA]
    have hf' : ‖f n‖ ≤ Real.log Y :=
      calc ‖f n‖ ≤ Λ n := hf n
        _ ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log Y := Real.log_le_log hnpos hn2
    calc ‖f n‖ * (y * (Y / n - 1)) ≤ Real.log Y * (Y - y) :=
          mul_le_mul hf' hB hA (Real.log_nonneg hY1)
      _ = (Y - y) * Real.log Y := by ring
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, (Y - y) * Real.log Y := Finset.sum_le_sum hterm
    _ = ((Ioc ⌊y⌋₊ ⌊Y⌋₊).card : ℝ) * ((Y - y) * Real.log Y) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by linarith) (Real.log_nonneg hY1))
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hyY)]
      have h1 := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 := Nat.lt_floor_add_one y
      linarith

/- English proof (translation)
Rewrite using `[weightedSum_identity f hyY, add_sub_cancel_left]`. Conclude with `norm_sum_Ioc_le f hf hy hyY`.
-/
lemma norm_weightedSum_sub_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖((y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y) - ((Y - y : ℝ) : ℂ) * partialSumUpTo f y‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  rw [weightedSum_identity f hyY, add_sub_cancel_left]
  exact norm_sum_Ioc_le f hf hy hyY

/- English proof (translation)
Use `set K := Nat.log 2 N`. Use `set g : ℕ → ℝ := fun n => Λ n * (if n.Coprime q then 0 else 1) with hg`. Establish `hgle : ∀ n, g n ≤ Λ n` using `fun n => by`. Apply the tactic sequence `simp only [hg]; split_ifs <;> simp [vonMangoldt_nonneg]`. Establish `hsub : (Icc 1 N).filter (fun n => g n ≠ 0) ⊆ (q ^ K).divisors`.

Introduce `n hn`. Rewrite `hn` using `[Finset.mem_filter, Finset.mem_Icc]`. Take `⟨⟨_, hN⟩, hgn⟩` from `hn`. Establish `hΛ : Λ n ≠ 0` using `by intro h; apply hgn; simp [hg, h]`. Establish `hnc : ¬ n.Coprime q` using `by intro h; apply hgn; simp [hg, h]`.

Take `⟨p, k, hp, hk, rfl⟩` from `(isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)`. Establish `hpq : p ∣ q`. Assume the negation of the conclusion as `hc`. Conclude with `hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hc))`. Establish `hkK : k ≤ K`.

Apply `Nat.le_log_of_pow_le one_lt_two` to reduce the goal to its premises. Conclude with `le_trans (Nat.pow_le_pow_left hp.two_le k) hN`. Rewrite using `[Nat.mem_divisors]`. Conclude with `⟨(pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK), pow_ne_zero _ hq⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma sum_vonMangoldt_not_coprime_le (q : ℕ) (hq : q ≠ 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, Λ n * (if n.Coprime q then 0 else 1) ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  set K := Nat.log 2 N
  set g : ℕ → ℝ := fun n => Λ n * (if n.Coprime q then 0 else 1) with hg
  have hgle : ∀ n, g n ≤ Λ n := fun n => by
    simp only [hg]; split_ifs <;> simp [vonMangoldt_nonneg]
  have hsub : (Icc 1 N).filter (fun n => g n ≠ 0) ⊆ (q ^ K).divisors := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hN⟩, hgn⟩ := hn
    have hΛ : Λ n ≠ 0 := by intro h; apply hgn; simp [hg, h]
    have hnc : ¬ n.Coprime q := by intro h; apply hgn; simp [hg, h]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hpq : p ∣ q := by
      by_contra hc
      exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hc))
    have hkK : k ≤ K := by
      apply Nat.le_log_of_pow_le one_lt_two
      exact le_trans (Nat.pow_le_pow_left hp.two_le k) hN
    rw [Nat.mem_divisors]
    exact ⟨(pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK), pow_ne_zero _ hq⟩
  calc ∑ n ∈ Icc 1 N, g n = ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), g n :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), Λ n := Finset.sum_le_sum fun n _ => hgle n
    _ ≤ ∑ n ∈ (q ^ K).divisors, Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = (K : ℝ) * Real.log q := by rw [vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

/- English proof (translation)
Use `split_ifs with h`. Conclude with `MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 h)`. Conclude with `MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).1 hu))`.
-/
lemma one_apply_natCast {q : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if n.Coprime q then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 h)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).1 hu))

end Formalism.ZeroFreeDirichlet
