import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LiftExp

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `succ n ih`. Take `⟨r, hr, h⟩` from `ih`. Use `⟨(n.choose 2 : ℕ) + (r + x * r), ?_, ?_⟩` and prove the remaining obligations.

Use `(Padic.nonarchimedean _ _).trans (max_le ?_ ((Padic.nonarchimedean _ _).trans (max_le hr ?_)))` and prove the remaining obligations. Conclude with `IsUltrametricDist.norm_natCast_le_one _ _`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ hx (norm_nonneg _) hr`. Establish `h2 : (1 + x) ^ n = 1 + (n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r))`.

Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[pow_succ, h2, Nat.choose_succ_succ' n 1, Nat.choose_one_right]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_add_pow_expand (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∃ r : ℚ_[l], ‖r‖ ≤ 1 ∧
      (1 + x) ^ n - 1 = n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r) := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, h⟩ := ih
    refine ⟨(n.choose 2 : ℕ) + (r + x * r), ?_, ?_⟩
    · refine (Padic.nonarchimedean _ _).trans (max_le ?_ ((Padic.nonarchimedean _ _).trans
        (max_le hr ?_)))
      · exact IsUltrametricDist.norm_natCast_le_one _ _
      · rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hr
    · have h2 : (1 + x) ^ n = 1 + (n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r)) := by
        rw [← h]; ring
      rw [pow_succ, h2, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
      push_cast
      ring

/- English proof (translation)
Rewrite using `[Padic.add_eq_max_of_ne h.ne', max_eq_left h.le]`.
-/
theorem norm_add_of_lt {a b : ℚ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [Padic.add_eq_max_of_ne h.ne', max_eq_left h.le]

/- English proof (translation)
Conclude with `hl.out.one_lt` after adjusting the coercions.
-/
theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt

/- English proof (translation)
The claim follows from `zpow_lt_zpow_right₀ one_lt_l h`.
-/
theorem zpow_lt {a b : ℤ} (h : a < b) : (l : ℝ) ^ a < (l : ℝ) ^ b :=
  zpow_lt_zpow_right₀ one_lt_l h

/- English proof (translation)
Establish `hl0 : (l : ℝ) ≠ 0` using `(zero_lt_one.trans one_lt_l).ne'`. Establish `hx : ‖u - 1‖ ≤ 1`. Rewrite using `[hu]; exact zpow_le_one_of_nonpos₀ one_lt_l.le (by omega)`. Take `⟨r, hr, h⟩` from `one_add_pow_expand (u - 1) hx n`. Rewrite `h` using `[add_sub_cancel]`.

Establish `hm : ‖(n : ℚ_[l]) * (u - 1)‖ = (l : ℝ) ^ (-((j : ℤ) + e))`. Rewrite using `[norm_mul, hn, hu, ← zpow_add₀ hl0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, norm_add_of_lt, hm]`.

Rewrite using `[hm]`. Use `(Padic.nonarchimedean _ _).trans_lt (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, hu]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zpow_add₀ hl0, zpow_mul]`.

Use `norm_cast`. Use `_ < _ := zpow_lt (by omega)`. Rewrite using `[norm_mul, norm_pow, hu]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one, zpow_mul]`.

Use `norm_cast`. Use `_ < _ := zpow_lt (by omega)`.
-/
theorem norm_pow_sub_one_of (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (e c : ℤ) (hn : ‖(n : ℚ_[l])‖ = (l : ℝ) ^ (-e))
    (hc : ‖((n.choose 2 : ℕ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-c)) (h1 : e < c + j) (h2 : e < 2 * j) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
  have hl0 : (l : ℝ) ≠ 0 := (zero_lt_one.trans one_lt_l).ne'
  have hx : ‖u - 1‖ ≤ 1 := by
    rw [hu]; exact zpow_le_one_of_nonpos₀ one_lt_l.le (by omega)
  obtain ⟨r, hr, h⟩ := one_add_pow_expand (u - 1) hx n
  rw [add_sub_cancel] at h
  have hm : ‖(n : ℚ_[l]) * (u - 1)‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
    rw [norm_mul, hn, hu, ← zpow_add₀ hl0]; congr 1; ring
  rw [h, norm_add_of_lt, hm]
  rw [hm]
  refine (Padic.nonarchimedean _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ (l : ℝ) ^ (-c) * ((l : ℝ) ^ (-(j : ℤ))) ^ 2 := by gcongr
      _ = (l : ℝ) ^ (-c + (-(j : ℤ)) * 2) := by
        rw [zpow_add₀ hl0, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ ((l : ℝ) ^ (-(j : ℤ))) ^ 3 * 1 := by gcongr
      _ = (l : ℝ) ^ ((-(j : ℤ)) * 3) := by
        rw [mul_one, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)

/- English proof (translation)
Use `norm_pow_sub_one_of j hj u hu n 0 0 (by` as an intermediate fact. Rewrite using `[neg_zero, zpow_zero, Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)`. Use the proof step `(by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)`. Use the proof step `(by omega) (by omega)`.

Simplify using `using this`.
-/
theorem norm_pow_coprime (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (hn : ¬ l ∣ n) : ‖u ^ n - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by
  have := norm_pow_sub_one_of j hj u hu n 0 0
    (by
      rw [neg_zero, zpow_zero, Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
    (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
    (by omega) (by omega)
  simpa using this

/- English proof (translation)
Establish `hn : ‖(l : ℚ_[l])‖ = (l : ℝ) ^ (-(1 : ℤ))` using `by simp`. Establish `hj1` using `hj.1`. Use `push_cast`. Distinguish the cases in `h2 : l = 2`. Use `hj.2 h2` as an intermediate fact.

Conclude with `norm_pow_sub_one_of j hj.1 u hu l 1 0 hn (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _) (by omega) (by omega)`. Establish `h3 : 2 < l` using `lt_of_le_of_ne hl.out.two_le (Ne.symm h2)`. Take `⟨m, hm⟩` from `hl.out.dvd_choose_self (k := 2) two_ne_zero h3`. Use `norm_pow_sub_one_of j hj.1 u hu l 1 1 hn ?_ (by omega) (by omega)` and prove the remaining obligations. Rewrite using `[hm, Nat.cast_mul, norm_mul, hn]`.

Conclude with `mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)`.
-/
theorem norm_pow_prime (j : ℕ) (hj : Lev l j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ l - 1‖ = (l : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) := by
  have hn : ‖(l : ℚ_[l])‖ = (l : ℝ) ^ (-(1 : ℤ)) := by simp
  have hj1 := hj.1
  push_cast
  by_cases h2 : l = 2
  · have := hj.2 h2
    exact norm_pow_sub_one_of j hj.1 u hu l 1 0 hn
      (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
      (by omega) (by omega)
  · have h3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
    obtain ⟨m, hm⟩ := hl.out.dvd_choose_self (k := 2) two_ne_zero h3
    refine norm_pow_sub_one_of j hj.1 u hu l 1 1 hn ?_ (by omega) (by omega)
    rw [hm, Nat.cast_mul, norm_mul, hn]
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simpa using hu`. Consider the case `succ a ih`. Establish `h : Lev l (j + a)` using `⟨by have := hj.1; omega, fun h => by have := hj.2 h; omega⟩`. Rewrite using `[pow_succ, pow_mul]`.

Conclude with `norm_pow_prime (j + a) h _ ih`.
-/
theorem norm_pow_prime_pow (a : ℕ) (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ (l ^ a) - 1‖ = (l : ℝ) ^ (-((j + a : ℕ) : ℤ)) := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
    have h : Lev l (j + a) := ⟨by have := hj.1; omega, fun h => by have := hj.2 h; omega⟩
    rw [pow_succ, pow_mul]
    exact norm_pow_prime (j + a) h _ ih

/- English proof (translation)
Take `⟨a, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hm`. Rewrite using `[padicValNat.mul (pow_ne_zero _ hl.out.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, pow_mul, norm_pow_coprime (j + a) (by have := hj.1; omega) _ (norm_pow_prime_pow a j hj u hu) m hm]`. Use `push_cast`. Simplify using the standard rewrite rules.
-/
theorem norm_pow_nat (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (n : ℕ) (hn : n ≠ 0) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValNat l n : ℤ))) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [padicValNat.mul (pow_ne_zero _ hl.out.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, pow_mul,
    norm_pow_coprime (j + a) (by have := hj.1; omega) _ (norm_pow_prime_pow a j hj u hu) m hm]
  push_cast
  simp

/- English proof (translation)
Introduce `l _ j hj u hu k hk`. Establish `hu1 : ‖u‖ = 1`. Establish `h : ‖u - 1‖ < ‖(1 : ℚ_[l])‖`. Rewrite using `[hu, norm_one]`. Conclude with `zpow_lt_one_of_neg₀ one_lt_l (by have := hj.1; omega)`.

Use `norm_add_of_lt h` as an intermediate fact. Simplify using `using this`. Establish `hu0 : u ≠ 0` using `by rintro rfl; simp at hu1`. Establish `key` using `norm_pow_nat j hj u hu k.natAbs (Int.natAbs_ne_zero.2 hk)`. Unfold `padicValInt`.

Rewrite using `[← key]`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg k`. Simplify using the standard rewrite rules. Rewrite using `[Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]`. Establish `: (u ^ n)⁻¹ - 1 = -((u ^ n - 1) * (u ^ n)⁻¹)` using `by field_simp; ring`.

Rewrite using `[this, norm_neg, norm_mul, norm_inv, norm_pow, hu1]`. Simplify using the standard rewrite rules.
-/
theorem norm_zpow_sub_one : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l],
    ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 →
      ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  intro l _ j hj u hu k hk
  have hu1 : ‖u‖ = 1 := by
    have h : ‖u - 1‖ < ‖(1 : ℚ_[l])‖ := by
      rw [hu, norm_one]
      exact zpow_lt_one_of_neg₀ one_lt_l (by have := hj.1; omega)
    have := norm_add_of_lt h
    simpa using this
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have key := norm_pow_nat j hj u hu k.natAbs (Int.natAbs_ne_zero.2 hk)
  unfold padicValInt
  rw [← key]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have : (u ^ n)⁻¹ - 1 = -((u ^ n - 1) * (u ^ n)⁻¹) := by field_simp; ring
    rw [this, norm_neg, norm_mul, norm_inv, norm_pow, hu1]; simp

end GlobalTheory.Cyc.LiftExp
