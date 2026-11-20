import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

/- English proof (translation)
Introduce `r a hN`. Establish `hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ)` using `by exact_mod_cast hN`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [restX]`. Use `push_cast`.

Move the coercions through the operations in `at hN'`. Use polynomial arithmetic with `[sq_nonneg ((r : ℝ) - a)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem XBound.intersectionNumber_baseChange : XBound.Statement := by
  intro r a hN
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · simp only [restX]
    push_cast
    push_cast at hN'
    nlinarith [sq_nonneg ((r : ℝ) - a)]
  · nlinarith

/- English proof (translation)
Introduce `f r a B₀ p hf hN hB hp`. Establish `hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ)` using `by exact_mod_cast hN`. Establish `hf' : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hX` using `(XBound.intersectionNumber_baseChange r a hN)`. Establish `hX2 : (restX r a : ℝ) ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2` using `hX.1.trans hX.2`.

Establish `hN2 : 0 < ((r + a : ℕ) : ℝ) ^ 2` using `by positivity`. Establish `hp4 : 4 * ((r + a : ℕ) : ℝ) ^ 2 < p` using `by nlinarith`. Establish `hp0 : 0 < p` using `lt_trans (by positivity) hp4`. Rewrite using `[div_le_iff₀ hp0]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem XOverPrime.intersectionNumber_baseChange : XOverPrime.Statement := by
  intro f r a B₀ p hf hN hB hp
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hX := (XBound.intersectionNumber_baseChange r a hN)
  have hX2 : (restX r a : ℝ) ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := hX.1.trans hX.2
  have hN2 : 0 < ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hp4 : 4 * ((r + a : ℕ) : ℝ) ^ 2 < p := by nlinarith
  have hp0 : 0 < p := lt_trans (by positivity) hp4
  rw [div_le_iff₀ hp0]
  nlinarith

/- English proof (translation)
Use `Real.log_two_lt_d9` as an intermediate fact. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_log_four_le : 2 * Real.log 4 ≤ 2.78 := by
  have := Real.log_two_lt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  nlinarith

/- English proof (translation)
Use `⟨two_log_four_le, ?_⟩` and prove the remaining obligations. Introduce `f N hf hN`. Establish `hf' : (0 : ℝ) < f` using `by exact_mod_cast hf`. Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)`. Establish `: (1.5 : ℝ) * f * (3 / 2 * (N : ℝ) ^ 2) * (2.78 / (4 * f * (N : ℝ) ^ 2)) = 1.5 * (3 / 2) * 2.78 / 4`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Evaluate the numerical expressions.
-/
theorem RestConstants.intersectionNumber_baseChange : RestConstants.Statement := by
  refine ⟨two_log_four_le, ?_⟩
  intro f N hf hN
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have : (1.5 : ℝ) * f * (3 / 2 * (N : ℝ) ^ 2) * (2.78 / (4 * f * (N : ℝ) ^ 2)) =
      1.5 * (3 / 2) * 2.78 / 4 := by
    field_simp
  rw [this]
  norm_num

/- English proof (translation)
Introduce `k m j' N hm hk hj hN`. Establish `h3 : 8 ≤ m ^ 3`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 8 * m ≤ m ^ 4`. Combine the equalities or inequalities in the displayed calculation.

Establish `hk' : 2 * m + 2 ≤ k` using `by omega`. Conclude with `⟨hk', by omega⟩`.
-/
theorem SmallRankBound.intersectionNumber_baseChange : SmallRankBound.Statement := by
  intro k m j' N hm hk hj hN
  have h3 : 8 ≤ m ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ m ^ 3 := Nat.pow_le_pow_left hm 3
  have h4 : 8 * m ≤ m ^ 4 := by
    calc 8 * m ≤ m ^ 3 * m := Nat.mul_le_mul_right m h3
      _ = m ^ 4 := by ring
  have hk' : 2 * m + 2 ≤ k := by omega
  exact ⟨hk', by omega⟩

/- English proof (translation)
Introduce `h`. Use `h 5 2 2 6 le_rfl (by norm_num) le_rfl (by norm_num)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem SmallRankWeakHypothesis.intersectionNumber_baseChange : SmallRankWeakHypothesis.Statement := by
  intro h
  have := h 5 2 2 6 le_rfl (by norm_num) le_rfl (by norm_num)
  omega

/- English proof (translation)
Introduce `p k hp hk`. Use `set x : ℝ := (p ^ k)⁻¹ with hx`. Establish `hpk : (2 : ℝ) ≤ p ^ k`. Combine the equalities or inequalities in the displayed calculation. Establish `hx0 : 0 ≤ x` using `by positivity`.

Establish `hx2 : x ≤ 1 / 2`. Rewrite using `[hx]`. Rewrite using `[inv_le_comm₀ (by positivity) (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ n : ℕ, (p ^ ((n + 1) * k))⁻¹ = x * x ^ n`.

Introduce `n`. Rewrite using `[hx, ← pow_succ', inv_pow, ← pow_mul, mul_comm k]`. Establish `hs : Summable (fun n : ℕ => x ^ n)` using `summable_geometric_of_lt_one hx0 (by linarith)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hterm]`.

Conclude with `hs.mul_left x`. Repeatedly rewrite using `[hterm]`. Rewrite using `[tsum_mul_left, tsum_geometric_of_lt_one hx0 (by linarith)]`. Establish `h1 : (1 - x)⁻¹ ≤ 2`. Rewrite using `[inv_le_comm₀ (by linarith) (by norm_num)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GeometricTail.intersectionNumber_baseChange : GeometricTail.Statement := by
  intro p k hp hk
  set x : ℝ := (p ^ k)⁻¹ with hx
  have hpk : (2 : ℝ) ≤ p ^ k := by
    calc (2 : ℝ) ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := pow_le_pow_right₀ (by linarith) hk
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hterm : ∀ n : ℕ, (p ^ ((n + 1) * k))⁻¹ = x * x ^ n := by
    intro n
    rw [hx, ← pow_succ', inv_pow, ← pow_mul, mul_comm k]
  have hs : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_lt_one hx0 (by linarith)
  refine ⟨?_, ?_⟩
  · simp_rw [hterm]
    exact hs.mul_left x
  · simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 (by linarith)]
    have h1 : (1 - x)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc x * (1 - x)⁻¹ ≤ x * 2 := mul_le_mul_of_nonneg_left h1 hx0
      _ = 2 * x := by ring

/- English proof (translation)
Establish `he` using `Real.exp_one_lt_d9`. Establish `h8 : Real.exp (3 / 8) ^ 8 = Real.exp 1 ^ 3`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_nat_mul]`. Evaluate the numerical expressions. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Establish `h1 : (1.5 : ℝ) ^ 8 < Real.exp (3 / 8) ^ 8` using `pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)`. Establish `h2 : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3` using `pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)`. Rewrite `h1` using `[h8]`. Evaluate the numerical expressions using `at h1 h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_three_eighths_le : Real.exp (3 / 8) ≤ 1.5 := by
  have he := Real.exp_one_lt_d9
  have h8 : Real.exp (3 / 8) ^ 8 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  by_contra hlt
  push Not at hlt
  have h1 : (1.5 : ℝ) ^ 8 < Real.exp (3 / 8) ^ 8 :=
    pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  have h2 : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  rw [h8] at h1
  norm_num at h1 h2
  linarith

/- English proof (translation)
Introduce `p X hp hX hXp`. Use `set u : ℝ := X / p with hu`. Establish `hu0 : 0 ≤ u` using `by positivity`. Establish `hu38 : u ≤ 3 / 8` using `by rw [hu, div_le_iff₀ hp]; linarith`. Establish `hA : 0 ≤ X / p ^ 2` using `by positivity`.

Establish `hterm : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) = X / p ^ 2 * (u ^ k * (2 / ((k + 2).factorial : ℝ)))`. Introduce `k`. Rewrite using `[hu, div_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hfac : ∀ k : ℕ, 2 / ((k + 2).factorial : ℝ) ≤ 1 / (k.factorial : ℝ)`. Introduce `k`. Establish `h1 : (2 : ℝ) * k.factorial ≤ (k + 2).factorial`. Establish `: 2 * k.factorial ≤ (k + 2).factorial`. Rewrite using `[Nat.factorial_succ, Nat.factorial_succ]`.

Conclude with `Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))`. Conclude with `this` after adjusting the coercions. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbound : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) ≤ X / p ^ 2 * (u ^ k / (k.factorial : ℝ))`.

Introduce `k`. Rewrite using `[hterm]`. Apply `mul_le_mul_of_nonneg_left _ hA` to reduce the goal to its premises. Rewrite using `[div_eq_mul_one_div (u ^ k)]`. Conclude with `mul_le_mul_of_nonneg_left (hfac k) (by positivity)`.

Establish `hnn : ∀ k : ℕ, 0 ≤ 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)`. Introduce `k`. Check the signs of the components of the expression. Establish `hexp : Summable (fun k : ℕ => u ^ k / (k.factorial : ℝ))` using `Real.summable_pow_div_factorial u`. Establish `hsum : Summable (fun k : ℕ => X / p ^ 2 * (u ^ k / (k.factorial : ℝ)))` using `hexp.mul_left _`.

Establish `hS : Summable (fun k : ℕ => 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ))` using `Summable.of_nonneg_of_le hnn hbound hsum`. Use `⟨hS, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]`. Use `_ ≤ X / p ^ 2 * Real.exp (3 / 8) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu38) hA`.

Use `_ = Real.exp (3 / 8) * X / p ^ 2 := by ring`. Use `exp_three_eighths_le` as an intermediate fact. Rewrite using `[mul_div_assoc, mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_right this hA`.
-/
theorem ExponentialTail.intersectionNumber_baseChange : ExponentialTail.Statement := by
  intro p X hp hX hXp
  set u : ℝ := X / p with hu
  have hu0 : 0 ≤ u := by positivity
  have hu38 : u ≤ 3 / 8 := by rw [hu, div_le_iff₀ hp]; linarith
  have hA : 0 ≤ X / p ^ 2 := by positivity
  have hterm : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) =
      X / p ^ 2 * (u ^ k * (2 / ((k + 2).factorial : ℝ))) := by
    intro k
    rw [hu, div_pow]
    field_simp
    ring
  have hfac : ∀ k : ℕ, 2 / ((k + 2).factorial : ℝ) ≤ 1 / (k.factorial : ℝ) := by
    intro k
    have h1 : (2 : ℝ) * k.factorial ≤ (k + 2).factorial := by
      have : 2 * k.factorial ≤ (k + 2).factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hbound : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) ≤
      X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [hterm]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [div_eq_mul_one_div (u ^ k)]
    exact mul_le_mul_of_nonneg_left (hfac k) (by positivity)
  have hnn : ∀ k : ℕ, 0 ≤ 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) := by
    intro k; positivity
  have hexp : Summable (fun k : ℕ => u ^ k / (k.factorial : ℝ)) := Real.summable_pow_div_factorial u
  have hsum : Summable (fun k : ℕ => X / p ^ 2 * (u ^ k / (k.factorial : ℝ))) := hexp.mul_left _
  have hS : Summable (fun k : ℕ => 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)) :=
    Summable.of_nonneg_of_le hnn hbound hsum
  refine ⟨hS, ?_, ?_⟩
  · calc ∑' k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)
        ≤ ∑' k : ℕ, X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := hS.tsum_le_tsum hbound hsum
      _ = X / p ^ 2 * Real.exp u := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      _ ≤ X / p ^ 2 * Real.exp (3 / 8) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu38) hA
      _ = Real.exp (3 / 8) * X / p ^ 2 := by ring
  · have := exp_three_eighths_le
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right this hA

/- English proof (translation)
Introduce `x hx`. Use `set n := ⌊x⌋₊`. Establish `hprod : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p = Real.log (primorial n)`. Rewrite using `[primorial, Nat.cast_prod, Real.log_prod]`. Introduce `p hp`.

Use `(Finset.mem_filter.mp hp).2.pos` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions. Rewrite using `[hprod]`. Establish `hpos : (0 : ℝ) < primorial n` using `by exact_mod_cast primorial_pos n`. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.log_le_log hpos` to reduce the goal to its premises. Conclude with `primorial_le_four_pow n` after adjusting the coercions. Use `_ = n * Real.log 4 := by rw [Real.log_pow]`. Use `_ ≤ x * Real.log 4 := by`. Apply `mul_le_mul_of_nonneg_right (Nat.floor_le hx)` to reduce the goal to its premises.

Conclude with `Real.log_nonneg (by norm_num)`.
-/
theorem ChebyshevThetaBound.intersectionNumber_baseChange : ChebyshevThetaBound.Statement := by
  intro x hx
  set n := ⌊x⌋₊
  have hprod : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p =
      Real.log (primorial n) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    exact_mod_cast this.ne'
  rw [hprod]
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  calc Real.log (primorial n) ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log hpos
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]
    _ ≤ x * Real.log 4 := by
        apply mul_le_mul_of_nonneg_right (Nat.floor_le hx)
        exact Real.log_nonneg (by norm_num)

end

end RestTerms

end GroundTheory.Heights₂.Heights
