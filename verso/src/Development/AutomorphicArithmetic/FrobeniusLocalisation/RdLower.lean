import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Establish `he' : (2 : ℝ) ≤ (e : ℝ)` using `by exact_mod_cast he`. Establish `h1 : (2 : ℝ) ^ (-(e : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ))` using `Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)`. Establish `h2 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4`. Rewrite using `[Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num`. Rewrite `h1` using `[h2]`.

Establish `h3 : (2 : ℝ) ^ ((11 : ℝ) / 4) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ)))` using `Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [he', h1])`. Use `lt_of_lt_of_le ?_ h3` and prove the remaining obligations. Establish `h4 : ((2 : ℝ) ^ ((11 : ℝ) / 4)) ^ (4 : ℕ) = 2 ^ (11 : ℕ)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]`. Evaluate the numerical expressions.

Use `lt_of_pow_lt_pow_left₀ 4 (by positivity) ?_` and prove the remaining obligations. Rewrite using `[h4]`. Evaluate the numerical expressions.
-/
private theorem rd_lower_num (e : ℕ) (he : 2 ≤ e) :
    (6.7 : ℝ) < (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) := by
  have he' : (2 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have h1 : (2 : ℝ) ^ (-(e : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ ((11 : ℝ) / 4) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [he', h1])
  refine lt_of_lt_of_le ?_ h3
  have h4 : ((2 : ℝ) ^ ((11 : ℝ) / 4)) ^ (4 : ℕ) = 2 ^ (11 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    norm_num
  refine lt_of_pow_lt_pow_left₀ 4 (by positivity) ?_
  rw [h4]; norm_num

/- English proof (translation)
Introduce `φ H`. Establish `h1` using `rd_lower_num φ.e H.two_le_e`. Establish `h2` using `H.der.rd_ge`. Establish `hd : 7 ≤ H.d` using `by have := H.d_mod_sixteen; omega`. Establish `hd' : (7 : ℝ) ≤ (H.d : ℝ)` using `by exact_mod_cast hd`.

Establish `hs : (2.6 : ℝ) ≤ Real.sqrt H.d` using `Real.le_sqrt_of_sq_le (by linarith)`. Establish `hs0 : (0 : ℝ) < Real.sqrt H.d` using `by linarith`. Use `⟨h1, (le_div_iff₀ hs0).2 h2, ?_, Nat.mul_le_mul_left 2 φ.two_pow_le_ord, ?_⟩` and prove the remaining obligations. Establish `h3 : (6.7 : ℝ) * 2.6 ≤ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d` using `mul_le_mul h1.le hs (by norm_num) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[mul_assoc]`. Conclude with `Nat.mul_le_mul_left 2 φ.ord_le_o_mul_two_pow`.
-/
theorem UpperTheory.HF.rd_lower :
    ∀ {φ : Frame} (H : HostAx φ), (6.7 : ℝ) < (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ∧ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ≤ H.rd / Real.sqrt H.d ∧ 8 < H.rd / 2 ∧ 2 * 2 ^ φ.e ≤ 2 * φ.ord ∧ 2 * φ.ord ≤ 2 * φ.o * 2 ^ φ.e := by
  intro φ H
  have h1 := rd_lower_num φ.e H.two_le_e
  have h2 := H.der.rd_ge
  have hd : 7 ≤ H.d := by have := H.d_mod_sixteen; omega
  have hd' : (7 : ℝ) ≤ (H.d : ℝ) := by exact_mod_cast hd
  have hs : (2.6 : ℝ) ≤ Real.sqrt H.d := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < Real.sqrt H.d := by linarith
  refine ⟨h1, (le_div_iff₀ hs0).2 h2, ?_, Nat.mul_le_mul_left 2 φ.two_pow_le_ord, ?_⟩
  · have h3 : (6.7 : ℝ) * 2.6 ≤ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d :=
      mul_le_mul h1.le hs (by norm_num) (by positivity)
    linarith
  · rw [mul_assoc]
    exact Nat.mul_le_mul_left 2 φ.ord_le_o_mul_two_pow
