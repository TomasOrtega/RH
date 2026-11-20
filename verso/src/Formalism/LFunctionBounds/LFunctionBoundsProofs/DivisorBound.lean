import Formalism.LFunctionBounds.PositivityBound

namespace Formalism.FX

open Finset

/- English proof (translation)
Establish `hM1 : (1 : ℝ) ≤ max 1 (1 / a)` using `le_max_left _ _`. Establish `hMa : 1 ≤ max 1 (1 / a) * a`. Combine the equalities or inequalities in the displayed calculation. Establish `hk : (0 : ℝ) ≤ k` using `k.cast_nonneg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem succ_le_max_mul_exp (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) ≤ max 1 (1 / a) * Real.exp (a * k) := by
  have hM1 : (1 : ℝ) ≤ max 1 (1 / a) := le_max_left _ _
  have hMa : 1 ≤ max 1 (1 / a) * a := by
    calc (1 : ℝ) = (1 / a) * a := by field_simp
      _ ≤ max 1 (1 / a) * a := mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc ((k : ℝ) + 1) ≤ max 1 (1 / a) * (1 + a * k) := by nlinarith
    _ ≤ max 1 (1 / a) * Real.exp (a * k) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (a * k)]) (by linarith)

/- English proof (translation)
Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (show 0 < p by omega)`. Establish `hlog : Real.log 2 ≤ Real.log p` using `Real.log_le_log (by norm_num) (by exact_mod_cast hp)`. Establish `ha : 0 < e * Real.log 2` using `mul_pos he (Real.log_pos (by norm_num))`. Use `(succ_le_max_mul_exp _ ha k).trans ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (le_max_left _ _))` and prove the remaining obligations.

Rewrite using `[Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hk : (0 : ℝ) ≤ k` using `k.cast_nonneg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem succ_le_max_mul_pow (e : ℝ) (he : 0 < e) (p k : ℕ) (hp : 2 ≤ p) :
    ((k : ℝ) + 1) ≤ max 1 (1 / (e * Real.log 2)) * ((p : ℝ) ^ e) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have ha : 0 < e * Real.log 2 := mul_pos he (Real.log_pos (by norm_num))
  refine (succ_le_max_mul_exp _ ha k).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (le_max_left _ _))
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc e * Real.log 2 * k ≤ e * Real.log p * k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog he.le) hk
    _ = k * (Real.log p * e) := by ring

/- English proof (translation)
Establish `hx : (0 : ℝ) ≤ (p : ℝ) ^ e` using `by positivity`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`.

Establish `h1 : ((k : ℝ) + 1) * 2 ≤ ((p : ℝ) ^ e) ^ k * (p : ℝ) ^ e` using `mul_le_mul ih hp (by norm_num) (by positivity)`. Establish `hk : (0 : ℝ) ≤ k` using `k.cast_nonneg`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem succ_le_pow_of_two_le (e : ℝ) (p k : ℕ) (hp : 2 ≤ (p : ℝ) ^ e) :
    ((k : ℝ) + 1) ≤ ((p : ℝ) ^ e) ^ k := by
  have hx : (0 : ℝ) ≤ (p : ℝ) ^ e := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h1 : ((k : ℝ) + 1) * 2 ≤ ((p : ℝ) ^ e) ^ k * (p : ℝ) ^ e :=
      mul_le_mul ih hp (by norm_num) (by positivity)
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    push_cast
    linarith

/- English proof (translation)
Use `conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]`. Rewrite using `[Finsupp.prod, Nat.support_factorization]`. Use `push_cast`. Rewrite using `[← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations.

Establish `hx : (0 : ℝ) ≤ p` using `p.cast_nonneg`. Rewrite using `[← Real.rpow_natCast (p : ℝ) (n.factorization p), ← Real.rpow_mul hx, mul_comm ((n.factorization p : ℕ) : ℝ) e, Real.rpow_mul hx, Real.rpow_natCast]`.
-/
theorem rpow_eq_prod_primeFactors (e : ℝ) {n : ℕ} (hn0 : n ≠ 0) :
    (n : ℝ) ^ e = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
  rw [Finsupp.prod, Nat.support_factorization]
  push_cast
  rw [← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hx : (0 : ℝ) ≤ p := p.cast_nonneg
  rw [← Real.rpow_natCast (p : ℝ) (n.factorization p), ← Real.rpow_mul hx,
    mul_comm ((n.factorization p : ℕ) : ℝ) e, Real.rpow_mul hx, Real.rpow_natCast]

/- English proof (translation)
Introduce `e he`. Use `set M := max 1 (1 / (e * Real.log 2)) with hM`. Use `set K := ⌈(2 : ℝ) ^ (1 / e)⌉₊ with hK`. Use `⟨M ^ K, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hn0 : n ≠ 0` using `by omega`.

Establish `hM1 : (1 : ℝ) ≤ M` using `le_max_left _ _`. Establish `hcard : ((n.divisors.card : ℕ) : ℝ) = ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1)`. Rewrite using `[Nat.card_divisors hn0]`. Use `norm_cast`. Rewrite using `[hcard, rpow_eq_prod_primeFactors e hn0]`.

Establish `hfac : ∀ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) ≤ (if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p)`. Introduce `p hp`. Establish `hp2 : 2 ≤ p` using `(Nat.prime_of_mem_primeFactors hp).two_le`. Use `split_ifs with hpK`. Conclude with `succ_le_max_mul_pow e he p _ hp2`.

Rewrite using `[one_mul]`. Apply `succ_le_pow_of_two_le` to reduce the goal to its premises. Establish `h1 : (2 : ℝ) ^ (1 / e) ≤ p` using `(Nat.le_ceil _).trans (by exact_mod_cast (not_lt.mp hpK))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]`.

Use `_ ≤ (p : ℝ) ^ e := Real.rpow_le_rpow (by positivity) h1 he.le`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun p _ => by positivity)` and prove the remaining obligations. Rewrite using `[Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]`. Apply `pow_le_pow_right₀ hM1` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem divisor_weight_bound : DivisorBound := by
  intro e he
  set M := max 1 (1 / (e * Real.log 2)) with hM
  set K := ⌈(2 : ℝ) ^ (1 / e)⌉₊ with hK
  refine ⟨M ^ K, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hcard : ((n.divisors.card : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]
    norm_cast
  rw [hcard, rpow_eq_prod_primeFactors e hn0]
  have hfac : ∀ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) ≤
      (if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with hpK
    · exact succ_le_max_mul_pow e he p _ hp2
    · rw [one_mul]
      apply succ_le_pow_of_two_le
      have h1 : (2 : ℝ) ^ (1 / e) ≤ p :=
        (Nat.le_ceil _).trans (by exact_mod_cast (not_lt.mp hpK))
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / e)) ^ e := by
            rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ e := Real.rpow_le_rpow (by positivity) h1 he.le
  calc ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, ((if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p)) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, (if p < K then M else 1)) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := Finset.prod_mul_distrib
    _ ≤ M ^ K * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun p _ => by positivity)
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        apply pow_le_pow_right₀ hM1
        calc (n.primeFactors.filter (fun p => p < K)).card ≤ (Finset.range K).card :=
              Finset.card_le_card fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          _ = K := Finset.card_range K

end Formalism.FX
