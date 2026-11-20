import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

namespace GlobalTheory

namespace RadiiIdentities

/- English proof (translation)
Establish `: (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sub_one_pos {l : ℕ} (hl : 2 ≤ l) : (0 : ℝ) < (l : ℝ) - 1 := by
  have : (2 : ℝ) ≤ l := by exact_mod_cast hl
  linarith

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
theorem sq_sub_one_eq (l : ℕ) : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) := by
  ring

/- English proof (translation)
Introduce `l i hl hi`. Establish `h1 : (0 : ℝ) < (l : ℝ) - 1` using `sub_one_pos hl`. Establish `hsq : ((l : ℝ) ^ 2 - 1) ≠ 0`. Rewrite using `[sq_sub_one_eq]`. Establish `: (0 : ℝ) < (l : ℝ) + 1` using `by linarith`.

Check the signs of the components of the expression. Prove the components needed by the constructor for the conclusion. Simplify using `only [gam, rho]`. Clear the denominators using the available nonvanishing facts. Take `⟨k, rfl⟩` from `hi`.

Establish `hk : (2 * k + 1 - 1) / 2 = k` using `by omega`. Establish `hne : ((l : ℝ) ^ 2) ≠ 1`. Introduce `h`. Apply `hsq` to reduce the goal to its premises. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [expE, hk, Ereal, rho]`. Use `push_cast`. Rewrite using `[geom_sum_eq hne]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exponent_integral : Formalism.L2.FormalSeriesBounds.EInt := by
  intro l i hl hi
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have hsq : ((l : ℝ) ^ 2 - 1) ≠ 0 := by
    rw [sq_sub_one_eq]
    have : (0 : ℝ) < (l : ℝ) + 1 := by linarith
    positivity
  constructor
  · simp only [gam, rho]
    field_simp
  · obtain ⟨k, rfl⟩ := hi
    have hk : (2 * k + 1 - 1) / 2 = k := by omega
    have hne : ((l : ℝ) ^ 2) ≠ 1 := by
      intro h
      apply hsq
      rw [h]
      ring
    simp only [expE, hk, Ereal, rho]
    push_cast
    rw [geom_sum_eq hne]
    field_simp
    ring

/- English proof (translation)
Introduce `l i hl`. Establish `h1 : (0 : ℝ) < (l : ℝ) - 1` using `sub_one_pos hl`. Establish `h2 : (0 : ℝ) < (l : ℝ) + 1` using `by linarith`. Establish `hpow : ((l : ℝ) ^ i) ≠ 0` using `by positivity`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [r1, r2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Ereal, rho]`. Rewrite using `[sq_sub_one_eq]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem radii_sum : I1 := by
  intro l i hl
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have h2 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hpow : ((l : ℝ) ^ i) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [r1, r2]
    field_simp
    ring
  · simp only [Ereal, rho]
    rw [sq_sub_one_eq]
    field_simp
    ring

/- English proof (translation)
Introduce `l i hl hi`. Establish `h1 : (0 : ℝ) < (l : ℝ) - 1` using `sub_one_pos hl`. Establish `h2 : (0 : ℝ) < (l : ℝ) + 1` using `by linarith`. Establish `hsq : ((l : ℝ) ^ 2 - 1) = ((l : ℝ) - 1) * ((l : ℝ) + 1)` using `sq_sub_one_eq l`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`.

Establish `hli : (l : ℝ) ≤ (l : ℝ) ^ i`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Ereal, rho, gam]`. Rewrite using `[hsq]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [gam]`. Rewrite using `[hsq, sub_nonneg, mul_div_assoc', le_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem slope_identity : I2 := by
  intro l i hl hi
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have h2 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hsq : ((l : ℝ) ^ 2 - 1) = ((l : ℝ) - 1) * ((l : ℝ) + 1) := sq_sub_one_eq l
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
    calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi
  refine ⟨?_, ?_⟩
  · simp only [Ereal, rho, gam]
    rw [hsq]
    field_simp
    ring
  · simp only [gam]
    rw [hsq, sub_nonneg, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[AddValuation.map_one]`. Conclude with `le_min ih le_rfl`. Use `_ ≤ v ((k : C) + 1) := AddValuation.map_add v _ _`.
-/
theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    calc (0 : WithTop ℝ) ≤ min (v (k : C)) (v 1) := by
          rw [AddValuation.map_one]
          exact le_min ih le_rfl
      _ ≤ v ((k : C) + 1) := AddValuation.map_add v _ _

/- English proof (translation)
Break down `Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩` into its components or cases. Conclude with `val_natCast_nonneg v k` after adjusting the coercions. Use `push_cast`. Rewrite using `[AddValuation.map_neg]`. Conclude with `val_natCast_nonneg v k`.
-/
theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact_mod_cast val_natCast_nonneg v k
  · push_cast
    rw [AddValuation.map_neg]
    exact val_natCast_nonneg v k

/- English proof (translation)
Introduce `C _ v l hl hvl p hp hpl`. Use `le_antisymm ?_ (val_natCast_nonneg v p)` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hcop : Nat.Coprime l p` using `(Nat.coprime_primes hl hp).2 (Ne.symm hpl)`.

Establish `hbez : ((1 : ℤ) : C) = ((l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p : ℤ)`. Rewrite using `[← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]`. Simplify using the standard rewrite rules. Move the coercions through the operations in `at hbez`. Establish `hA : (0 : WithTop ℝ) < v ((l : C) * (Nat.gcdA l p : C))`.

Rewrite using `[AddValuation.map_mul, hvl]`. Conclude with `lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) (le_add_of_nonneg_right (val_intCast_nonneg v _))`. Establish `hB : (0 : WithTop ℝ) < v ((p : C) * (Nat.gcdB l p : C))`. Rewrite using `[AddValuation.map_mul]`. Conclude with `lt_of_lt_of_le hlt (le_add_of_nonneg_right (val_intCast_nonneg v _))`.

Establish `hsum` using `AddValuation.map_add v ((l : C) * (Nat.gcdA l p : C)) ((p : C) * (Nat.gcdB l p : C))`. Rewrite `hsum` using `[← hbez, AddValuation.map_one]`. Conclude with `absurd (lt_of_lt_of_le (lt_min hA hB) hsum) (lt_irrefl 0)`.
-/
theorem val_other_prime : ValOther := by
  intro C _ v l hl hvl p hp hpl
  refine le_antisymm ?_ (val_natCast_nonneg v p)
  by_contra hlt
  rw [not_le] at hlt
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 (Ne.symm hpl)
  have hbez : ((1 : ℤ) : C) = ((l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p : ℤ) := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    simp
  push_cast at hbez
  have hA : (0 : WithTop ℝ) < v ((l : C) * (Nat.gcdA l p : C)) := by
    rw [AddValuation.map_mul, hvl]
    exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1))
      (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have hB : (0 : WithTop ℝ) < v ((p : C) * (Nat.gcdB l p : C)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have hsum := AddValuation.map_add v ((l : C) * (Nat.gcdA l p : C)) ((p : C) * (Nat.gcdB l p : C))
  rw [← hbez, AddValuation.map_one] at hsum
  exact absurd (lt_of_lt_of_le (lt_min hA hB) hsum) (lt_irrefl 0)

/- English proof (translation)
Introduce `C _ v l i n0 h1`. Establish `e1 : rho l + 1 / (2 * (l : ℝ) ^ i) - 1 / (8 * (l : ℝ) ^ i) = rho l + ((l : ℝ) ^ i)⁻¹ / 2 - ((l : ℝ) ^ i)⁻¹ / 8` using `by ring`. Establish `e2 : rho l + 1 / 2 - 1 / (8 * (l : ℝ) ^ i) = rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8` using `by ring`. Simplify using `only [HM1, WeightCond, r1, r2, del, e1, e2]`.
-/
theorem weight_forms_agree : WeightConditionIff := by
  intro C _ v l i n0 h1
  have e1 : rho l + 1 / (2 * (l : ℝ) ^ i) - 1 / (8 * (l : ℝ) ^ i) =
      rho l + ((l : ℝ) ^ i)⁻¹ / 2 - ((l : ℝ) ^ i)⁻¹ / 8 := by ring
  have e2 : rho l + 1 / 2 - 1 / (8 * (l : ℝ) ^ i) = rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8 := by ring
  simp only [HM1, WeightCond, r1, r2, del, e1, e2]

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y s`. Establish `hf : (s.factorial : ℚ) ≠ 0` using `by exact_mod_cast s.factorial_ne_zero`. Establish `key : (s.factorial : ℤ) * Ring.choose y s = ∏ j ∈ Finset.range s, (y - (j : ℤ))`. Rewrite using `[← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]`.

Rewrite using `[eq_div_iff hf, mul_comm]`. Conclude with `key` after adjusting the coercions. Introduce `y s`. Rewrite using `[Ring.choose_succ_succ]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `y`. Simplify using the standard rewrite rules. Introduce `s`. Consider the cases of `s with`. Consider the case `zero => simp`.

Consider the case `succ k => simp [Ring.choose_zero_succ]`.
-/
theorem binomial_differences : F5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y s
    have hf : (s.factorial : ℚ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
    have key : (s.factorial : ℤ) * Ring.choose y s = ∏ j ∈ Finset.range s, (y - (j : ℤ)) := by
      rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
        Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
    rw [eq_div_iff hf, mul_comm]
    exact_mod_cast key
  · intro y s
    rw [Ring.choose_succ_succ]
    ring
  · intro y
    simp
  · intro s
    cases s with
    | zero => simp
    | succ k => simp [Ring.choose_zero_succ]

end RadiiIdentities

open RadiiIdentities in

/- English proof (translation)
Assemble the required witnesses or components as `⟨exponent_integral, radii_sum, slope_identity, val_other_prime, weight_forms_agree, binomial_differences⟩`.
-/
theorem radii_valuation_differences :
    Formalism.L2.FormalSeriesBounds.EInt ∧ I1 ∧ I2 ∧ ValOther ∧ WeightConditionIff ∧ F5 :=
  ⟨exponent_integral, radii_sum, slope_identity, val_other_prime, weight_forms_agree,
    binomial_differences⟩

end GlobalTheory
